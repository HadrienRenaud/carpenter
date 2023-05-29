open Carpenter_lib
open Asllib

module Demo : sig
  val show : unit -> unit
end = struct
  open ASTEnums
  open Normal

  let sample = Feat.Enum.sample

  let pp_seq_with name same_line pp seq =
    let open_content_box f () =
      match same_line with
      | `SameLineAllowed -> Format.pp_open_hovbox f 0
      | `OnePerLine -> Format.pp_open_vbox f 0
    in
    let pp_content f seq =
      open_content_box f ();
      Format.pp_print_seq ~pp_sep:Format.pp_print_space pp f seq;
      Format.close_box ()
    in
    Format.printf
      "@[<v \
       0>================================================================================@,\
       Iter %s@,\
       --------------------------------------------------------------------------------@,\
       %a@,\
       @,\
       @]@."
      name pp_content seq

  let show () =
    sample 10 unops 0 1 Seq.empty
    |> pp_seq_with "unop" `SameLineAllowed (fun f unop ->
           Format.fprintf f "%s" (PP.unop_to_string unop));

    sample 10 binops 0 1 Seq.empty
    |> pp_seq_with "binop" `SameLineAllowed (fun f binop ->
           Format.fprintf f "%s" (PP.binop_to_string binop));

    sample 10 ints 0 3 Seq.empty
    |> pp_seq_with "ints" `SameLineAllowed Format.pp_print_int;

    sample 100 values 0 5 Seq.empty
    |> pp_seq_with "values" `SameLineAllowed PP.pp_value;

    sample 10 exprs 0 5 Seq.empty |> pp_seq_with "expr" `OnePerLine PP.pp_expr;

    sample 3 lexprs 0 3 Seq.empty |> pp_seq_with "lexpr" `OnePerLine PP.pp_lexpr;

    sample 4 mains 3 10 Seq.empty |> pp_seq_with "stmt" `OnePerLine PP.pp_t
end

module Filter = struct
  module Rule = Instrumentation.Rule
  module RSet = Instrumentation.Set

  type t = Any | Err | NoErr | NoErrWithRules of RSet.t

  let pp f =
    let open Format in
    function
    | Any -> ()
    | Err -> pp_print_string f "error"
    | NoErr -> pp_print_string f "no-error"
    | NoErrWithRules rules ->
        let pp_sep f () = fprintf f "|@," in
        fprintf f "@[<2>%a@]" (pp_print_seq ~pp_sep Rule.pp) (RSet.to_seq rules)

  let _to_string = function
    | Any -> ""
    | Err -> "error"
    | NoErr -> "no-error"
    | NoErrWithRules _ as ef -> Format.asprintf "%a" pp ef

  let as_without_err = function
    | (NoErr | NoErrWithRules _) as ef -> ef
    | Err -> raise (Invalid_argument "as_without_err")
    | Any -> NoErr

  let as_with_err = function
    | Err as ef -> ef
    | Any -> Err
    | NoErr | NoErrWithRules _ -> raise (Invalid_argument "as_with_err")

  let get_rules = function
    | NoErrWithRules rules -> rules
    | Any | NoErr -> RSet.empty
    | Err -> raise (Invalid_argument "get_rules")

  let parse_and_append filter_ref s =
    try
      filter_ref :=
        match String.lowercase_ascii s with
        | "no-error" | "noerror" -> as_without_err !filter_ref
        | "error" -> as_with_err !filter_ref
        | s' ->
            let one rules s2 = RSet.add (Rule.of_string s2) rules in
            NoErrWithRules
              (String.split_on_char ',' s'
              |> List.fold_left one (get_rules !filter_ref))
    with
    | Not_found ->
        raise (Arg.Bad (Printf.sprintf "Cannot parse argument '%s'." s))
    | Invalid_argument _ ->
        raise (Arg.Bad "Unsupported: With error AND using specific rule.")

  let filter_execution =
    let protect ~err run ast = try run ast with Error.ASLException _ -> err in
    function
    | Any -> Fun.const true
    | Err ->
        protect ~err:true (fun ast ->
            Native.interprete `TypeCheck ast;
            false)
    | NoErr ->
        protect ~err:false (fun ast ->
            Native.interprete `TypeCheck ast;
            true)
    | NoErrWithRules rules ->
        let run ast =
          let used_rules =
            Native.interprete_with_instrumentation `TypeCheck ast
          in
          List.exists (fun r -> RSet.mem r rules) used_rules
        in
        protect ~err:false run
end

module Executable : sig
  val main : unit -> unit
end = struct
  type args = {
    demo : bool;
    o : string option;
    n : int option;
    until : bool;
    depth : int;
    rand : bool;
    no_undef : bool;
    filters : Filter.t;
  }

  let parse_args () : args =
    let open Arg in
    let demo = ref false in
    let o = ref None in
    let depth = ref 10 in
    let until = ref false in
    let no_undef = ref false in
    let filters = ref Filter.Any in
    let n = ref None in
    let rand = ref false in

    let set_opt ref_opt v = ref_opt := Some v in
    let opt_string ref_opt = String (set_opt ref_opt) in
    let opt_int ref_opt = Int (set_opt ref_opt) in

    let speclist =
      [
        ("--demo", Set demo, " Print various enumerations on stdout.");
        ( "-o",
          opt_string o,
          "OUTPUT_DIR Set output directory: tests are written to \
           OUTPUT_DIR/N.asl. If not set, output to stdout." );
        ("-n", opt_int n, "N Produce at most N tests.");
        ( "--depth",
          Set_int depth,
          "DEPTH Depth of the generated ASTs. Default to 10." );
        ("--until", Set until, " Generate all ASTs with depth <= DEPTH.");
        ("--rand", Set rand, " Select randomly some tests. Needs N to be set.");
        ( "--no-undef",
          Set no_undef,
          " Try and avoid generating ASTs that would fail with an Undefined \
           Identifier error." );
        ( "--only",
          String (Filter.parse_and_append filters),
          "FILTER Only generate ASTs that pass this filter." );
      ]
      |> align
    in

    let usage_msg = "Builds (abstract syntax) trees for ASL." in

    let anon_fun s = raise (Bad s) in

    let () = parse speclist anon_fun usage_msg in

    {
      demo = !demo;
      o = !o;
      n = !n;
      until = !until;
      depth = !depth;
      rand = !rand;
      no_undef = !no_undef;
      filters = !filters;
    }

  let select start depth (enum : 'a Feat.Enum.enum) : 'a Seq.t =
    Seq.ints start
    |> Seq.take (depth - start + 1)
    |> Seq.fold_left (fun k i -> Feat.IFSeq.to_seq (enum i) k) Seq.empty

  let select_rand n start depth (enum : 'a Feat.Enum.enum) : 'a Seq.t =
    Seq.ints start
    |> Seq.take (depth - start + 1)
    |> Seq.fold_left (fun k i -> Feat.IFSeq.sample n (enum i) k) Seq.empty

  let with_names seq =
    let name i thing = (Printf.sprintf "%d.asl" i, thing) in
    Seq.mapi name seq

  let print_named (o : string option) ((name, ast) : string * AST.t) : unit =
    let formatter, close, finally =
      match o with
      | Some dirname ->
          let filename = Filename.concat dirname name in
          let chan = open_out filename in
          let formatter = Format.formatter_of_out_channel chan in
          let close () =
            Format.pp_print_newline formatter ();
            close_out chan
          in
          (formatter, close, fun () -> close_out_noerr chan)
      | None -> (Format.std_formatter, Format.print_newline, fun () -> ())
    in
    Fun.protect ~finally (fun () ->
        PP.pp_t formatter ast;
        close ())

  let _take = function None -> Fun.id | Some n -> Seq.take n

  let main () =
    let args = parse_args () in
    if args.demo then Demo.show ()
    else
      let start = if args.until then 0 else args.depth in
      let mains =
        if args.no_undef then ASTEnums.NoUndef.mains else ASTEnums.Normal.mains
      in
      let select =
        if args.rand && Option.is_some args.n then
          select_rand (Option.get args.n)
        else select
      in
      mains |> select start args.depth
      |> Seq.filter (Filter.filter_execution args.filters)
      |> _take args.n |> with_names
      |> Seq.iter (print_named args.o)
end

let () = Executable.main ()
