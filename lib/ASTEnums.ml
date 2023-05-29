open Asllib
open AST
open Feat
open Enum

let annot desc = ASTUtils.add_dummy_pos desc

(* Util not to forget to pay ==> make payment mandatory on recursion. *)
let fix f = Fix.Memoize.Int.fix (fun blah -> f (pay blah))
let enum_from_seq seq = seq |> Seq.map just |> Seq.fold_left ( ++ ) empty
let unops : unop enum = finite [ NEG (* BNOT; NOT *) ]

let binops : binop enum =
  finite
    [
      PLUS;
      (*
      AND;
      BAND;
      BEQ;
      BOR;
      DIV;
      EOR;
      EQ_OP;
      GT;
      GEQ;
      IMPL;
      LT;
      LEQ;
      MOD;
      MINUS;
      MUL;
      NEQ;
      OR;
      RDIV;
      SHL;
      SHR;
      *)
    ]

let ints : int enum = fun i -> IFSeq.up (~-i + 1) i
let uints : int enum = fun i -> IFSeq.up 0 i

let values : value enum =
  let v_ints = map (fun i -> V_Int i) ints in
  let v_bools = finite [ V_Bool true; V_Bool false ] in
  let v_reals = empty in
  let v_bvs =
    map
      (fun s -> V_BitVector (Bitvector.of_string ("'" ^ s ^ "'")))
      (fix (fun ss -> just "" ++ map (( ^ ) "0") ss ++ map (( ^ ) "1") ss))
  in
  let v_tuples = empty in
  let v_records = empty in
  let v_exceptions = empty in
  v_ints ++ v_bools ++ v_reals ++ v_bvs ++ v_tuples ++ v_records ++ v_exceptions

let _make_vari i = "x" ^ string_of_int i

let exprs (vars : string enum) : expr enum =
  fix (fun exprs ->
      let e_unops =
        let make_unop (op, expr) = E_Unop (op, expr) in
        unops ** exprs |> map make_unop
      in
      let e_binops =
        let make_binop (op, (e1, e2)) = E_Binop (op, e1, e2) in
        binops ** exprs ** exprs |> map make_binop
      in
      let e_literals =
        let make_value v = E_Literal v in
        values |> map make_value
      in
      let e_vars =
        let make_var s = E_Var s in
        vars |> map make_var
      in
      let e_conds =
        let make_cond (e1, (e2, e3)) = E_Cond (e1, e2, e3) in
        exprs ** exprs ** exprs |> map make_cond
      in
      e_unops ++ e_binops ++ e_literals ++ e_vars ++ e_conds |> map annot)

let lexprs (vars : string enum) : lexpr enum =
  (* No need for a fix point yet: no recursive lexprs *)
  let le_vars =
    let make_var s = LE_Var s in
    vars |> map make_var
  in
  let le_ignore = just LE_Ignore in
  le_vars ++ le_ignore |> map annot

let stmt_lists (stmts : stmt enum) : stmt enum =
  list stmts |> map ASTUtils.stmt_from_list

let _make_mains_of_stmts =
  let make_main body =
    let name = "main"
    and args = []
    and parameters = []
    and return_type = None in
    [ D_Func { body; name; args; parameters; return_type } ]
  in
  map make_main

module Normal = struct
  let vars : string enum = finite [ "x"; "y" ] ++ pay (map _make_vari uints)
  let exprs = exprs vars
  let lexprs = lexprs vars

  let stmts : stmt enum =
    fix (fun stmts ->
        let s_assigns =
          let make_assign (le, e) = S_Assign (le, e) in
          lexprs ** exprs |> map make_assign
        in
        let s_conds =
          let make_cond (e, (s1, s2)) = S_Cond (e, s1, s2) in
          exprs ** stmt_lists stmts ** stmt_lists stmts |> map make_cond
        in
        s_assigns ++ s_conds |> map annot)

  let mains : AST.t enum = _make_mains_of_stmts (stmt_lists stmts)
end

module NoUndef = struct
  module Var = struct
    type t = int

    let compare = Int.compare
    let to_string i = "x" ^ Int.to_string i
    let succ = Int.succ
  end

  module Env = Set.Make (Var)
  module MemoizedEnv = Fix.Memoize.ForOrderedType (Env)

  type env = Env.t

  let vars env = env |> Env.to_seq |> enum_from_seq
  let vars_string env = map Int.to_string (vars env)
  let exprs = MemoizedEnv.memoize (fun env -> exprs (vars_string env))
  let lexprs = MemoizedEnv.memoize (fun env -> lexprs (vars_string env))

  module EnvFixCmp = struct
    type t = Env.t * int

    let compare (s1, i1) (s2, i2) =
      if i1 != i2 then i2 - i1 else Env.compare s1 s2
  end

  module EnvFix = Fix.Memoize.ForOrderedType (EnvFixCmp)

  let fresh_var env = try Env.max_elt env |> Var.succ with Not_found -> 0

  let stmts : env -> stmt enum =
    EnvFix.curried EnvFix.fix (fun stmts env ->
        let s_assigns =
          let make_assign (le, e) = S_Assign (le, e) in
          lexprs env ** exprs env |> map make_assign
        in
        let s_conds =
          let make_cond (e, (s1, s2)) = S_Cond (e, s1, s2) in
          let stmts = stmts env |> pay |> stmt_lists in
          exprs env ** stmts ** stmts |> map make_cond
        in
        let s_then_with_new_var =
          let var = fresh_var env in
          let stmts = Env.add var env |> stmts |> stmt_lists in
          let make_assign e =
            S_Assign (LE_Var (Var.to_string var) |> annot, e) |> annot
          in
          let assigns = exprs env |> map make_assign |> pay in
          let make_then (s1, s2) = ASTUtils.s_then s1 s2 in
          assigns ** stmts |> map make_then
        in
        s_then_with_new_var ++ (s_assigns ++ s_conds |> map annot))

  let mains = _make_mains_of_stmts (stmts Env.empty ++ just (annot S_Pass))
end
