(lang dune 3.7)

(name carpenter)

(generate_opam_files true)

(source
 (github HadrienRenaud/carpenter))

(authors "Hadrien Renaud <hadrien.renaud.22@ucl.ac.uk")

(maintainers "Hadrien Renaud <hadrien.renaud.22@ucl.ac.uk")

(license LICENSE)

(documentation https://github.com/HadrienRenaud/carpenter)

(package
 (name carpenter)
 (synopsis "Test generator for ASL")
 (description "Generate tests for the Architecture Specification Language, and various tooling to use those tests")
 (depends ocaml dune herdtools7 feat fix)
 (depopts ocamlformat)
 (tags
  (tests asl afl)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
