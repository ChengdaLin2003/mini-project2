(lang dune 3.17)

(name interp2)

(generate_opam_files true)

(package
 (name interp2)
 (depends ocaml stdlib320 ounit2))

(using menhir 3.0)
