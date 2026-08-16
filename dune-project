(lang dune 3.21)
(generate_opam_files)
(name earley)

(source
 (github rlepigre/ocaml-earley))
(authors
 "Christophe Raffalli <christophe@raffalli.eu>"
 "Rodolphe Lepigre <lepigre@mpi-sws.org>")
(maintainers
 "Rodolphe Lepigre <lepigre@mpi-sws.org>")
(license
 "CECILL-B")

(package
 (name earley)
 (synopsis "Parsing library based on Earley Algorithm")
 (description
  "Earley is a parser combinator library base on Earley's algorithm. It
is intended to be used in conjunction with an OCaml syntax extension
which allows the definition of parsers inside the language.
")
 (depends
  (ocaml (>= 4.14.0))))
