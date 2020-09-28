### 3.0.0 (2020-09-28)

New major release introducing compatibility with newer versions of OCaml.
Here are the most important changes:
 - Remove quotations/antiquotations support.
 - Remove syntax extension support.
 - Do not expose the internals of the OCaml parser anymore.
 - Embed the OCaml AST, pprintast and friends (based on 4.10.0 for now).
 - Only the preprocessor remain.

### 2.0.0 (2018-11-10)

New major release, introducing incompatibilities due to wrapping of library
modules. Here are the most important changes:
 - Switch to `dune` (build system).
 - New (ocamlfind) packing: `earley.core`, `earley.str`, `earley.ocaml`.
 - Modules are wrapped in packages (`Earley` is now `Earley_core.Earley`).
 - `EarleyStr` is now `Earley_str`.

### 1.1.0 (2018-09-19)

Adds default blank function to the library. Small changes of semantics have
been observed in very complex cases (probably due to new optimization).

### 1.0.2 (2018-04-05)

Fix support for `ocaml 4.06.1`

### 1.0.1 (2018-02-13)

Several improvements, including optimizations.

### 1.0.0 (2017-08-24)

First release as `earley` (previously known as DeCaP).
