#!/bin/bash

# compile many versions with opam. Usefull one changes some combinators and
# want to bootstrap earley-ocaml after that.

# List of versions on which to install.
VERSIONS="4.07.0 4.06.1 4.06.0 4.05.0 4.04.2 4.04.1 4.04.0 4.03.0"

# Save the current switch.
SAVE=$(opam config var switch)

# Perform the installations.
for V in $VERSIONS; do
  echo -e "\033[0;32mInstalling on OCaml $V...\033[0m"
  opam switch $V
  eval `opam config env`
  opam install ocamlfind ocamlbuild
  make distclean
  make
  make install
done

# Making sure the repository is clean.
make distclean

# Restoring original switch.
opam switch $SAVE
eval `opam config env`

echo -e "\033[0;32mBack to OCaml $SAVE...\033[0m"
