#!/bin/bash

# Checking command-line arguments.
if [[ "$#" -ne 1 || ("$1" != "--full" && "$1" != "--quick") ]]; then
  echo "Usage: $0 [--full | --quick]"
  exit -1
fi

# Preprocessing if pa_ocaml is installed.
if ! [ -x "$(command -v pa_ocaml)" ]; then
  echo "No preprocessor available, using generated files."
else
  echo -n "Preprocessing... "
  for SRC in `ls tests/need_pp`; do
    pa_ocaml --ascii tests/need_pp/$SRC > tests/$SRC
  done
  echo "Done."
fi

# Building binaries.
echo -n "Building...      "
ocamlbuild -use-ocamlfind -quiet tests/test.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/blank.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left2.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left3.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left5.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left6.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left7.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left8.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/calc_prio_left9.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix,str tests/gamma3.native
ocamlbuild -use-ocamlfind -quiet -pkgs unix     tests/calcyacc/calc.native
echo "Done."

# Running the tests.
echo "Testing...       "
echo "##########"
./test.native $1 > /dev/null
./blank.native $1 > /dev/null
./calc_prio_left.native $1 > /dev/null
./calc_prio_left2.native --quick > /dev/null #too slow!
./calc_prio_left3.native $1 > /dev/null
./calc_prio_left5.native $1 > /dev/null
./calc_prio_left6.native $1 > /dev/null
./calc_prio_left7.native $1 > /dev/null
./calc_prio_left8.native $1 > /dev/null
./calc_prio_left9.native $1 > /dev/null
./gamma3.native 30 > /dev/null
echo "##########"
echo "All good."
