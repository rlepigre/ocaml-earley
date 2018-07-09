#!/bin/bash

# compile many versions with opam. Usefull one changes some combinators and
# want to bootstrap earley-ocaml after that.

VERSIONS="4.07.0+trunk 4.06.1 4.06.0 4.05.0 4.04.2 4.04.1 4.04.0 4.03.0"

for v in $VERSIONS; do
    opam switch $v
    eval `opam config env`
    make distclean && make && make install
done

make distclean
