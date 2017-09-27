#!/bin/bash

export MAKE="make"

set -v

GOOD=""
VERSIONS="4.05.0 4.04.2 4.04.1 4.04.0 4.03.0 4.02.2 4.02.1 4.02.0"

function build {
    opam switch $1
    eval `opam config env`
    $MAKE distclean && $MAKE && $MAKE
    GOOD="$1 , $GOOD"
}

for v in $VERSIONS; do
    build $v
done

$MAKE distclean
