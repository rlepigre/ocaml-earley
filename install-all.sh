#!/bin/bash

VERSIONS="4.04.0 4.03.0 4.02.3 4.02.2 4.02.1 4.02.0 4.01.0"

function build {
    opam switch $1
    eval `opam config env`
    make clean
    make
    make install
}

for v in $VERSIONS; do
    build $v $1
done
