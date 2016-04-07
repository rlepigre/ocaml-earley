#!/bin/bash

export MAKE="make"

set -v

function build {
    opam switch $1
    eval `opam config env`
    export OCAMLVERSION=$1
    echo ==========================================================
    echo $PATH
    which ocamlopt.opt
    touch pa_ocaml.ml
    if [ $2 = "--cold" ]; then \
	 $MAKE distclean && $MAKE && $MAKE
    else
	cp pa_ocaml-$1 pa_ocaml && $MAKE clean && $MAKE
    fi &&\
    $MAKE ASCII=--ascii clean boot asttools &&\
    if [ -x ./pa_ocaml ]; then rm pa_ocaml; fi &&\
    $MAKE distclean &&\
    $MAKE && $MAKE
    echo ==========================================================
    # ./tests_pa_ocaml.sh
}

if [ $1 = "--cold" ]; then
    echo COLD: bootstraping from bootstraped file
elif [ $1 = "--hot" ]; then
    echo HOT: bootstraping from previous version
else
    echo you must tell --hot or --cold
    exit 1
fi

for v in 4.03.0+trunk 4.02.3 4.02.2 4.02.1 4.02.0 4.01.0; do
    build $v $1
    cp -f pa_ocaml pa_ocaml-$v
done

$MAKE distclean
