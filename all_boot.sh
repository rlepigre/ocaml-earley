#!/bin/bash

make pa_ocaml

export MAKEOPTS="OCAMLFIND= OCAMLOPT=ocamlopt.opt OCAMLC=ocamlc.opt"
export MAKE="make $MAKEOPTS"

function build {
    opam switch $1
    eval `opam config env`
    export OCAMLVERSION=$1
    echo ==========================================================
    echo $PATH
    echo $MAKE clean boot
    which ocamlopt.opt
    echo ==========================================================
    $MAKE clean boot
    if [ -x ./pa_ocaml ]; then rm pa_ocaml; fi
    echo ==========================================================
    echo $MAKE pa_ocaml
    echo ==========================================================
    $MAKE pa_ocaml
    echo ==========================================================
    echo $MAKE
    echo ==========================================================
    $MAKE
    echo ==========================================================
    echo cd ast_tools
    echo $MAKE distclean all
    echo ==========================================================
    cd ast_tools
    $MAKE distclean all
    cd ..
    echo ==========================================================
    echo ./tests_pa_ocaml.sh
    echo ==========================================================
    #./tests_pa_ocaml.sh
}

for v in 4.03.0+trunk 4.02.3 4.02.2 4.02.1 4.02.0 4.01.0; do
    build $v
    cp -f pa_ocaml pa_ocaml-$v
done

$MAKE distclean
