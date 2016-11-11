#!/bin/bash

export MAKE="make"

set -v

GOOD_BOOTSTRAPS=""

function build {
    opam switch $1
    eval `opam config env`
    export OCAMLVERSION=$1
    echo ==========================================================
    echo $PATH
    which ocamlopt.opt
    touch pa_ocaml.ml
    if [ "$2" = "--all" ] ; then \
	 $MAKE distclean && $MAKE && $MAKE
    else
	cp pa_ocaml-$1 pa_ocaml && $MAKE clean && $MAKE ASCII=--ascii
    fi &&\
    $MAKE clean boot asttools &&\
    if [ -x ./pa_ocaml ]; then rm pa_ocaml; fi &&\
    $MAKE distclean &&\
    $MAKE && $MAKE &&\
    GOOD_BOOTSTRAPS="$1 , $GOOD_BOOTSTRAPS"
    echo ==========================================================
    echo GOOD_BOOTSTRAPS: $GOOD_BOOTSTRAPS
    echo ==========================================================
    # ./tests_pa_ocaml.sh
}

if [ "$1" = "--all" ] ; then
    VERSIONS="4.04.0 4.03.0 4.02.3 4.02.2 4.02.1 4.02.0 4.01.0"
    echo ALL: bootstraping all version \($VERSIONS\) from file in bootstrap
elif [ "$1" = "--new" ] ; then
    echo NEW: bootstraping $2 from previous version
    VERSIONS=$2
else
    echo you give option --new VERSION or --all
    exit 1
fi


for v in $VERSIONS; do
    build $v $1
    cp -f pa_ocaml pa_ocaml-$v
done

$MAKE distclean

echo GOOD_BOOTSTRAPS: $GOOD_BOOTSTRAPS
