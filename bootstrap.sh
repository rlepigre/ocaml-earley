#!/bin/bash

export MAKE="make"

set -v

SAVE=`opam config var switch`
GOOD_BOOTSTRAPS=""
ALL_VERSIONS="4.05.0 4.04.2 4.04.1 4.04.0 4.03.0 4.02.3 4.02.2 4.02.1 4.02.0"

function build {
    opam switch $1
    eval `opam config env`
    export OCAMLVERSION=$1
    echo ==========================================================
    echo $PATH
    which ocamlopt.opt
    touch pa_ocaml.ml
    if [ "$2" = "--all" ] ; then \
	$MAKE distclean && $MAKE && $MAKE ; \
    else \
	if [ ! -x ./pa_ocaml ] ; then \
	    echo pa_ocaml must be compiled first; \
	    exit 1; \
	fi \
    fi &&\
    $MAKE boot asttools &&\
    if [ -x ./pa_ocaml ]; then rm pa_ocaml; fi &&\
    $MAKE distclean &&\
    $MAKE && $MAKE &&\
    GOOD_BOOTSTRAPS="$1 , $GOOD_BOOTSTRAPS"
    echo ==========================================================
    echo GOOD_BOOTSTRAPS: $GOOD_BOOTSTRAPS
    echo ==========================================================
    # ./tests_pa_ocaml.sh
}

if [ "$1" = "--all" -o "$1" = "--allnew" ] ; then
    VERSIONS=$ALL_VERSIONS
    echo ALL: bootstraping all version \($VERSIONS\) from file in bootstrap
elif [ "$1" = "--new" ] ; then
    echo NEW: bootstraping $2 from previous version
    VERSIONS=$2
elif [ "$1" = "--earley" ] ; then
    cd $2
    for v in $ALL_VERSIONS; do
	opam switch $v
	eval `opam config env`
	make clean && make && make install
    done
    exit 0
else
    echo you give option --new VERSION or --all or --allnew or --earley dir
    exit 1
fi

for v in $VERSIONS; do
    build $v $1
    cp -f pa_ocaml pa_ocaml-$v
done

$MAKE distclean

opam switch $SAVE
eval `opam config env`

echo GOOD_BOOTSTRAPS: $GOOD_BOOTSTRAPS
