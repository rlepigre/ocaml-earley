#!/bin/bash

export MAKE="make"

set -v

SAVE=`opam config var switch`
GOOD_BOOTSTRAPS=""
ALL_VERSIONS="4.07.0+trunk 4.06.0+trunk 4.05.0 4.04.2 4.04.1 4.04.0 4.03.0"
   # 4.02.3 4.02.2 4.02.1 4.02.0

function build {
    opam switch $1
    eval `opam config env`
    make boot || exit 1
    # ./tests_pa_ocaml.sh
}

if [ "$1" = "--all" -o "$1" = "--allnew" ] ; then
    VERSIONS=$ALL_VERSIONS
    echo ALL: bootstraping all version \($VERSIONS\) from file in bootstrap
#elif [ "$1" = "--new" ] ; then
#    echo NEW: bootstraping $2 from previous version
#    VERSIONS=$2
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
