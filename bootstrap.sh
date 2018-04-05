#!/bin/bash

export MAKE="make"

#set -v

SAVE=`opam config var switch`
GOOD_BOOTSTRAPS=""
VERSIONS="4.07.0+trunk 4.06.1 4.06.0 4.05.0 4.04.2 4.04.1 4.04.0 4.03.0"

function build {
    opam switch $1
    eval `opam config env`
    opam install -y ocamlfind ocamlbuild
    # Check if earley is installed.
    ocamlfind query -qo -qe earley
    if [ $? -ne 0 ]; then
      cd ../earley
      make distclean
      make install
      make distclean
      cd -
    fi
    make boot || exit 1
    make distclean
}

function tests {
    opam switch $1
    eval `opam config env`
    make distclean
    make && make && make tests
    if ! $?; then exit 1; fi
    make distclean
}

function expected {
    opam switch $1
    eval `opam config env`
    make distclean
    make && make && make expected
    make distclean
}

if [ "$1" = "--all" -o "$1" = "--allnew" ] ; then
    echo ALL: bootstraping all version \($VERSIONS\) from file in bootstrap
    for v in $VERSIONS; do
	build $v
    done
elif [ "$1" = "--new" ] ; then
    echo NEW: bootstraping $2 from previous version
    make && make
elif [ "$1" = "--expected" ] ; then
    echo ALL: created expected tests results for \($VERSIONS\)
    for v in $VERSIONS; do
	expected $v
    done
elif [ "$1" = "--tests" ] ; then
    echo ALL: created expected tests results for \($VERSIONS\)
    for v in $VERSIONS; do
	tests $v
    done
else
    echo you give option --new VERSION, --all, --allnew, --expected or --tests
    exit 1
fi

$MAKE distclean

opam switch $SAVE
eval `opam config env`
