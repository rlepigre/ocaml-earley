#!/bin/bash

echo Running earley install

git clone http://github.com/rlepigre/ocaml-earley.git && \
  cd ocaml-earley && opam pin add . && cd ..
