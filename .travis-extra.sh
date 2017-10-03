#!/bin/bash

echo Running earley install

git clone http://github.com/rlepigre/ocaml-earley.git && \
  opam pin add earley ocaml-earley
