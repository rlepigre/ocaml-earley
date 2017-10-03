#!/bin/bash

echo Running earley install

git clone http://github.com/rlepigre/ocaml-earley.git && \
  cd ocaml-earley && make && make install && cd ..
