#!/bin/bash
# Compile the extracted checker with an flambda compiler (separate switch bb6fl), using the kernel's own uint63.ml.
set -e
K=$(eval "$(opam env --switch=rocq 2>/dev/null)"; coqc -where)/../coq-core/kernel
eval "$(opam env --switch=bb6fl 2>/dev/null)"
cd extract; mkdir -p fl; cp checker.ml checker.mli main.ml fl/; cp "$K/uint63.ml" "$K/uint63.mli" fl/; cd fl
ocamlopt -O3 -unbox-closures -inline 400 -unsafe -w -a unix.cmxa ../stub.c uint63.mli uint63.ml checker.mli checker.ml main.ml -o check 2>&1 | tail -2
