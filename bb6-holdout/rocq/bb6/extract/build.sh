#!/bin/bash
# Extract the checker and compile it with ocamlopt. Run from the lane root after `make`.
set -e
eval "$(opam env --switch=rocq 2>/dev/null)" || true
coqc -Q busycoq BusyCoq -Q theories BB6 -native-compiler ondemand extract/Extract.v
K=$(coqc -where)/../coq-core/kernel
cd extract
ocamlfind ocamlopt -O3 -unboxed-types 2>/dev/null || true
ocamlfind ocamlopt -thread -package unix,coq-core.kernel -linkpkg -inline 200 -unsafe -w -a checker.mli checker.ml main.ml -o check
