#!/usr/bin/env sh
date
ocamlopt -config
./gen.py
cd ..
rm -f Fiat4Mirage.mli
ocamlfind ocamlopt -linkpkg -thread -package core -package core_bench Int64Word.ml ArrayVector.ml OCamlNativeInt.ml Fiat4Mirage.ml benchmarks/microbenchmarks.ml -o microbenchmarks || exit 1
./microbenchmarks -save -quota 60 -width 2000 -ci-absolute +time
