#!/usr/bin/env sh
ocamlopt -config
cp ../../../../Fiat4Mirage.ml ./
rm -f Fiat4Mirage.mli
ocamlfind ocamlopt -p -g -linkpkg -thread -package cstruct -package core -package core_bench Int64Word.ml ArrayVector.ml CstructBytestring.ml OCamlNativeInt.ml Fiat4Mirage.ml bench.ml -o fiat4mirage-bench || exit 1
./fiat4mirage-bench -width 2000 -quota 5 -ci-absolute +time
#short, tall, line, blank or column
