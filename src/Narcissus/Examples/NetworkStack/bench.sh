#!/usr/bin/env sh
ocamlopt -config
rm -f Fiat4Mirage.mli
ocamlfind ocamlopt -linkpkg -thread -package core -package core_bench Int64Word.ml ArrayVector.ml OCamlNativeInt.ml Fiat4Mirage.ml bench.ml -o fiat4mirage-bench || exit 1
./fiat4mirage-bench -width 2000 -quota 1 -ci-absolute +time
#short, tall, line, blank or column
