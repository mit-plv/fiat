#!/usr/bin/env sh
ocamlopt -config
rm Fiat4Mirage.mli
ocamlfind ocamlopt -linkpkg -thread -package core -package core_bench Int64Word.ml ArrayVector.ml OCamlNativeInt.ml Fiat4Mirage.ml bench.ml -o fiat4mirage-bench || exit 1
./fiat4mirage-bench
