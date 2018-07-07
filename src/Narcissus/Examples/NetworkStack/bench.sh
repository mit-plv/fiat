#!/usr/bin/env sh
ocamlopt -config
ocamlfind ocamlopt -linkpkg -thread -package core -package core_bench ArrayVector.ml Fiat4Mirage.mli Fiat4Mirage.ml bench.ml -o fiat4mirage-bench || exit 1
./fiat4mirage-bench
