#!/usr/bin/env sh
cp ../../../bookstore.ml* ./
ocamlfind ocamlopt -linkpkg -package unix -package core_bench -thread -w -8 -package str -o bookstore_repl bookstore.mli bookstore.ml bookstore_repl.ml
# echo "benchmark 1000 10000 1000 1000 1000" | ./bookstore_repl
./bookstore_repl 100 1000 100 100 100 "$@"
