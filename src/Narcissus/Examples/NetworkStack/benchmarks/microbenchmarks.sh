#!/usr/bin/env sh
date
ocamlopt -config
./gen.py
cd ..
cp ../../../../Fiat4Mirage* ./
rm -f Fiat4Mirage.mli
ocamlfind ocamlopt -linkpkg -thread -package cstruct -package core -package core_bench \
          -I ../../OCamlExtraction \
          ../../OCamlExtraction/Int64Word.ml \
          ../../OCamlExtraction/ArrayVector.ml \
          ../../OCamlExtraction/StackVector.ml \
          ../../OCamlExtraction/CstructBytestring.ml \
          ../../OCamlExtraction/OCamlNativeInt.ml \
          Fiat4Mirage.ml \
          benchmarks/microbenchmarks.ml \
          -o microbenchmarks || exit 1
./microbenchmarks -save -quota 60 -width 2000 -ci-absolute +time
mv ./*.txt benchmarks/outputs
