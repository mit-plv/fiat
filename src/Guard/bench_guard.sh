#!/usr/bin/env sh
# cp "./tcpfilter.${INDEX}.ml" ./tcpfilter.ml
# cp "./tcpfilter.${INDEX}.mli" ./tcpfilter.mli
# cp -u "../../tcpfilter.${INDEX}.ml" ./tcpfilter.ml
# cp -u "../../tcpfilter.${INDEX}.mli" ./tcpfilter.mli
cp "../../tcpfilter.ml" ./tcpfilter.ml
cp "../../tcpfilter.mli" ./tcpfilter.mli

# Adjust the mli file because OCaml extraction is confused
sed -i '470s/^ *val eq_dec.*$//' tcpfilter.mli
sed -i '410s/^ *val eqb.*$//' tcpfilter.mli
sed -i '456s/^ *val eq_dec.*$//' tcpfilter.mli
sed -i '396s/^ *val eqb.*$//' tcpfilter.mli
perl -0777 -i -pe 's/val eq_dec : OCamlNativeInt.t -> OCamlNativeInt.t -> bool//gs' tcpfilter.mli
perl -0777 -i -pe 's/val eqb : OCamlNativeInt.t -> OCamlNativeInt.t -> bool//gs' tcpfilter.mli
perl -0777 -i -pe 's/(let tCP_decoder_impl.*?=\n  if ).*?then/\1 true then/gs' tcpfilter.ml
perl -0777 -i -pe 's/if iPChecksum_Valid_dec.*?then/if true then/gs' tcpfilter.ml
# perl -0777 -i -pe 's/val eq_dec[^\n]*\n//gs' tcpfilter.mli
perl -0777 -i -pe 's/val (ipv4ToString|ipv4ToList|byteString2ListOfChar|monoid_dequeue_word|append_bit|onesComplement|checksum|add_bytes_into_checksum|add_w16_into_checksum|oneC_plus|byteString_QueueMonoidOpt|byteStringQueueMonoid|byteString_id|byteString_enqueue_ByteString|byteString_enqueue_char|byteString_enqueue_word|byteString_dequeue|charList_dequeue|word_dequeue|byteString_enqueue|byteString_enqueue_full_word|length_ByteString|byteString0|numBytes|front|padding|dequeue_opt).*?\n\n//gs' tcpfilter.mli
perl -0777 -i -pe 's/type[\n]+? (queueMonoidOpt|monoid) .*?\n\n//gs' tcpfilter.mli

ocamlfind ocamlopt -fPIC -linkpkg -thread -package unix -package cstruct -package core -package core_bench \
          -I ../Narcissus/OCamlExtraction/ \
          ../Narcissus/OCamlExtraction/Int64Word.ml \
          ../Narcissus/OCamlExtraction/ArrayVector.ml \
          ../Narcissus/OCamlExtraction/StackVector.ml \
          ../Narcissus/OCamlExtraction/CstructBytestring.ml \
          ../Narcissus/OCamlExtraction/OCamlNativeInt.ml \
          ListVector.ml tcpfilter.mli tcpfilter.ml guard.ml \
          -o guard || exit 1
./guard "$@"
