Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Set Implicit Arguments.

Definition bin := list bool.

Definition encode_decode_correct
           (data_t : Type)
           (encode : data_t -> bin)
           (decode : bin -> data_t) :=
  forall data, decode (encode data) = data.

Infix "<+>" := encode_decode_correct (at level 20, no associativity).

Definition encode_decode_correct_app
           (data_t : Type)
           (encode : data_t -> bin)
           (decode : bin -> data_t * bin) :=
  forall data ext, decode (encode data ++ ext) = (data, ext).

Infix "<++>" := encode_decode_correct_app (at level 20, no associativity).

Definition encode_decode_correct_app_curry
           (data_t prev_t proj_t : Type)
           (prev : data_t -> prev_t)
           (proj : data_t -> proj_t)
           (encode : proj_t -> bin)
           (decode : prev_t -> bin -> proj_t * bin) :=
  forall data ext, decode (prev data) (encode (proj data) ++ ext) = (proj data, ext).

(* Notation "[ data | encode proj <+++> decode prev ]"
  := (encode_decode_correct_app_curry (fun data => prev) (fun data => proj) encode decode)
       (at level 20, no associativity). *)

Definition decode_well_founded (A : Type) (decode : bin -> A * bin) :=
  forall bin, length (snd (decode bin)) <= pred (length bin).

Class decoder
      (A : Type)
      (encode : A -> bin) :=
  { decode : bin -> A;
    decode_correct : encode <+> decode }.

Class decoder_block
      (A : Type)
      (encode : A -> bin) :=
  { decode_block : bin -> A * bin;
    decode_block_app : encode <++> decode_block;
    decode_block_wellfounded  : decode_well_founded decode_block }.
