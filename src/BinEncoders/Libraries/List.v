Require Export Coq.Lists.List.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core.

Set Implicit Arguments.

Section List_encode_decode.

  Variable (A : Type)
           (encode_A : A * bin -> bin)
           (A_Decoder : decoder (fun _ => True) encode_A).

  Fixpoint List_encode (ls : list A) :=
    match ls with
    | nil => nil
    | x :: xs => encode_A (x, List_encode xs)
    end.

  Definition List_encode_pair (p : list A * bin) :=
    List_encode (fst p) ++ snd p.

  Fixpoint List_decode_pair (size : nat) (b : bin) :=
    match size with
    | O => (nil, b)
    | S size' => let (_data, _bin) := @decode _ _ _ _ A_Decoder b in
                 let (_rest, __bin) := List_decode_pair size' _bin in
                     (_data :: _rest, __bin)
    end.

  Definition List_decode (size : nat) (b : bin) :=
    fst (List_decode_pair size b).

  Lemma List_encode_decode_correct :
    forall size, encode_decode_correct
                   (fun data : list A => length data = size) List_encode (List_decode size).
  Proof.
  Admitted.

  Lemma List_encode_decode_correct_pair :
    forall size, encode_decode_correct
                   (fun data => length (fst data) = size) List_encode_pair (List_decode_pair size).
  Proof.
  Admitted.

End List_encode_decode.

Global Instance List_decoder
       (A : Type)
       (encode_A : A * bin -> bin)
       (A_Decoder : decoder (fun _ => True) encode_A)
       (size : nat)
  : decoder (fun data => length data = size) (List_encode encode_A) :=
  { decode := List_decode A_Decoder size;
    decode_correct := @List_encode_decode_correct _ encode_A A_Decoder size }.

Global Instance List_decoder_pair
       (A : Type)
       (encode_A : A * bin -> bin)
       (A_Decoder : decoder (fun _ => True) encode_A)
       (size : nat)
  : decoder (fun data => length (fst data) = size) (List_encode_pair encode_A) :=
  { decode := List_decode_pair A_Decoder size;
    decode_correct := @List_encode_decode_correct_pair _ encode_A A_Decoder size }.
