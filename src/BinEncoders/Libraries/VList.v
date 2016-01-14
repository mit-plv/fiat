Require Export Coq.Lists.List.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core.

Set Implicit Arguments.

Section VList_encode_decode.

  Variable (A : Type)
           (encode_A : A * bin -> bin)
           (A_Decoder : decoder (fun _ => True) encode_A).

  Fixpoint VList_encode (ls : list A) :=
    match ls with
    | nil => nil
    | x :: xs => encode_A (x, VList_encode xs)
    end.

  Definition VList_encode_pair (p : list A * bin) :=
    VList_encode (fst p) ++ snd p.

  Fixpoint VList_decode_pair (b : bin) : list A * bin := (nil, b).

  Definition VList_decode (b : bin) :=
    fst (VList_decode_pair b).

  Lemma VList_encode_decode_correct :
    encode_decode_correct (fun _ => True) VList_encode VList_decode.
  Proof.
  Admitted.

  Lemma List_encode_decode_correct_pair :
    encode_decode_correct (fun _ => True) VList_encode_pair VList_decode_pair.
  Proof.
  Admitted.

End VList_encode_decode.

Global Instance VList_decoder
       (A : Type)
       (encode_A : A * bin -> bin)
       (A_Decoder : decoder (fun _ => True) encode_A)
  : decoder (fun _ => True) (VList_encode encode_A) :=
  { decode := VList_decode _;
    decode_correct := @VList_encode_decode_correct _ encode_A }.

Global Instance VList_decoder_pair
       (A : Type)
       (encode_A : A * bin -> bin)
       (A_Decoder : decoder (fun _ => True) encode_A)
  : decoder (fun _ => True) (VList_encode_pair encode_A) :=
  { decode := VList_decode_pair _;
    decode_correct := @List_encode_decode_correct_pair _ encode_A }.
