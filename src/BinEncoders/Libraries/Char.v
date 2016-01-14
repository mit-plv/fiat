Require Export Coq.Strings.Ascii.
Require Import Coq.omega.Omega.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core
               Fiat.BinEncoders.Libraries.FixInt.

Section Char_encode_decode.

  Lemma nonzero_8 : 0 < 8. omega. Qed.

  Definition Char_encode (c : ascii) : bin.
    refine (FixInt_encode 8 (exist _ (N_of_ascii c) _)).
    unfold exp2; unfold exp2'.
    induction c.
    repeat (match goal with
              | B : bool |- _ => destruct B
            end); simpl; unfold Nlt; auto.
  Defined.

  Definition Char_decode (b : bin) : ascii :=
    ascii_of_N (proj1_sig (@Specs.decode _ _ _ _ (FixInt_decoder 8) b)).

  Theorem Char_encode_decode_correct :
    encode_decode_correct (fun _ => True) Char_encode Char_decode.
  Proof.
    unfold encode_decode_correct, Char_encode, Char_decode.
    intros c _.
    rewrite (@decode_correct _ _ _ (FixInt_encode 8) _); simpl; eauto.
    rewrite ascii_N_embedding; eauto.
  Qed.

  (*Theorem decode_shorten : decode_shorten decode.
  Proof.
    unfold decode_shorten, decode; intro ls.
    pose proof (shorten_R (FixInt_encode_decode 8 nonzero_8) ls).
    destruct (decode_R (FixInt_encode_decode 8 nonzero_8) ls); eauto.
  Qed.

  Definition Char_encode_decode :=
    {| predicate_R := fun _ => True;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct;
       shorten_R   := decode_shorten |}. *)
End Char_encode_decode.

Global Instance Char_decoder
  : decoder (fun _ => True) Char_encode :=
  { decode := Char_decode;
    decode_correct := Char_encode_decode_correct }.
