Require Export Coq.Strings.Ascii.
Require Import Coq.omega.Omega.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core
               Fiat.BinEncoders.Libraries.FixInt.

Section Char_encode_decode.

  Lemma nonzero_8 : 0 < 8. omega. Qed.

  Definition Char_encode_pair (p : ascii * bin) : bin.
    refine (FixInt_encode_pair 8 (exist _ (N_of_ascii (fst p)) _, snd p)).
    unfold exp2; unfold exp2'.
    induction (fst p).
    repeat (match goal with
              | B : bool |- _ => destruct B
            end); simpl; unfold Nlt; auto.
  Defined.

  Definition Char_encode (c : ascii) := Char_encode_pair (c, nil).

  Definition Char_decode_pair (b : bin) : ascii * bin :=
    let (_n, _bin) := @Specs.decode _ _ _ _ (FixInt_decoder_pair 8) b
    in  (ascii_of_N (proj1_sig _n), _bin).

  Definition Char_decode (b : bin) : ascii := fst (Char_decode_pair b).

  Theorem Char_encode_decode_correct_pair :
    encode_decode_correct (fun _ => True) Char_encode_pair Char_decode_pair.
  Proof.
    unfold encode_decode_correct, Char_encode_pair, Char_decode_pair.
    intros c _.
    rewrite (@decode_correct _ _ _ (FixInt_encode_pair 8) _); simpl; eauto.
    rewrite ascii_N_embedding; intuition.
  Qed.

  Theorem Char_encode_decode_correct :
    encode_decode_correct (fun _ => True) Char_encode Char_decode.
  Proof.
    unfold encode_decode_correct, Char_encode, Char_decode.
    intros c _.
    rewrite Char_encode_decode_correct_pair; intuition.
  Qed.

  (* Theorem decode_shorten : decode_shorten decode.
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

Global Instance Char_decoder_pair
  : decoder (fun _ => True) Char_encode_pair :=
  { decode := Char_decode_pair;
    decode_correct := Char_encode_decode_correct_pair }.
