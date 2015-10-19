Require Import FixInt Ascii BinNat Omega Base.

Section Char.

  Definition encode c := encode_R (FixInt_encode_decode 8) (N_of_ascii c).

  Definition decode b :=
    let (n, ext) := decode_R (FixInt_encode_decode 8) b
    in (ascii_of_N n, ext).

  Lemma N_of_ascii_size : forall c, (N_of_ascii c < exp2 8)%N.
  Proof.
    unfold exp2; unfold exp2'.
    induction c.
    repeat (match goal with
              | B : bool |- _ => destruct B
            end); simpl; unfold Nlt; auto.
  Qed.

  Theorem encode_correct : encode_correct (fun _ => True) encode decode.
  Proof.
    unfold encode_correct, encode, decode.
    intros c ext _.
    rewrite (proof_R (FixInt_encode_decode 8) _ _ (N_of_ascii_size _)).
    rewrite ascii_N_embedding. reflexivity.
  Qed.

  Definition Char_encode_decode :=
    {| predicate_R := fun _ => True;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct |}.
End Char.
