Require Import Fiat.BinEncoders.BigNat Fiat.BinEncoders.Base.

Section List1.

  Context {A : Type}.
  Variable A_record : encode_decode_R A.

  Definition predicate (xs : list A) :=
    forall x, In x xs -> predicate_R A_record x.

  Fixpoint encode' (xs : list A) :=
    match xs with
      | nil => nil
      | x :: xs => encode_R A_record x ++ encode' xs
    end.

  Definition encode (xs : list A) :=
    encode_R BigNat_encode_decode (length xs) ++ encode' xs.

  Fixpoint decode' (b : bin) (d : nat) :=
    match d with
      | O => (nil, b)
      | S d' =>
        let (x, b') := decode_R A_record b in
        let (xs, b'') := decode' b' d' in
        (x :: xs, b'')
    end.

  Definition decode (b : bin) :=
    let (d, b') := decode_R BigNat_encode_decode b in
    decode' b' d.

  Theorem encode_correct : encode_correct predicate encode decode.
  Proof.
    unfold encode_correct, predicate.
    intros xs b pred.
    unfold encode, decode.
    rewrite <- app_assoc.
    rewrite (proof_R BigNat_encode_decode).
    induction xs as [ | x xs' ]; simpl; eauto.
    rewrite <- app_assoc. rewrite (proof_R A_record).
    rewrite IHxs'; eauto.
    intros; eapply pred; econstructor 2; eauto.
    eapply pred; econstructor 1; eauto.
    simpl; eauto.
  Qed.

  Lemma decode'_shorten' : forall d b, length (snd (decode' b d)) <= length b.
  Proof.
    induction d; intuition eauto; simpl.
    pose proof (shorten_R A_record b).
    destruct (decode_R A_record b); simpl in *; specialize (IHd b0).
    destruct (decode' b0 d). eapply Le.le_trans; eauto.
    eapply Le.le_trans; eauto. eapply Le.le_pred_n.
  Qed.

  Theorem decode_shorten : decode_shorten decode.
  Proof.
    unfold decode_shorten, decode; intro ls.
    pose proof (shorten_R BigNat_encode_decode ls).
    destruct (decode_R BigNat_encode_decode ls).
    eapply Le.le_trans. eapply decode'_shorten'. eauto.
  Qed.

  Definition List1_encode_decode :=
    {| predicate_R := predicate;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct;
       shorten_R   := decode_shorten |}.
End List1.
