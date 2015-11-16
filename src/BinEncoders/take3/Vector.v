Require Import Fiat.BinEncoders.Base.
Require Export Coq.Vectors.Vector.

Section Vector.

  Context {A : Type}.
  Variable A_record : encode_decode_R A.
  Variable n : nat.
  Hypothesis n_nonzero : 0 < n.

  Definition predicate (i : nat) (data : t A i) :=
    forall x, In x data -> predicate_R A_record x.

  Fixpoint encode' (i : nat) (x : t A i) : bin :=
    match x with
      | nil => List.nil
      | cons x i' x'  => (encode_R A_record x) ++ (encode' i' x')
    end.

  Definition encode (x : t A n) := encode' n x.

  Fixpoint decode' (i : nat) (b : bin) : ((t A i) * bin) :=
    match i with
      | O => (nil A, b)
      | S i' =>
        let (x, b') := decode_R A_record b in
        let (xs, b'') := decode' i' b' in
        (cons A x i' xs, b'')
    end.

  Definition decode (b : bin) := decode' n b.

  Lemma encode_correct' :
    forall i, encode_correct (predicate i) (encode' i) (decode' i).
  Proof.
    unfold encode_correct.
    intros i xs b pred.
    induction xs; simpl; eauto.
    rewrite <- app_assoc. rewrite (proof_R A_record).
    rewrite IHxs. reflexivity.
    unfold predicate in *; intros; eapply pred; econstructor; eauto.
    unfold predicate in *; eapply pred; econstructor; eauto.
  Qed.

  Theorem encode_correct :
    encode_correct (predicate n) encode decode.
  Proof.
    apply encode_correct'.
  Qed.

  Lemma decode'_shorten' :
    forall i ls, length (snd (decode' i ls)) <= length ls.
  Proof.
    induction i; simpl; intuition eauto.
    pose proof (shorten_R A_record ls); destruct (decode_R A_record ls).
    specialize (IHi b); destruct (decode' i b).
    eapply Le.le_trans; eauto. eapply Le.le_trans; eauto. eapply Le.le_pred_n.
  Qed.

  Theorem decode_shorten : decode_shorten decode.
  Proof.
    unfold decode_shorten, decode.
    induction ls; simpl; intuition.
    { eapply decode'_shorten'. }
    { destruct n. inversion n_nonzero. simpl.
      pose proof (shorten_R A_record (a :: ls));
        destruct (decode_R A_record (a :: ls)).
      pose proof (decode'_shorten' n0 b).
      destruct (decode' n0 b).
      eapply Le.le_trans; eauto. }
  Qed.

  Definition Vector_encode_decode :=
    {| predicate_R := predicate n;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct;
       shorten_R   := decode_shorten |}.
End Vector.
