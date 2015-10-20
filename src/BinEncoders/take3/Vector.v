Require Import Fiat.BinEncoders.Base.
Require Export Vector.

Section Vector.

  Context {A : Type}.
  Variable A_record : encode_decode_R A.
  Variable n : nat.

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

  Lemma encode_correct :
    encode_correct (predicate n) encode decode.
  Proof.
    apply encode_correct'.
  Qed.

  Definition Vector_encode_decode :=
    {| predicate_R := predicate n;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct |}.
End Vector.
