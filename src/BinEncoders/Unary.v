Require Import Fiat.BinEncoders.Base.

Section Unary.

  Definition UInt := nat.

  Fixpoint encode (n : UInt) :=
    match n with
      | O => false :: nil
      | S n' => true :: encode n'
    end.

  Fixpoint decode (b : Bin) :=
    match b with
      | nil => (O, nil)
      | true :: b' =>
        match decode b' with
          | (n', e) => (S n', e)
        end
      | false :: b' => (O, b')
    end.

  Theorem encode_append_correct : encode_append_correct UInt encode decode.
  Proof.
    unfold encode_append_correct.
    induction x; simpl; intuition eauto.
    rewrite IHx; eauto.
  Qed.

  Corollary encode_correct : encode_correct UInt encode decode.
  Proof.
    unfold encode_correct.
    intro x.
    rewrite <- app_nil_r with (l:=encode x).
    rewrite encode_append_correct.
    reflexivity.
  Qed.

End Unary.
