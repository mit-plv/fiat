Require Import Fiat.BinEncoders.Base.

Section BigNat.

  Fixpoint encode (n : nat) :=
    match n with
      | O => false :: nil
      | S n' => true :: encode n'
    end.

  Fixpoint decode (b : bin) :=
    match b with
      | nil => (O, nil)
      | true :: b' =>
        match decode b' with
          | (n', e) => (S n', e)
        end
      | false :: b' => (O, b')
    end.

  Theorem encode_correct : encode_correct (fun _ => True) encode decode.
    unfold encode_correct.
    induction val; simpl; intuition eauto.
    rewrite IHval; eauto.
  Qed.

  Theorem decode_shorten : decode_shorten decode.
  Proof.
    unfold decode_shorten.
    destruct ls; intuition eauto.
    induction ls; destruct b; simpl; intuition eauto.
    destruct a; simpl in *; intuition eauto.
    destruct (decode ls); intuition eauto.
  Qed.

  Definition BigNat_encode_decode :=
    {| predicate_R := fun _ => True;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct;
       shorten_R   := decode_shorten |}.

End BigNat.
