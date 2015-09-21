Require Import BinNums Unary Base.

Section Binary.

  Definition BInt := N.

  Fixpoint encode'' (n : positive) :=
    match n with
      | xH => true :: nil
      | xI n' => true :: encode'' n'
      | xO n' => false :: encode'' n'
    end.

  Definition encode' (n : BInt) :=
    match n with
      | N0 => nil
      | Npos pos => encode'' pos
    end.

  Definition encode (n : BInt) :=
    let e := encode' n in
    Unary.encode (length e) ++ e.

  Fixpoint decode'' (b : Bin) (d : nat) :=
    match d, b with
      | S O, true :: b' => (xH, b')
      | S d', true :: b' =>
        match decode'' b' d' with
          | (pos, b'') => (xI pos, b'')
        end
      | S d', false :: b' =>
        match decode'' b' d' with
          | (pos, b'') => (xO pos, b'')
        end
      (* bogus value *)
      | _, _ => (xH, nil)
    end.

  Definition decode' (b : Bin) (d : nat) :=
    match d with
      | O => (N0, b)
      | S _ =>
        match decode'' b d with
          | (pos, b') => (Npos pos, b')
        end
    end.

  Definition decode (b : Bin) :=
    match Unary.decode b with
      | (d, b') => decode' b' d
    end.

  Lemma encode''_nonnil : forall n, length (encode'' n) <> O.
  Proof.
    intro n.
    destruct n; simpl; eauto.
  Qed.

  Theorem encode_append_correct : encode_append_correct BInt encode decode.
  Proof.
    unfold encode_append_correct.
    induction x; simpl; intuition eauto.
    unfold decode, encode, encode', decode'.
    rewrite <- app_assoc.
    rewrite Unary.encode_append_correct.
    destruct (length (encode'' p)) eqn: eq; [
        apply encode''_nonnil in eq; intuition | rewrite <- eq; clear eq ].
    induction p; simpl; eauto.
    - destruct (length (encode'' p)) eqn: eq; [
        apply encode''_nonnil in eq; intuition | rewrite <- eq in *; clear eq ].
      destruct (decode'' (encode'' p ++ b) (length (encode'' p))).
      inversion IHp; subst; reflexivity.
    - destruct (length (encode'' p)) eqn: eq; [
        apply encode''_nonnil in eq; intuition | rewrite <- eq in *; clear eq ].
      destruct (decode'' (encode'' p ++ b) (length (encode'' p))).
      inversion IHp; subst; reflexivity.
  Qed.

  Corollary encode_correct : encode_correct BInt encode decode.
  Proof.
    intro x.
    rewrite <- app_nil_r with (l:=encode x).
    rewrite encode_append_correct.
    reflexivity.
  Qed.

End Binary.
