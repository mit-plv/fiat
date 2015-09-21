Require Import Unary Base.

Section List.

  Variable A : Type.
  Variable A_encode : A -> Bin.
  Variable A_decode : Bin -> A * Bin.
  Hypothesis A_proof : encode_append_correct A A_encode A_decode.

  Definition BIntList := list A.

  Fixpoint encode' (xs : BIntList) :=
    match xs with
      | nil => nil
      | x :: xs => A_encode x ++ encode' xs
    end.

  Definition encode (xs : BIntList) :=
    Unary.encode (length xs) ++ encode' xs.

  Fixpoint decode' (b : Bin) (d : nat) :=
    match d with
      | O => (nil, b)
      | S d' =>
        let (x, b') := A_decode b in
        let (xs, b'') := decode' b' d' in
        (x :: xs, b'')
    end.

  Definition decode (b : Bin) :=
    let (d, b') := Unary.decode b in
    decode' b' d.

  Theorem encode_append_correct : encode_append_correct BIntList encode decode.
  Proof.
    unfold encode_append_correct.
    intros xs b.
    unfold encode, decode.
    rewrite <- app_assoc. rewrite Unary.encode_append_correct.
    induction xs as [ | x xs' ]; simpl; eauto.
    rewrite <- app_assoc. rewrite A_proof.
    rewrite IHxs'; eauto.
  Qed.

  Corollary encode_correct : encode_correct BIntList encode decode.
  Proof.
    unfold encode_correct.
    intro x.
    rewrite <- app_nil_r with (l:=encode x).
    rewrite encode_append_correct.
    reflexivity.
  Qed.

End ListBinaryInt.
