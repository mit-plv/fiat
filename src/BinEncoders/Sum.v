Require Import Fiat.BinEncoders.Base.

Section Sum.

  Variable A : Type.
  Variable A_encode : A -> Bin.
  Variable A_decode : Bin -> A * Bin.
  Hypothesis A_proof : encode_append_correct A A_encode A_decode.

  Variable B : Type.
  Variable B_encode : B -> Bin.
  Variable B_decode : Bin -> B * Bin.
  Hypothesis B_proof : encode_append_correct B B_encode B_decode.

  Inductive Sum :=
  | S_left : A -> Sum
  | S_right : B -> Sum.

  Definition encode (x : Sum) :=
    match x with
      | S_left a => true :: A_encode a
      | S_right b => false :: B_encode b
    end.

  Definition decode (x : Bin) :=
    match x with
      (* bogus *)
      | nil =>
        let (a, x') := A_decode x
        in (S_left a, x')
      | true :: x' =>
        let (a, x'') := A_decode x'
        in (S_left a, x'')
      | false :: x' =>
        let (b, x'') := B_decode x'
        in (S_right b, x'')
    end.

  Theorem encode_append_correct : encode_append_correct Sum encode decode.
  Proof.
    unfold encode_append_correct.
    unfold encode, decode; intro x; destruct x as [a | b]; simpl; intros.
    - rewrite A_proof; eauto.
    - rewrite B_proof; eauto.
  Qed.

  Corollary encode_correct : encode_correct Sum encode decode.
  Proof.
    unfold encode_correct.
    intro x.
    rewrite <- app_nil_r with (l:=encode x).
    rewrite encode_append_correct.
    reflexivity.
  Qed.

End Sum.
