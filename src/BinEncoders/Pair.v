Require Import Fiat.BinEncoders.Base.

Section Pair.

  Variable A : Type.
  Variable A_encode : A -> Bin.
  Variable A_decode : Bin -> A * Bin.
  Hypothesis A_proof : encode_append_correct A A_encode A_decode.

  Variable B : Type.
  Variable B_encode : B -> Bin.
  Variable B_decode : Bin -> B * Bin.
  Hypothesis B_proof : encode_append_correct B B_encode B_decode.

  Definition Pair := (A * B)%type.

  Definition encode (x : Pair) :=
    (A_encode (fst x)) ++ (B_encode (snd x)).

  Definition decode (b : Bin) :=
    let (x, b') := A_decode b in
    let (y, b'') := B_decode b' in
    ((x, y), b'').

  Theorem encode_append_correct : encode_append_correct Pair encode decode.
  Proof.
    unfold encode_append_correct.
    unfold encode, decode; destruct x as [x y].
    intros; simpl; rewrite <- app_assoc.
    rewrite A_proof. rewrite B_proof. eauto.
  Qed.

  Corollary encode_correct : encode_correct Pair encode decode.
  Proof.
    unfold encode_correct.
    intro x.
    rewrite <- app_nil_r with (l:=encode x).
    rewrite encode_append_correct.
    reflexivity.
  Qed.

End Pair.
