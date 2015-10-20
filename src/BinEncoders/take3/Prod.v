Require Import Fiat.BinEncoders.Base.

Section Prod.

  Context {A B : Type}.

  Variable A_record : encode_decode_R A.
  Variable B_record : encode_decode_R B.

  Definition predicate (data : A * B) :=
    predicate_R A_record (fst data) /\ predicate_R B_record (snd data).

  Definition encode (data : A * B) :=
    (encode_R A_record (fst data)) ++ (encode_R B_record (snd data)).

  Definition decode (b : bin) :=
    let (x, b') := decode_R A_record b in
    let (y, b'') := decode_R B_record b' in
    ((x, y), b'').

  Theorem encode_correct : encode_correct predicate encode decode.
    unfold encode_correct, predicate.
    unfold encode, decode; destruct val as [x y].
    intros; simpl; rewrite <- app_assoc.
    rewrite (proof_R A_record); [ rewrite (proof_R B_record) | ]; firstorder.
  Qed.

  Definition encode_decode :=
    {| predicate_R := predicate;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct |}.
End Prod.
