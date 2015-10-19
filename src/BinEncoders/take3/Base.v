Require Export List.

Definition bin := list bool.

Section Specifications.

  Context {A : Type}.

  Variable predicate : A -> Prop.
  Variable encode : A -> bin.
  Variable decode : bin -> A * bin.

  Definition encode_correct :=
    forall val ext, predicate val -> decode ((encode val) ++ ext) = (val, ext).

End Specifications.

Record encode_decode_R {A : Type} :=
  { predicate_R : A -> Prop;
    encode_R    : A -> bin;
    decode_R    : bin -> A * bin;
    proof_R     : encode_correct predicate_R encode_R decode_R }.
Arguments encode_decode_R : clear implicits.
