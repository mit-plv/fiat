Require Export Coq.Lists.List.

Definition Bin := list bool.

Section Specifications.

  Variable A : Type.
  Variable encode : A -> Bin.
  Variable decode : Bin -> A * Bin.

  Definition encode_append_correct := forall x b, decode ((encode x) ++ b) = (x, b).
  Definition encode_correct := forall x, fst (decode (encode x)) = x.

End Specifications.
