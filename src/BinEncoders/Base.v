Require Export Coq.Lists.List.

Definition Bin := list bool.

Section Specifications.

  Variable A : Type.
  Variable encode : A -> Bin.
  Variable decode : Bin -> A * Bin.

  Hypothesis predicate : A -> Prop.

  Definition encode_append_correct :=
    forall val ext, predicate val -> decode ((encode val) ++ ext) = (val, ext).

End Specifications.
