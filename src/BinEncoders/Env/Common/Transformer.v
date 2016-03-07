Set Implicit Arguments.

Section Transformer.
  Variable B : Type.

  Class Transformer :=
    { transform : B -> B -> B;
      transform_id : B;
      transform_id_pf : forall l, transform transform_id l = l;
      transform_assoc : forall l m n, transform l (transform m n) = transform (transform l m) n }.
End Transformer.