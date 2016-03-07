Set Implicit Arguments.

Class Transformer :=
  { bin : Type;
    transform : bin -> bin -> bin;
    transform_id : bin;
    transform_id_pf : forall l, transform transform_id l = l;
    transform_assoc : forall l m n, transform l (transform m n) = transform (transform l m) n }.
