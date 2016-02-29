Require Export
        Coq.Lists.List.

Set Implicit Arguments.

Section Specifications.
  Variable A B E E' : Type.

  Class Transformer :=
    { transform : B -> B -> B;
      transform_id : B;
      transform_id_pf : forall l, transform transform_id l = l;
      transform_assoc : forall l m n, transform l (transform m n) = transform (transform l m) n }.

  Definition encode_decode_correct
             (envequiv  : E -> E' -> Prop)
             (transformer : Transformer)
             (predicate : A -> Prop)
             (encode : A -> E -> B * E)
             (decode :  B -> E' -> A * B * E') :=
    forall env env' xenv xenv' data data' bin ext ext',
      envequiv env env' ->
      predicate data ->
      encode data env = (bin, xenv) ->
      decode (transform bin ext) env' = (data', ext', xenv') ->
      envequiv xenv xenv' /\ data = data' /\ ext = ext'.

  Class decoder
        (envequiv  : E -> E' -> Prop)
        (transformer : Transformer)
        (predicate : A -> Prop)
        (encode : A -> E -> B * E) :=
    { decode : B -> E' -> A * B * E';
      decode_correct : encode_decode_correct envequiv transformer predicate encode decode }.
End Specifications.
