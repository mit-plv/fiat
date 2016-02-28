Require Export
        Coq.Lists.List.

Set Implicit Arguments.

Section Specifications.
  Variable A B C E E' Z : Type.

  Definition encode_decode_correct
             (envequiv  : E -> E' -> Prop)
             (transform : B -> C -> Z)
             (predicate : A -> Prop)
             (encode : A -> E -> B * E)
             (decode :  Z -> E' -> A * C * E') :=
    forall env env' xenv xenv' data data' bin ext ext',
      envequiv env env' ->
      predicate data ->
      encode data env = (bin, xenv) ->
      decode (transform bin ext) env' = (data', ext', xenv') ->
      envequiv xenv xenv' /\ data = data' /\ ext = ext'.

  Class decoder
        (envequiv  : E -> E' -> Prop)
        (transform : B -> C -> Z)
        (predicate : A -> Prop)
        (encode : A -> E -> B * E) :=
    { decode : Z -> E' -> A * C * E';
      decode_correct : encode_decode_correct envequiv transform predicate encode decode }.
End Specifications.
