Set Implicit Arguments.

Class Transformer (bin : Type) :=
  { transform : bin -> bin -> bin;
    transform_id : bin;
    transform_id_left : forall l, transform transform_id l = l;
    transform_id_right : forall l, transform l transform_id = l;
    transform_assoc : forall l m n, transform l (transform m n) = transform (transform l m) n }.

Class TransformerUnit (bin : Type) (trans : Transformer bin) (T : Type) :=
  { transform_push : T -> bin -> bin;
    transform_pop : bin -> T * bin;
    transform_push_pop : forall t m, transform_pop (transform_push t m) = (t, m);
    transform_push_step : forall t m n, transform (transform_push t m) n =
                                        transform_push t (transform m n) }.

Class TransformerUnitOpt (bin : Type) (trans : Transformer bin) (T : Type) :=
  { transform_push_opt : T -> bin -> bin;
    transform_pop_opt : bin -> option (T * bin);
    transform_push_pop_opt :
      forall t m, transform_pop_opt (transform_push_opt t m) = Some (t, m);
    transform_push_step_opt : forall t m n, transform (transform_push_opt t m) n =
                                            transform_push_opt t (transform m n);
    transform_pop_opt_inj :
      forall t m b b',
        transform_pop_opt b = Some (t, m) ->
        transform_pop_opt b' = Some (t, m) ->
        b = b'
  }.
