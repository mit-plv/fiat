Set Implicit Arguments.

Class Monoid (bin : Type) :=
  { mappend : bin -> bin -> bin;
    mempty : bin;
    bin_measure : bin -> nat;
    mappend_measure :
      forall b b', bin_measure (mappend b b') =
                   bin_measure b + bin_measure b';
    mempty_left : forall l, mappend mempty l = l;
    mempty_right : forall l, mappend l mempty = l;
    mappend_assoc : forall l m n, mappend l (mappend m n) = mappend (mappend l m) n }.

Class MonoidUnit (bin : Type) (trans : Monoid bin) (T : Type) :=
  { mappend_push : T -> bin -> bin;
    mappend_pop : bin -> T * bin;
    mappend_push_pop : forall t m, mappend_pop (mappend_push t m) = (t, m);
    mappend_push_step : forall t m n, mappend (mappend_push t m) n =
                                        mappend_push t (mappend m n) }.

Class MonoidUnitOpt (bin : Type) (trans : Monoid bin) (T : Type) :=
  { T_measure : T -> nat;
    T_measure_gt_0 : forall t, 0 < T_measure t;
    mappend_push_opt : T -> bin -> bin;
    mappend_pop_opt : bin -> option (T * bin);
    measure_push :
      forall t b,
        bin_measure (mappend_push_opt t b) = bin_measure b + T_measure t;
    measure_pop_Some :
      forall b' t b,
        mappend_pop_opt b = Some (t, b')
        -> bin_measure b = bin_measure b' + T_measure t;
    mappend_push_pop_opt :
      forall t m, mappend_pop_opt (mappend_push_opt t m) = Some (t, m);
    mappend_push_step_opt
    : forall t m n, mappend (mappend_push_opt t m) n =
                    mappend_push_opt t (mappend m n);
    mappend_pop_opt_inj :
      forall t m b b',
        mappend_pop_opt b = Some (t, m) ->
        mappend_pop_opt b' = Some (t, m) ->
        b = b'
  }.

Class QueueMonoidOpt (bin : Type) (trans : Monoid bin) (B : Type) :=
  { B_measure : B -> nat;
    B_measure_gt_0 : forall b, 0 < B_measure b;
    enqueue_opt : B -> bin -> bin;
    dequeue_opt : bin -> option (B * bin);
    measure_enqueue :
      forall b b',
        bin_measure (enqueue_opt b b') = bin_measure b' + B_measure b;
    measure_dequeue_Some :
      forall b' t b,
        dequeue_opt b = Some (t, b')
        -> bin_measure b = bin_measure b' + B_measure t;
    dequeue_mappend_opt :
      forall t b b' b'',
        dequeue_opt b = Some (t, b')
        -> dequeue_opt (mappend b b'') = Some (t, mappend b' b'');
    enqueue_mappend_opt :
      forall b b' b'',
        enqueue_opt b (mappend b' b'') = mappend b' (enqueue_opt b b'');
    dequeue_head_opt :
      forall t,
        dequeue_opt (enqueue_opt t mempty) = Some (t, mempty);
    dequeue_None :
        dequeue_opt mempty = None;
    dequeue_opt_inj :
      forall t m b b',
        dequeue_opt b = Some (t, m) ->
        dequeue_opt b' = Some (t, m) ->
        b = b'
  }.

  Definition lt_B {B} {monoid : Monoid B} (b b' : B) : Prop :=
    bin_measure b < bin_measure b'.

  Definition le_B {B} {monoid : Monoid B} (b b' : B) : Prop :=
    bin_measure b <= bin_measure b'.

  Lemma well_founded_lt_b {B}
        {monoid : Monoid B}
    : well_founded lt_B.
  Proof.
    constructor.
    unfold lt_B; induction (bin_measure a); intros.
    - inversion H.
    - inversion H; subst.
      + constructor; eauto.
      + eauto.
  Qed.

  Lemma measure_mempty {B} `{Monoid B} :
    bin_measure mempty = 0.
  Proof.
    assert (forall m n, n = n + m -> m = 0) by
        (induction n; simpl; eauto).
    eapply H0.
    etransitivity.
    - eapply (mappend_measure mempty mempty).
    - rewrite mempty_left; reflexivity.
  Qed.

Class RichMonoidOpt (bin : Type) (trans : Monoid bin) :=
  {
    mappend_inj : forall (t1 t2 t : bin), mappend t1 t = mappend t2 t -> t1 = t2
  }.
