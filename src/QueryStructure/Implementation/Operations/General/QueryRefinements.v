Require Import Coq.Strings.String Coq.Lists.List Coq.Sorting.Permutation
        Coq.Bool.Bool Coq.Sets.Ensembles
        Coq.Logic.FunctionalExtensionality
        ADTSynthesis.ADTNotation ADTSynthesis.Common
        ADTSynthesis.Common.ListFacts
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Computation
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Operations.FlattenCompList
        ADTSynthesis.QueryStructure.Specification.Operations.Query
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure.

(* [Query_For] and all aggregates are opaque, so we need to make them
   transparent in order to reason about them. *)
Local Transparent Query_For Count Max MaxN MaxZ Sum SumN SumZ.
Require Import Coq.NArith.NArith Coq.ZArith.ZArith.

Lemma refine_Count {A} rows
: refine (@Count A rows)
         (l <- rows;
          ret (List.length l)).
Proof. reflexivity. Qed.

Lemma refine_FoldAggregateOption {A} (rows: Comp (list A)) (updater: A -> A -> A) :
  refine (@FoldAggregateOption A updater rows)
         (l <- rows;
          ret (foldOption updater l)).
Proof. reflexivity. Qed.

Lemma refine_FoldAggregate {A B} (rows: Comp (list B)) (updater: A -> B -> A) (default: A) :
  refine (@FoldAggregate A B updater default rows)
         (l <- rows;
          ret (List.fold_left updater l default)).
Proof. reflexivity. Qed.

Lemma refine_Sum rows :
  refine (Sum rows)
         (l <- rows;
          ret (List.fold_left plus l 0)).
Proof. reflexivity. Qed.

Lemma refine_SumN rows :
  refine (SumN rows)
         (l <- rows;
          ret (List.fold_left N.add l 0%N)).
Proof. reflexivity. Qed.

Lemma refine_SumZ rows :
  refine (SumZ rows)
         (l <- rows;
          ret (List.fold_left Z.add l 0%Z)).
Proof. reflexivity. Qed.

Lemma refine_Max rows :
  refine (Max rows)
         (l <- rows;
          ret (foldOption max l)).
Proof. reflexivity. Qed.

Lemma refine_MaxN rows :
  refine (MaxN rows)
         (l <- rows;
          ret (foldOption N.max l)).
Proof. reflexivity. Qed.

Lemma refine_MaxZ rows :
  refine (MaxZ rows)
         (l <- rows;
          ret (foldOption Z.max l)).
Proof. reflexivity. Qed.

Lemma refine_For
: forall ResultT (bod : Comp (list ResultT)),
    refine (For bod)%QuerySpec
           (result <- bod;
            {l | Permutation result l}).
Proof. reflexivity. Qed.

Tactic Notation "t_morphism" reference(symb) :=
  intros * H; unfold symb; rewrite H; reflexivity.

Add Parametric Morphism ResultT
: (@Query_For ResultT)
    with signature (refine ==> refine)
      as refine_refine_For.
Proof.
  t_morphism Query_For.
Qed.

Add Parametric Morphism ResultT
: (@Count ResultT)
    with signature (refine ==> refine)
      as refine_refine_Count.
Proof.
  t_morphism Count.
Qed.

Add Parametric Morphism {A B} (updater: A -> B -> A) :
  (@FoldAggregate A B updater)
    with signature (eq ==> refine ==> refine)
      as FoldAggregate_eq_refine_refine_morphism.
Proof.
  t_morphism FoldAggregate.
Qed.

Add Parametric Morphism {A} (updater: A -> A -> A) :
  (@FoldAggregateOption A updater)
    with signature (refine ==> refine)
      as FoldAggregateOption_refine_refine_morphism.
Proof.
  t_morphism FoldAggregateOption.
Qed.

Add Morphism Max
    with signature (refine ==> refine)
      as Max_refine_refine_Morphism.
Proof.
  t_morphism Max.
Qed.

Add Morphism MaxN
    with signature (refine ==> refine)
      as MaxN_refine_refine_Morphism.
Proof.
  t_morphism MaxN.
Qed.

Add Morphism MaxZ
    with signature (refine ==> refine)
      as MaxZ_refine_refine_Morphism.
Proof.
  t_morphism MaxZ.
Qed.

Add Morphism Sum
    with signature (refine ==> refine)
      as Sum_refine_refine_Morphism.
Proof.
  t_morphism Sum.
Qed.

Add Morphism SumN
    with signature (refine ==> refine)
      as SumN_refine_refine_Morphism.
Proof.
  t_morphism SumN.
Qed.

Add Morphism SumZ
    with signature (refine ==> refine)
      as SumZ_refine_refine_Morphism.
Proof.
  t_morphism SumZ.
Qed.

Lemma refine_Count_bind_bind_app {A}
: forall (l l' : Comp (list A)),
    refine (Count (la <- l;
                   la' <- l';
                   {l | Permutation.Permutation (la ++ la') l}))
           (len <- Count l;
            len' <- Count l';
            ret (len + len')).
Proof.
  intros; unfold Count.
  unfold refine; intros; inversion_by computes_to_inv; subst.
  econstructor; eauto.
  rewrite app_length; econstructor.
Qed.


Definition UnConstrQuery_In {ResultT}
           qsSchema (qs : UnConstrQueryStructure qsSchema)
           (R : @StringBound.BoundedString
                  (map relName (qschemaSchemas qsSchema)))
           (bod : @Tuple (schemaHeading (relSchema
                                           (StringBound.nth_Bounded relName (qschemaSchemas qsSchema) R))) -> Comp (list ResultT))
  :=
    QueryResultComp (GetUnConstrRelation qs R) bod.

Lemma refine_flatten_CompList_func {A B}
: forall (l : list A) (f f' : A -> Comp (list B)),
    pointwise_relation _ refine f f'
    -> refine (flatten_CompList (map f l))
              (flatten_CompList (map f' l)).
Proof.
  induction l; simpl; intros.
  + reflexivity.
  + rewrite H; setoid_rewrite (IHl f f' H).
    reflexivity.
Qed.

Add Parametric Morphism {ResultT} P
: (@Query_Where ResultT P)
    with signature (refine ==> refine)
      as refine_Query_Where_In.
Proof.
  unfold Query_Where, refine; intros;
  inversion_by computes_to_inv; econstructor; intuition.
Qed.

Add Parametric Morphism {ResultT} qsSchema qs R
: (@UnConstrQuery_In ResultT qsSchema qs R)
    with signature (pointwise_relation _ refine ==> refine)
      as refine_UnConstrQuery_In.
Proof.
  intros; unfold UnConstrQuery_In, QueryResultComp.
  apply refine_bind.
  reflexivity.
  unfold pointwise_relation; intros;
  eapply refine_flatten_CompList_func; eauto.
Qed.

(* Cross product of lists using heterogenous lists. *)
Definition Join_Comp_Lists
           {A : Type}
           {f : A -> Type}
           {As : list A}
           {a : A}
           (l' : list (ilist f As))
           (c : ilist f As -> Comp (list (f a)))
: Comp (list (ilist f (a :: As))) :=
  flatten_CompList (map (fun l' => l <- c l'; ret (map (fun fa => icons _ fa l') l)) l').

Definition Build_single_Tuple_list
           {heading}
           (l : list (@Tuple heading))
: list (ilist (@Tuple) [heading])
  := map (fun a => icons _ a (inil _)) l.

Lemma filter_and_join_ilist_tail
      {A}
      {a}
      {As}
      (f' : A -> Type)
: forall
    (f : (ilist f' As) -> bool)
    (s1 : list (ilist f' As))
    (s2 : ilist f' As -> Comp (list (f' a)))
    filter_rest,
    (forall a, List.In a s1 -> exists v, computes_to (s2 a) v)
    -> refineEquiv (l <- (Join_Comp_Lists s1 s2);
                    ret (filter (fun x : ilist f' (a :: As) => f (ilist_tl x) && filter_rest x) l))
                   (l <- Join_Comp_Lists (filter f s1) s2;
                    ret (filter filter_rest l)).
Proof.
  split; induction s1; unfold Join_Comp_Lists in *; simpl in *; intros; eauto.
  - simplify with monad laws; simpl; intros v Comp_v;
    inversion_by computes_to_inv; subst; repeat econstructor.
  - simplify with monad laws; intros v.
    case_eq (f a0); simpl; intros a0_eq Comp_v.
    + inversion_by computes_to_inv; subst; econstructor; eauto.
      pose (IHs1 (fun a In_a => H _ (or_intror In_a)) _ (BindComputes _ H3 (ReturnComputes _))); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      repeat rewrite filter_app, filter_map; rewrite H4; simpl.
      rewrite a0_eq, filter_and, filter_true; eauto.
    + pose (IHs1 (fun a In_a => H _ (or_intror In_a)) _ Comp_v); inversion_by computes_to_inv; subst.
      destruct (H a0); eauto.
      repeat (econstructor; eauto).
      rewrite filter_app, filter_map; simpl; intros;
      rewrite a0_eq, filter_false; constructor.
  - intros v Comp_v; inversion_by computes_to_inv; subst; eauto.
  - intros v Comp_v; inversion_by computes_to_inv; subst.
    pose proof (IHs1 (fun a In_a => H _ (or_intror In_a)) _
                     (BindComputes _ H3 (ReturnComputes _))).
    inversion_by computes_to_inv.
    case_eq (f a0); intros a0_eq; simpl.
    + repeat (econstructor; eauto).
      repeat rewrite filter_app, filter_map; rewrite H4, filter_and; simpl.
      rewrite a0_eq, filter_and, filter_true; eauto.
    + repeat (econstructor; eauto).
      repeat rewrite filter_app, filter_map, filter_and; rewrite H4; simpl.
      rewrite a0_eq, filter_false; eauto.
Qed.

Definition List_Query_In
           {QueryT ResultT}
           (queriedList : list QueryT)
           (resultComp : QueryT -> Comp (list ResultT))
  :=
    flatten_CompList (map resultComp queriedList).

Corollary filter_join_ilist_tail
          {A}
          {a}
          {As}
          (f' : A -> Type)
: forall
    (f : (ilist f' As) -> bool)
    (s1 : list (ilist f' As))
    (s2 : ilist f' As -> Comp (list (f' a))),
    (forall a, List.In a s1 -> exists v, computes_to (s2 a) v)
    -> refineEquiv (l <- (Join_Comp_Lists s1 s2);
                    ret (filter (fun x : ilist f' (a :: As) => f (ilist_tl x)) l))
                   (Join_Comp_Lists (filter f s1) s2).
Proof.
  intros; pose proof (filter_and_join_ilist_tail f s1 s2 (fun _ => true)).
  setoid_rewrite filter_and in H0; setoid_rewrite filter_true in H0.
  setoid_rewrite H0; eauto; setoid_rewrite refineEquiv_unit_bind; reflexivity.
Qed.


Lemma refine_Join_Comp_Lists_filter_tail
: forall (heading : Heading)
         (headings : list Heading)
         (f : ilist (@Tuple) (headings) -> bool)
         (filter_rest : ilist (@Tuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : _ -> Comp (list ResultT))
         (l2 : ilist (@Tuple) headings
               -> Comp (list (@Tuple heading))),
    (forall a : ilist (@Tuple) headings,
     exists v : list (@Tuple heading),
       refine (l2 a) (ret v))
    ->
    forall l1,
      refine
        (l' <- Join_Comp_Lists l1 l2;
         List_Query_In
           (filter (fun (a : ilist (@Tuple) (heading :: headings))
                    => f (ilist_tl a) && (filter_rest a)) l')
           resultComp)
        (l' <- Join_Comp_Lists (filter f l1) l2;
         List_Query_In (filter filter_rest l') resultComp).
Proof.
  intros; revert l2 H.
  unfold Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - setoid_rewrite refineEquiv_bind_unit; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    + inversion_by computes_to_inv; subst; econstructor; eauto.
      rewrite filter_app, filter_map in H2.
      unfold List_Query_In in H2.
      repeat rewrite map_app, map_map in H2.
      apply flatten_CompList_app_inv' in H2.
      destruct_ex; split_and.
      pose (IHl1 l2 H _ (BindComputes _ H3 H5)); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
    + destruct (H a); eauto.
      inversion_by computes_to_inv; subst; econstructor; eauto.
      pose (IHl1 l2 H _ (BindComputes _ H2 H3)); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_false; simpl; eauto.
Qed.

(* A version of [refine_Join_Comp_Lists_filter_tail] for the case that
      the realizeablity of [l2] depends on the elements of [l1]*)
Lemma refine_Join_Comp_Lists_filter_tail_cond
: forall (heading : Heading)
         (headings : list Heading)
         (f : ilist (@Tuple) (headings) -> bool)
         (filter_rest : ilist (@Tuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : _ -> Comp (list ResultT))
         (l1 : list (ilist (@Tuple) headings))
         (l2 : ilist (@Tuple) headings
               -> Comp (list (@Tuple heading))),
    (forall a : ilist (@Tuple) headings,
       List.In a l1 -> exists v : list (@Tuple heading),
                         refine (l2 a) (ret v))
    -> refine
         (l' <- Join_Comp_Lists l1 l2;
          List_Query_In
            (filter (fun (a : ilist (@Tuple) (heading :: headings))
                     => f (ilist_tl a) && (filter_rest a)) l')
            resultComp)
         (l' <- Join_Comp_Lists (filter f l1) l2;
          List_Query_In (filter filter_rest l') resultComp).
Proof.
  unfold Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - setoid_rewrite refineEquiv_bind_unit; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    + inversion_by computes_to_inv; subst; econstructor; eauto.
      rewrite filter_app, filter_map in H2.
      unfold List_Query_In in H2.
      rewrite map_app, map_map in H2.
      apply flatten_CompList_app_inv' in H2.
      destruct_ex; split_and.
      pose (IHl1 l2 (fun a In_a => H _ (or_intror In_a)) _ (BindComputes _ H3 H5)); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
    + destruct (H a); eauto.
      inversion_by computes_to_inv; subst; econstructor; eauto.
      pose (IHl1 l2 (fun a In_a => H _ (or_intror In_a)) _ (BindComputes _ H2 H3)); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_false; simpl; eauto.
Qed.

Definition Join_Filtered_Comp_Lists
           {A : Type}
           {f : A -> Type}
           {As : list A}
           {a : A}
           (l' : list (ilist f As))
           (c : ilist f As -> Comp (list (f a)))
           (cond : ilist f (a :: As) -> bool)
: Comp (list (ilist f (a :: As))) :=
  l <- Join_Comp_Lists l' c;
  ret (filter cond l).

Lemma Join_Filtered_Comp_Lists_id
      {A : Type}
      {f : A -> Type}
      {As : list A}
      {a : A}
: forall (l' : list (ilist f As))
         (c : ilist f As -> Comp (list (f a))),
    refine (Join_Comp_Lists l' c)
           (Join_Filtered_Comp_Lists l' c (fun _ => true)).
  unfold Join_Filtered_Comp_Lists; setoid_rewrite filter_true.
  intros; rewrite refineEquiv_unit_bind; reflexivity.
Qed.

Lemma refine_Join_Filtered_Comp_Lists_filter_tail_andb
: forall (heading : Heading) (headings : list Heading)
         (f g : ilist (@Tuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : ilist (@Tuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (cond : ilist (@Tuple) (heading :: headings) -> bool),
  forall l1 : list (ilist (@Tuple) headings),
    refine
      (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
       List_Query_In (filter (fun a => f a && g a) l') resultComp)
      (l' <- Join_Filtered_Comp_Lists l1 l2 (fun a => cond a && f a);
       List_Query_In (filter g l') resultComp).
Proof.
  intros; revert l2.
  unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - repeat setoid_rewrite refineEquiv_bind_unit; simpl; reflexivity.
  - repeat setoid_rewrite refineEquiv_bind_bind.
    repeat setoid_rewrite refineEquiv_bind_unit.
    repeat (f_equiv; intro).
    rewrite !filter_and; f_equiv.
Qed.

Corollary refine_Join_Filtered_Comp_Lists_filter_tail
: forall (heading : Heading) (headings : list Heading)
         (f : ilist (@Tuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : ilist (@Tuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (cond : ilist (@Tuple) (heading :: headings) -> bool),
  forall l1 : list (ilist (@Tuple) headings),
    refine
      (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
       List_Query_In (filter f l') resultComp)
      (l' <- Join_Filtered_Comp_Lists l1 l2 (fun a => cond a && f a);
       List_Query_In l' resultComp).
Proof.
  intros;
  pose proof (@refine_Join_Filtered_Comp_Lists_filter_tail_andb
                _ _ f (fun _ => true) _ resultComp l2 cond l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
  inversion_by computes_to_inv; subst.
  rewrite filter_and, filter_true in H1.
  eauto.
Qed.

Lemma refine_Join_Filtered_Comp_Lists_filter_hd_andb
: forall (heading : Heading) (headings : list Heading)
         (f : ilist (@Tuple) headings -> bool)
         (g : ilist (@Tuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : ilist (@Tuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (cond : ilist (@Tuple) (heading :: headings) -> bool),
    (forall a : ilist (@Tuple) headings,
     exists v : list Tuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist (@Tuple) headings),
      refine
        (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
         List_Query_In
           (filter
              (fun a : ilist (@Tuple) (heading :: headings) =>
                 (f (ilist_tl a) && g a)) l') resultComp)
        (l' <- Join_Filtered_Comp_Lists (filter f l1) l2 cond;
         List_Query_In (filter g l') resultComp).
Proof.
  intros; revert l2 H.
  unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - repeat setoid_rewrite refineEquiv_bind_unit; simpl; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    + inversion_by computes_to_inv; subst; econstructor; eauto.
      unfold List_Query_In in H2.
      rewrite !filter_app, !filter_map, !map_app, !map_map in H2.
      apply FlattenCompList.flatten_CompList_app_inv' in H2.
      destruct_ex; split_and.
      assert (computes_to (l' <- l <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist (@Tuple) headings =>
                                    l <- l2 l';
                                  ret (map (fun fa : Tuple => icons _ fa l') l))
                                 (filter f l1));
                           ret (filter cond l);
                           List_Query_In (filter g l') resultComp) x0)
        as H'
          by (setoid_rewrite <- filter_and in H5;
              repeat econstructor; eauto;
              setoid_rewrite <- filter_and; eauto).
      pose (IHl1 l2 H _ H'); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
    + destruct (H a); eauto.
      inversion_by computes_to_inv; subst; econstructor; eauto.
      assert (computes_to (l' <- l <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist (@Tuple) headings =>
                                    l <- l2 l';
                                  ret (map (fun fa : Tuple => icons _ fa l') l))
                                 (filter f l1));
                           ret (filter cond l);
                           List_Query_In (filter g l') resultComp) v)
        as H' by  (repeat econstructor; eauto).
      pose (IHl1 l2 H _ H'); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite a_eq, filter_false; simpl; eauto.
Qed.

Lemma refine_Join_Filtered_Comp_Lists_filter_hd
: forall (heading : Heading) (headings : list Heading)
         (f : ilist (@Tuple) headings -> bool)
         (ResultT : Type)
         (resultComp : ilist (@Tuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (cond : ilist (@Tuple) (heading :: headings) -> bool),
    (forall a : ilist (@Tuple) headings,
     exists v : list Tuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist (@Tuple) headings),
      refine
        (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
         List_Query_In
           (filter
              (fun a : ilist (@Tuple) (heading :: headings) =>
                 f (ilist_tl a)) l') resultComp)
        (l' <- Join_Filtered_Comp_Lists (filter f l1) l2 cond;
         List_Query_In l' resultComp).
Proof.
  intros; pose proof (@refine_Join_Filtered_Comp_Lists_filter_hd_andb
                        _ _ f (fun _ => true) _ resultComp l2 cond H l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
  inversion_by computes_to_inv; subst.
  rewrite filter_and, filter_true in H2.
  eauto.
Qed.

Lemma Join_Filtered_Comp_Lists_ExtensionalEq_filters
      {A : Type}
      {f : A -> Type}
      {As : list A}
      {a : A}
: forall (l' : list (ilist f As))
         (c : ilist f As -> Comp (list (f a)))
         (g g' : ilist f (a :: As) -> bool),
    ExtensionalEq g g'
    -> refine (Join_Filtered_Comp_Lists l' c g)
              (Join_Filtered_Comp_Lists l' c g').
Proof.
  unfold Join_Filtered_Comp_Lists; intros.
  f_equiv; intro.
  f_equiv; apply filter_by_equiv; eauto.
Qed.


Lemma refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb
: forall (heading1 heading2 : Heading) (headings : list Heading)
         (f g : ilist (@Tuple) (heading1 :: headings) -> bool)
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (l2' : ilist (@Tuple) (heading1 :: headings) -> Comp (list Tuple))
         (cond1 : ilist (@Tuple) (heading1 :: headings) -> bool)
         (cond2 : ilist (@Tuple) (heading2 :: heading1 :: headings) -> bool),
  forall l1 : list (ilist (@Tuple) headings),
    refine
      (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
       Join_Filtered_Comp_Lists (filter (fun a => f a && g a) l) l2' cond2)
      (l <- Join_Filtered_Comp_Lists l1 l2 (fun a => cond1 a && f a);
       Join_Filtered_Comp_Lists (filter g l) l2' cond2).
Proof.
  intros; revert l2 l2'.
  unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - repeat setoid_rewrite refineEquiv_bind_unit; simpl; reflexivity.
  - repeat setoid_rewrite refineEquiv_bind_bind.
    repeat setoid_rewrite refineEquiv_bind_unit.
    repeat setoid_rewrite <- filter_and.
    repeat (f_equiv; intro).
    setoid_rewrite andb_assoc.
    eauto.
Qed.

Corollary refine_Join_Join_Filtered_Comp_Lists_filter_tail
: forall (heading1 heading2 : Heading) (headings : list Heading)
         (f : ilist (@Tuple) (heading1 :: headings) -> bool)
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (l2' : ilist (@Tuple) (heading1 :: headings) -> Comp (list Tuple))
         (cond1 : ilist (@Tuple) (heading1 :: headings) -> bool)
         (cond2 : ilist (@Tuple) (heading2 :: heading1 :: headings) -> bool),
  forall l1 : list (ilist (@Tuple) headings),
    refine
      (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
       Join_Filtered_Comp_Lists (filter f l) l2' cond2)
      (l <- Join_Filtered_Comp_Lists l1 l2 (fun a => cond1 a && f a);
       Join_Filtered_Comp_Lists l l2' cond2).
Proof.
  intros;
  pose proof (@refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb
                _ _ _ f (fun _ => true) l2 l2' cond1 cond2 l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
  inversion_by computes_to_inv; subst.
  rewrite filter_and, filter_true in H1.
  eauto.
Qed.

Lemma refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb
: forall (heading1 heading2 : Heading) (headings : list Heading)
         (f : ilist (@Tuple) headings -> bool)
         (g : ilist (@Tuple) (heading1 :: headings) -> bool)
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (l2' : ilist (@Tuple) (heading1 :: headings) -> Comp (list Tuple))
         (cond1 : ilist (@Tuple) (heading1 :: headings) -> bool)
         (cond2 : ilist (@Tuple) (heading2 :: heading1 :: headings) -> bool),
    (forall a : ilist (@Tuple) headings,
     exists v : list Tuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist (@Tuple) headings),
      refine
        (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
         Join_Filtered_Comp_Lists  (filter (fun a : ilist (@Tuple) (_ :: _) => f (ilist_tl a) && g a) l) l2' cond2)
        (l <- Join_Filtered_Comp_Lists (filter f l1) l2 cond1;
         Join_Filtered_Comp_Lists (filter g l) l2' cond2).
Proof.
  intros; revert l2 l2' cond1 cond2 H.
  unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - repeat setoid_rewrite refineEquiv_bind_unit; simpl; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    + inversion_by computes_to_inv; subst; econstructor; eauto.
      rewrite !filter_app, !filter_map, !map_app, !map_map in H2.
      apply FlattenCompList.flatten_CompList_app_inv' in H2.
      destruct_ex; split_and; subst.
      assert (computes_to (l <- l <- FlattenCompList.flatten_CompList
                             (map
                                (fun l' : ilist (@Tuple) headings =>
                                   l <- l2 l';
                                 ret (map (fun fa : Tuple => icons _ fa l') l))
                                (filter f l1));
                           ret (filter cond1 l);
                           l0 <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist (@Tuple) (heading1 :: headings) =>
                                    l0 <- l2' l';
                                  ret (map (fun fa : Tuple => icons _ fa l') l0))
                                 (filter g l));
                           ret (filter cond2 l0)) (filter cond2 x1)) as H'
          by (repeat econstructor; eauto).
      pose (IHl1 l2 l2' cond1 cond2 H _ H'); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      econstructor.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
      rewrite !filter_app, H7; econstructor.
    + destruct (H a); eauto.
      inversion_by computes_to_inv; subst; econstructor; eauto.
      assert (computes_to (l <- l <- FlattenCompList.flatten_CompList
                             (map
                                (fun l' : ilist (@Tuple) headings =>
                                   l <- l2 l';
                                 ret (map (fun fa : Tuple => icons _ fa l') l))
                                (filter f l1));
                           ret (filter cond1 l);
                           l0 <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist (@Tuple) (heading1 :: headings) =>
                                    l0 <- l2' l';
                                  ret (map (fun fa : Tuple => icons _ fa l') l0))
                                 (filter g l));
                           ret (filter cond2 l0)) (filter cond2 x1)) as H'
          by (repeat econstructor; eauto).
      pose (IHl1 l2 l2' cond1 cond2 H _ H'); inversion_by computes_to_inv; subst.
      econstructor; eauto.
      econstructor.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite a_eq, filter_false; simpl; eauto.
      rewrite H6; eauto.
Qed.


Lemma refine_Join_Join_Filtered_Comp_Lists_filter_hd
: forall (heading1 heading2 : Heading) (headings : list Heading)
         (f : ilist (@Tuple) headings -> bool)
         (l2 : ilist (@Tuple) headings -> Comp (list Tuple))
         (l2' : ilist (@Tuple) (heading1 :: headings) -> Comp (list Tuple))
         (cond1 : ilist (@Tuple) (heading1 :: headings) -> bool)
         (cond2 : ilist (@Tuple) (heading2 :: heading1 :: headings) -> bool),
    (forall a : ilist (@Tuple) headings,
     exists v : list Tuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist (@Tuple) headings),
      refine
        (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
         Join_Filtered_Comp_Lists  (filter (fun a : ilist (@Tuple) (_ :: _) => f (ilist_tl a)) l) l2' cond2)
        (l <- Join_Filtered_Comp_Lists (filter f l1) l2 cond1;
         Join_Filtered_Comp_Lists l l2' cond2).
Proof.
  intros; pose proof (@refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb
                        _ _ _ f (fun _ => true) l2 l2' cond1 cond2 H l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
  inversion_by computes_to_inv; subst.
  rewrite filter_and, filter_true in H2.
  eauto.
Qed.


Lemma List_Query_In_Return
      {ResultT}
      headings
      (l : list (ilist (@Tuple) headings))
      (r : ilist (@Tuple) headings -> ResultT)
: refine (List_Query_In l (fun tup => (Return (r tup))%QuerySpec))
         (ret (map r l)).
Proof.
  unfold List_Query_In; induction l; simpl; eauto.
  - reflexivity.
  - setoid_rewrite IHl; simplify with monad laws.
    reflexivity.
Qed.




(*Add Parametric Morphism {A: Type} :
  (Query_For)
    with signature (@Equivalent_Ensembles A ==> refine)
      as refine_Query_For_Equivalent.
Proof.
  unfold impl, Query_For, refine; intros.
  inversion_by computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  apply H; apply H1; auto.
  apply H2; apply H; auto.
Qed.

Add Parametric Morphism {A: Type}
    qsSchema qs R
:
  (fun bod => Query_For (@UnConstrQuery_In qsSchema qs _ R bod))
    with signature ((pointwise_relation Tuple (@Equivalent_Ensembles A) ==> refine ))
      as refine_Query_For_In_Equivalent.
Proof.
  unfold impl, Query_For, pointwise_relation, UnConstrQuery_In, In, refine.
  intros; inversion_by computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  destruct (H1 _ H0); eexists; intuition; eauto.
  apply H; auto.
  destruct_ex; apply H2; eexists; intuition; eauto.
  apply H; auto.
Qed. *)

Lemma DropQSConstraintsQuery_In {A} :
  forall qs R bod,
    @Query_In A qs R bod =
    UnConstrQuery_In (DropQSConstraints qsHint) R bod.
Proof.
  reflexivity.
Qed.

Lemma DropQSConstraintsQuery_In_UnderBinder {A B} :
  forall qs R bod,
    (fun b : B => @Query_In A qs R (bod b)) =
    (fun b : B => UnConstrQuery_In (DropQSConstraints qsHint) R (bod b)).
Proof.
  reflexivity.
Qed.

(*Lemma Equivalent_Swap_In {ResultT}
      qsSchema qs R (bod : Tuple -> Comp (list ResultT))
      enumR
      (enumerableR : EnsembleListEquivalence (GetUnConstrRelation qs R) enumR)
:
  refine
    (@UnConstrQuery_In qsSchema qs _ R (fun tup => @UnConstrQuery_In qsSchema qs _ R' (bod tup)))


Lemma Equivalent_Swap_In {ResultT}
      qsSchema qs R R' (bod : Tuple -> Tuple -> Comp (list ResultT))
      enumR enumR'
      (enumerableR : EnsembleListEquivalence (GetUnConstrRelation qs R) enumR)
      (enumerableR' : EnsembleListEquivalence (GetUnConstrRelation qs R') enumR')
:
  refine
    (@UnConstrQuery_In qsSchema qs _ R (fun tup => @UnConstrQuery_In qsSchema qs _ R' (bod tup)))
    (@UnConstrQuery_In qsSchema qs _ R' (fun tup => @UnConstrQuery_In qsSchema qs _ R
                                             (fun tup' => bod tup' tup))).
Proof.
  unfold UnConstrQuery_In, QueryResultComp, In; intros.
  unfold refine; intros; inversion_by computes_to_inv; subst.
  econstructor.
  econstructor; eauto.
  econstructor 2 with (comp_a_value := x0).
  assert (forall a : Tuple,
            (queryBod <- {queryBod : Tuple -> list ResultT |
                    forall a0 : Tuple, bod a0 a ↝ queryBod a0};
             {resultList : list ResultT |
              Permutation.Permutation resultList
                                      (flatten (map queryBod enumR))}) ↝ x0 a).
  { intros; generalize (H1 a); intros; inversion_by computes_to_inv.
    econstructor.
    econstructor.
    intros; apply H4.
    econstructor.
    eapply Permutation_trans; eauto.
    eapply flatten_permutation.
    unfold pointwise_relation; intros; eapply Permutation_refl.
    eapply EnsembleListEquivalence_Permutation; eauto.
  }
  econstructor 2 with (comp_a_value := x0).


  subst; repeat econstructor.
  intros; eapply H3.

  repeat econstructor; eauto.
  intros; eapply enumerableR'; eauto.
  intros; eapply enumerableR'; eauto.
  intros.

  apply H1 simplify with monad laws.
  assert (refine
  Print refine_pick_forall_Prop.
  setoid_rewrite refine_pick_forall_Prop. refine_pick_forall; try eassumption.

  rewrite computes_
  inversion_by computes_to_inv; subst.

  induction x; simpl; subst.
  constructor 2 with (comp_a_value := []).
  econstructor.

  Focus 2.
  constructor.
[ | econstructor].
  F

  repeat (progress (destruct_ex; intuition)).
  induction x; simpl in *; subst.
  exists (@nil (@Tuple (schemaHeading
                           (relSchema
                              (@StringBound.nth_Bounded NamedSchema string
                                 relName (qschemaSchemas qsSchema) R'))) * list ResultT)).
  simpl; intuition.
  destruct_ex; intuition.
  induction x; simpl in *; subst.
  eapply H2.

  eapply H0; eauto.
  eexists x; split; eauto.
  Focus 2.
  apply H1.
Qed.

Lemma Equivalent_Swap_In_Where {A}
      qsSchema qs R {heading}
      (bod : @Tuple heading -> Tuple -> Ensemble A)
      (P : @Tuple heading -> Prop)
:
  pointwise_relation
    Tuple Equivalent_Ensembles
    (fun tup' : Tuple =>
       (@UnConstrQuery_In qsSchema qs _ R
                  (fun tup => Query_Where (P tup') (bod tup' tup))))
    (fun tup' : Tuple =>
       Query_Where (P tup') (@UnConstrQuery_In qsSchema qs _ R (bod tup'))).
Proof.
  unfold Equivalent_Ensembles, UnConstrQuery_In, Query_Where; split; intros;
  repeat (progress (destruct_ex; intuition)); eexists;
  split; eauto.
Qed.

Add Parametric Morphism {A: Type} :
  (Query_For)
    with signature (@Equivalent_Ensembles A ==> refine)
      as refine_Query_For_Equivalent.
Proof.
  unfold impl, Query_For, refine; intros.
  inversion_by computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  apply H; apply H1; auto.
  apply H2; apply H; auto.
Qed.

Add Parametric Morphism {A: Type}
    qsSchema qs R
:
  (fun bod => Query_For (@UnConstrQuery_In qsSchema qs _ R bod))
    with signature ((pointwise_relation Tuple (@Equivalent_Ensembles A) ==> refine ))
      as refine_Query_For_In_Equivalent.
Proof.
  unfold impl, Query_For, pointwise_relation, UnConstrQuery_In, In, refine.
  intros; inversion_by computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  destruct (H1 _ H0); eexists; intuition; eauto.
  apply H; auto.
  destruct_ex; apply H2; eexists; intuition; eauto.
  apply H; auto.
Qed. *)

Lemma refine_Count_if {A} :
  forall (b : bool) (t : A),
    refine (Count (if b then (Return t)%QuerySpec else ret []))
           (ret (if b then 1 else 0)).
Proof.
  intros; rewrite refine_Count.
  destruct b; simplify with monad laws; reflexivity.
Qed.

Add Parametric Morphism
    (A : Type)
    (f : A -> Type)
    (As : list A)
    (a : A)
    (l' : list (ilist f As))
: (@Join_Comp_Lists A f As a l')
    with signature
    (pointwise_relation _ refine) ==> refine
      as refine_Join_Comp_Lists.
Proof.
  unfold pointwise_relation; simpl; intros.
  induction l'; unfold Join_Comp_Lists; simpl.
  - reflexivity.
  - rewrite H; setoid_rewrite IHl'; reflexivity.
Qed.

Lemma refine_Where {A B} :
  forall (P : Ensemble A)
         (P_dec : DecideableEnsemble P)
         (bod : Comp (list B)),
  forall a,
    refine (Where (P a) bod)%QuerySpec
           (if (dec a) then
              bod
            else
              (ret [])).
Proof.
  unfold refine, Query_Where; intros.
  caseEq (dec a); rewrite H0 in H; econstructor;
  split; intros; eauto.
  apply dec_decides_P in H0; intuition.
  apply Decides_false in H0; intuition.
  inversion_by computes_to_inv; eauto.
Qed.


Require Import Coq.Arith.Arith Coq.omega.Omega.

Lemma refineEquiv_For_DropQSConstraints A qsSchema qs :
  forall bod,
    refine
      {H1 |
       exists or' : QueryStructure qsSchema * list A,
                    (queryRes <- (For bod)%QuerySpec;
                     ret (qs, queryRes)) ↝ or' /\
                    DropQSConstraints_AbsR (fst or') (fst H1) /\ snd or' = snd H1}
      (b <- (For bod)%QuerySpec;
       ret (DropQSConstraints qs, b) ) .
Proof.
  setoid_rewrite refineEquiv_pick_ex_computes_to_bind_and;
  intros; f_equiv; unfold pointwise_relation; intros.
  setoid_rewrite refineEquiv_pick_ex_computes_to_and;
    setoid_rewrite refineEquiv_bind_unit; simpl;
    unfold DropQSConstraints_AbsR;
    setoid_rewrite refineEquiv_pick_pair;
    setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws; f_equiv.
Qed.

Global Instance IndexedDecideableEnsemble
       {heading}
       {P : Ensemble (@Tuple heading)}
       {P_dec : DecideableEnsemble P}
: DecideableEnsemble (fun x : IndexedTuple => P (indexedTuple x)) :=
  {| dec itup := @dec _ _ P_dec (indexedTuple itup)|}.
Proof.
  intuition; eapply dec_decides_P; simpl in *; eauto.
Defined.

Ltac subst_strings :=
  repeat match goal with
           | [ H : string |- _ ] => subst H
           | [ H : BoundedIndex _ |- _ ] => subst H
         end.

Ltac pose_string_ids :=
  subst_strings;
  repeat match goal with
           | |- context [String ?R ?R'] =>
             let str := fresh "StringId" in
             set (String R R') as str in *
           | |- context [ ``(?R) ] =>
             let idx := fresh in
             set ``(R) as fresh in *
         end.

Tactic Notation "drop" "constraints" "from" "query" constr(methname) :=
  hone method methname;
  [ simplify with monad laws;
    subst_strings; repeat (setoid_rewrite DropQSConstraintsQuery_In; simpl);
    repeat setoid_rewrite DropQSConstraintsQuery_In_UnderBinder;
    simpl; pose_string_ids;
    setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws; cbv beta; simpl;
    match goal with
        H : DropQSConstraints_AbsR _ _ |- _ =>
        unfold DropQSConstraints_AbsR in H; rewrite H
    end;
    finish honing | ].

(*
Require Import String List FunctionalExtensionality Ensembles Common
        Computation BuildADTRefinements
        QueryStructureSchema QueryQSSpecs QueryStructure
        EnsembleListEquivalence.

Definition UnConstrQuery_In
           qsSchema
           (qs : UnConstrQueryStructure qsSchema)
           {ReturnT TraceT}
           (R : _)
           (bod : @Tuple _ -> Ensemble (ReturnT * TraceT))
           (el : ReturnT * (Tuple * TraceT))
  :=
  GetUnConstrRelation qs R (fst (snd el))
  /\ bod (fst (snd el)) (fst el, snd (snd el)).

Lemma DropQSConstraintsQuery_In {ReturnT TraceT} :
  forall qs R bod,
         @Query_In ReturnT TraceT qs R bod =
         UnConstrQuery_In (DropQSConstraints qsHint) R bod.
Proof.
  reflexivity.
Qed.

Lemma DropQSConstraintsQuery_In_UnderBinder {ReturnT TraceT B} :
  forall qs R bod,
    (fun b : B => @Query_In ReturnT TraceT qs R (bod b)) =
    (fun b : B => UnConstrQuery_In (DropQSConstraints qsHint) R (bod b)).
Proof.
  reflexivity.
Qed.

Definition Equivalent_Ensembles {ReturnT TraceT TraceT' : Type}
           (P : Ensemble (ReturnT * TraceT))
           (Q : Ensemble (ReturnT * TraceT')) :=
  { TraceT_map : TraceT -> TraceT';
     TraceT'_map : TraceT' -> TraceT;
     TraceT_map_inv : forall trace, TraceT'_map (TraceT_map trace) = trace;
     TraceT'_map_inv : forall trace, TraceT_map (TraceT'_map trace) = trace;
     TraceT_map_inj : forall trace trace', TraceT_map trace = TraceT_map trace'
                                           -> trace = trace';
     TraceT'_map_inj : forall trace trace', TraceT'_map trace = TraceT'_map trace'
                                           -> trace = trace';
     TraceT_map_valid : forall el, P el -> Q (fst el, TraceT_map (snd el));
     TraceT'_map_valid : forall el, Q el -> P (fst el, TraceT'_map (snd el))
  }.

Ltac destruct_pairs :=
  repeat match goal with
             H : prod _ _ |- _ => destruct H
         end.

Lemma Equivalent_Swap_In {ReturnT TraceT}
      qsSchema qs R R' (bod : Tuple -> Tuple -> Ensemble (ReturnT * TraceT))
:
  Equivalent_Trace_Ensembles
    (@UnConstrQuery_In qsSchema qs _ _ R (fun tup => @UnConstrQuery_In qsSchema qs _ _ R' (fun tup' => bod tup tup')))
    (@UnConstrQuery_In qsSchema qs _ _ R' (fun tup => @UnConstrQuery_In qsSchema qs _ _ R
                                             (fun tup' => bod tup' tup))).
Proof.
  econstructor 1 with (TraceT_map := fun el => (fst (snd el), (fst el, snd (snd el))))
                        (TraceT'_map := fun el => (fst (snd el), (fst el, snd (snd el))));
  simpl; intros; destruct_pairs; simpl in *; injections; auto;
  unfold UnConstrQuery_In in *; intuition.
Qed.

Lemma Equivalent_Swap_In_Where {ReturnT TraceT}
      qsSchema qs R {heading}
      (bod : @Tuple heading -> Tuple -> Ensemble (ReturnT * TraceT))
      (P : @Tuple heading -> Prop)
:
  forall tup',
    Equivalent_Trace_Ensembles
      (@UnConstrQuery_In qsSchema qs _ _ R
                  (fun tup => Query_Where (P tup') (bod tup' tup)))
      (Query_Where (P tup') (@UnConstrQuery_In qsSchema qs _ _ R (bod tup'))).
Proof.
  econstructor 1 with (TraceT_map := id)
                      (TraceT'_map := id);
  intros; destruct_pairs; unfold id in *; simpl in *; auto;
  unfold UnConstrQuery_In, Query_Where in *; intuition.
Qed.

Lemma Equivalent_Under_In {ReturnT TraceT TraceT'}
      qsSchema qs R
      (bod : Tuple -> Ensemble (ReturnT * TraceT))
      (bod' : Tuple -> Ensemble (ReturnT * TraceT'))
:
  (forall tup, Equivalent_Trace_Ensembles (bod tup) (bod' tup))
  -> Equivalent_Trace_Ensembles
      (@UnConstrQuery_In qsSchema qs _ _ R (fun tup => bod tup))
      (@UnConstrQuery_In qsSchema qs _ _ R (fun tup => bod' tup)).
Proof.
  intros H.
  econstructor 1 with
  (TraceT_map :=
     (fun el : Tuple * TraceT =>
        (fst el, (TraceT_map (Equivalent_Trace_Ensembles := H (fst el)))
          (snd el))))
  (TraceT'_map :=
     (fun el : Tuple * TraceT' =>
        (fst el, (TraceT'_map (Equivalent_Trace_Ensembles := H (fst el)))
          (snd el))));
  intros; destruct_pairs; unfold id in *; simpl in *; auto;
  unfold UnConstrQuery_In, Query_Where in *; intuition;
  simpl in *; eauto.
  - f_equal; apply (TraceT_map_inv t0).
  - f_equal; apply (TraceT'_map_inv t0).
  - injection H0; intros; subst; f_equal; eauto using TraceT_map_inj.
  - injection H0; intros; subst; f_equal; eauto using TraceT'_map_inj.
  - eapply (TraceT_map_valid (r, t0)); eauto.
  - eapply (TraceT'_map_valid (r, t0)); eauto.
Qed.

Class DecideableEnsemble {A} (P : Ensemble A) :=
  { dec : A -> bool;
    dec_decides_P : forall a, dec a = true <-> P a}.

Instance DecideableEnsemble_EqDec {A B : Type}
         (B_eq_dec : Query_eq B)
         (f f' : A -> B)
         : DecideableEnsemble (fun a => eq (f a) (f' a)) :=
  {| dec a := if A_eq_dec (f a) (f' a) then true else false |}.
Proof.
  intros; find_if_inside; split; congruence.
Defined.

Require Import Arith Omega.

Instance DecideableEnsemble_gt {A} (f f' : A -> nat)
  : DecideableEnsemble (fun a => f a > f' a) :=
  {| dec a := if le_lt_dec (f a) (f' a) then false else true |}.
Proof.
  intros; find_if_inside; intuition.
Defined.

Lemma refine_For_Equivalent_Trace_Ensembles
      {ReturnT TraceT TraceT' : Type} :
  forall bod bod',
    @Equivalent_Trace_Ensembles ReturnT TraceT TraceT' bod bod' ->
    refine (For bod)%QuerySpec
           (For bod')%QuerySpec.
Proof.
  intros; unfold Query_For, refine;
  intros; inversion_by computes_to_inv; subst; econstructor.
  {
    exists (map (fun el => (fst el, TraceT'_map (snd el))) x); intuition.
    rewrite map_map; f_equal.
    unfold EnsembleListEquivalence.EnsembleListEquivalence in *; intuition.
    clear H0; induction x; simpl; inversion H; subst; constructor; eauto.
    unfold not; intros; apply H2.
    destruct ((proj1 (in_map_iff _ _ _ )) H0); intuition; injections; subst.
    apply_in_hyp TraceT'_map_inj; destruct a; destruct x0; simpl in *; subst; eauto.
    rewrite <- (TraceT_map_inv b); eapply in_map_iff; eexists (_, _); split;
    simpl; try reflexivity.
    eapply H0; eapply (TraceT_map_valid (_, _)); eassumption.
    rewrite <- (TraceT_map_inv b).
    eapply (TraceT'_map_valid (_, _)).
    eapply H0.
    destruct ((proj1 (in_map_iff _ _ _ )) H1); intuition; injections; subst.
    destruct x0; rewrite <- (TraceT'_map_inv t) in H4; eauto.
  }
Qed.

Lemma refineEquiv_For_DropQSConstraints {ReturnT TraceT : Type}
      qsSchema qs :
  forall (bod : Ensemble (ReturnT * TraceT)),
      refine
     {H1 |
      exists or' : QueryStructure qsSchema * list ReturnT,
                   (queryRes <- (For bod)%QuerySpec;
                    ret (qs, queryRes)) ↝ or' /\
                   DropQSConstraints_AbsR (fst or') (fst H1) /\ snd or' = snd H1}
     (b <- (For bod)%QuerySpec;
      ret (DropQSConstraints qs, b) ) .
Proof.
  setoid_rewrite refineEquiv_pick_ex_computes_to_bind_and;
  intros; f_equiv; unfold pointwise_relation; intros.
  setoid_rewrite refineEquiv_pick_ex_computes_to_and;
  setoid_rewrite refineEquiv_bind_unit; simpl;
  unfold DropQSConstraints_AbsR;
  setoid_rewrite refineEquiv_pick_pair;
  setoid_rewrite refineEquiv_pick_eq';
  simplify with monad laws; f_equiv.
Qed.

Tactic Notation "drop" "constraints" "from" "query" constr(methname) :=
  hone method methname;
  [ setoid_rewrite refineEquiv_pick_ex_computes_to_and;
    simplify with monad laws;
    setoid_rewrite DropQSConstraintsQuery_In;
    repeat setoid_rewrite DropQSConstraintsQuery_In_UnderBinder;
    setoid_rewrite refineEquiv_pick_pair; simpl;
    setoid_rewrite refineEquiv_pick_eq';
    match goal with
        H : DropQSConstraints_AbsR _ _ |- _ =>
        unfold DropQSConstraints_AbsR in H; rewrite H
    end; simplify with monad laws;
    finish honing | ]. *)
