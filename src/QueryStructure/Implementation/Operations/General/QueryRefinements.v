Require Import
        Coq.Arith.Arith
        Coq.omega.Omega
        Coq.NArith.NArith
        Coq.ZArith.ZArith
        Coq.Strings.String
        Coq.Lists.List
        Coq.Sorting.Permutation
        Coq.Bool.Bool
        Coq.Sets.Ensembles
        Coq.Logic.FunctionalExtensionality
        Fiat.ADTNotation
        Fiat.Common
        Fiat.Common.ilist2
        Fiat.Common.List.ListFacts
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

Import Coq.Vectors.VectorDef.VectorNotations.
(* [Query_For] and all aggregates are opaque, so we need to make them
   transparent in order to reason about them. *)
Local Transparent Query_For Count Max MaxN MaxZ Sum SumN SumZ.

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

Lemma refine_For_rev {ResultT}
      (bod : Comp (list ResultT))
  : refine
      (Query_For bod)
      (res <- Query_For bod;
       ret (rev res)).
Proof.
  unfold Query_For; intros v Comp_v; computes_to_inv.
  subst; computes_to_econstructor; eauto.
  computes_to_econstructor.
  setoid_rewrite Comp_v'0.
  apply Permutation_rev.
Qed.

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
  unfold refine; intros; computes_to_inv; subst.
  computes_to_econstructor; eauto.
  rewrite app_length; computes_to_econstructor.
Qed.

Definition UnConstrQuery_In {ResultT}
           {qsSchema}
           (qs : UnConstrQueryStructure qsSchema)
           (R : Fin.t _)
           (bod : RawTuple -> Comp (list ResultT))
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
  computes_to_inv; econstructor; intuition.
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
           {n}
           {A : Type}
           {f : A -> Type}
           {As : Vector.t A n}
           {a : A}
           (l' : list (ilist2 (B := f) As))
           (c : ilist2 (B := f) As -> Comp (list (f a)))
: Comp (list (ilist2 (B := f) (Vector.cons _ a _ As))) :=
  flatten_CompList (map (fun l' => l <- c l'; ret (map (fun fa => icons2 fa l') l)) l').

Definition Build_single_Tuple_list
           {heading}
           (l : list (@RawTuple heading))
: list (ilist2 (B := @RawTuple) (Vector.cons _ heading _ (Vector.nil _)))
  := map (fun a => icons2 a (inil2)) l.

Lemma filter_and_join_ilist_tail
      {n}
      {A}
      {a}
      {As : Vector.t A n}
      (f' : A -> Type)
: forall
    (f : (ilist2 (B := f') As) -> bool)
    (s1 : list (ilist2 (B := f') As))
    (s2 : ilist2 (B := f') As -> Comp (list (f' a)))
    filter_rest,
    (forall a, List.In a s1 -> exists v, computes_to (s2 a) v)
    -> refineEquiv (l <- (Join_Comp_Lists s1 s2);
                    ret (filter (fun x : ilist2 (B := f') (Vector.cons _ a _ As) => f (ilist2_tl x) && filter_rest x) l))
                   (l <- Join_Comp_Lists (filter f s1) s2;
                    ret (filter filter_rest l)).
Proof.
  split; induction s1; unfold Join_Comp_Lists in *; simpl in *; intros; eauto.
  - simplify with monad laws; simpl; intros v Comp_v;
    computes_to_inv; subst; repeat econstructor.
  - simplify with monad laws; intros v.
    case_eq (f a0); simpl; intros a0_eq Comp_v.
    + computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHs1 (fun a In_a => H _ (or_intror In_a)) _ (BindComputes _ (fun x => ret (filter filter_rest x)) _ _ Comp_v'0 (ReturnComputes _))) ;  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      rewrite !filter_app, !filter_map, c'; simpl.
      rewrite a0_eq, filter_and, filter_true; eauto.
    + pose (IHs1 (fun a In_a => H _ (or_intror In_a)) _ Comp_v);  computes_to_inv; subst.
      destruct (H a0); eauto.
      repeat (computes_to_econstructor; eauto).
      rewrite filter_app, filter_map; simpl; intros;
      rewrite a0_eq, filter_false, c'; simpl; computes_to_econstructor.
  - intros v Comp_v;  computes_to_inv; subst; eauto.
  - intros v Comp_v;  computes_to_inv; subst.
    pose proof (IHs1 (fun a In_a => H _ (or_intror In_a)) _
                     (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
     computes_to_inv.
    case_eq (f a0); intros a0_eq; simpl.
    + repeat (computes_to_econstructor; eauto).
      rewrite !filter_app, !filter_map, H0', filter_and; simpl.
      rewrite a0_eq, filter_and, filter_true; eauto.
    + repeat (computes_to_econstructor; eauto).
      rewrite !filter_app, !filter_map, !filter_and, H0'; simpl.
      rewrite a0_eq, filter_false, <- filter_and; eauto.
Qed.

Definition List_Query_In
           {QueryT ResultT}
           (queriedList : list QueryT)
           (resultComp : QueryT -> Comp (list ResultT))
  :=
    flatten_CompList (map resultComp queriedList).

Corollary filter_join_ilist2_tail
          {n}
          {A}
          {a}
          {As : Vector.t A n}
          (f' : A -> Type)
: forall
    (f : (ilist2 (B := f') As) -> bool)
    (s1 : list (ilist2 (B := f') As))
    (s2 : ilist2 (B := f') As -> Comp (list (f' a))),
    (forall a, List.In a s1 -> exists v, computes_to (s2 a) v)
    -> refineEquiv (l <- (Join_Comp_Lists s1 s2);
                    ret (filter (fun x : ilist2 (B := f') (a :: As) => f (ilist2_tl x)) l))
                   (Join_Comp_Lists (filter f s1) s2).
Proof.
  intros; pose proof (filter_and_join_ilist_tail f s1 s2 (fun _ => true)).
  setoid_rewrite filter_and in H0; setoid_rewrite filter_true in H0.
  setoid_rewrite H0; eauto; setoid_rewrite refineEquiv_unit_bind; reflexivity.
Qed.


Lemma refine_Join_Comp_Lists_filter_tail
: forall {n} heading headings
         (f : ilist2 (n := n) (B := @RawTuple) headings -> bool)
         (filter_rest : ilist2 (B := @RawTuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : _ -> Comp (list ResultT))
         (l2 : ilist2 (B:= @RawTuple) headings
               -> Comp (list (@RawTuple heading))),
    (forall a : ilist2 (B := @RawTuple) headings,
     exists v : list (@RawTuple heading),
       refine (l2 a) (ret v))
    ->
    forall l1,
      refine
        (l' <- Join_Comp_Lists l1 l2;
         List_Query_In
           (filter (fun (a : ilist2 (B := @RawTuple) (heading :: headings))
                    => f (ilist2_tl a) && (filter_rest a)) l')
           resultComp)
        (l' <- Join_Comp_Lists (filter f l1) l2;
         List_Query_In (filter filter_rest l') resultComp).
Proof.
  intros; revert l2 H.
  unfold Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - setoid_rewrite refineEquiv_bind_unit; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    + computes_to_inv; subst; computes_to_econstructor; eauto.
      rewrite filter_app, filter_map in Comp_v'.
      unfold List_Query_In in Comp_v'.
      repeat rewrite map_app, map_map in Comp_v'.
      apply flatten_CompList_app_inv' in Comp_v'.
      destruct_ex; split_and.
      pose (IHl1 l2 H _ (BindComputes _ _ _ _ Comp_v'0 H3));  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
    + destruct (H a); eauto.
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHl1 l2 H _ (BindComputes _ _ _ _ Comp_v Comp_v'));  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_false; simpl; eauto.
Qed.

(* A version of [refine_Join_Comp_Lists_filter_tail] for the case that
      the realizeablity of [l2] depends on the elements of [l1]*)
Lemma refine_Join_Comp_Lists_filter_tail_cond
: forall n heading headings
         (f : ilist2 (n := n) (B := @RawTuple) (headings) -> bool)
         (filter_rest : ilist2 (B := @RawTuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : _ -> Comp (list ResultT))
         (l1 : list (ilist2 (B := @RawTuple) headings))
         (l2 : ilist2 (B := @RawTuple) headings
               -> Comp (list (@RawTuple heading))),
    (forall a : ilist2 (B := @RawTuple) headings,
       List.In a l1 -> exists v : list (@RawTuple heading),
                         refine (l2 a) (ret v))
    -> refine
         (l' <- Join_Comp_Lists l1 l2;
          List_Query_In
            (filter (fun (a : ilist2 (B := @RawTuple) (heading :: headings))
                     => f (ilist2_tl a) && (filter_rest a)) l')
            resultComp)
         (l' <- Join_Comp_Lists (filter f l1) l2;
          List_Query_In (filter filter_rest l') resultComp).
Proof.
  unfold Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - setoid_rewrite refineEquiv_bind_unit; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    + computes_to_inv; subst; computes_to_econstructor; eauto.
      rewrite filter_app, filter_map in Comp_v'.
      unfold List_Query_In in Comp_v'.
      rewrite map_app, map_map in Comp_v'.
      apply flatten_CompList_app_inv' in Comp_v'.
      destruct_ex; split_and.
      pose (IHl1 l2 (fun a In_a => H _ (or_intror In_a)) _ (BindComputes _ _ _ _ Comp_v'0 H3));  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
    + destruct (H a); eauto.
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHl1 l2 (fun a In_a => H _ (or_intror In_a)) _ (BindComputes _ _ _ _ Comp_v Comp_v'));  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_false; simpl; eauto.
Qed.

Definition Join_Filtered_Comp_Lists
           {n}
           {A : Type}
           {f : A -> Type}
           {As : Vector.t A n}
           {a : A}
           (l' : list (ilist2 (B := f) As))
           (c : ilist2 (B := f) As -> Comp (list (f a)))
           (cond : ilist2 (B := f) (a :: As) -> bool)
: Comp (list (ilist2 (B := f) (a :: As))) :=
  l <- Join_Comp_Lists l' c;
  ret (filter cond l).

Lemma Join_Filtered_Comp_Lists_id
      {n}
      {A : Type}
      {f : A -> Type}
      {As : Vector.t A n}
      {a : A}
: forall (l' : list (ilist2 (B := f) As))
         (c : ilist2 (B := f) As -> Comp (list (f a))),
    refine (Join_Comp_Lists l' c)
           (Join_Filtered_Comp_Lists l' c (fun _ => true)).
  unfold Join_Filtered_Comp_Lists; setoid_rewrite filter_true.
  intros; rewrite refineEquiv_unit_bind; reflexivity.
Qed.

Lemma refine_Join_Filtered_Comp_Lists_filter_tail_andb
: forall n heading headings
         (f g : ilist2 (n := S n) (B := @RawTuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : ilist2 (B := @RawTuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (cond : ilist2 (B := @RawTuple) (heading :: headings) -> bool),
  forall l1 : list (ilist2 (B := @RawTuple) headings),
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
: forall n heading headings
         (f : ilist2 (n := S n) (B := @RawTuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : ilist2 (B := @RawTuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (cond : ilist2 (B := @RawTuple) (heading :: headings) -> bool),
  forall l1 : list (ilist2 (B := @RawTuple) headings),
    refine
      (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
       List_Query_In (filter f l') resultComp)
      (l' <- Join_Filtered_Comp_Lists l1 l2 (fun a => cond a && f a);
       List_Query_In l' resultComp).
Proof.
  intros;
  pose proof (@refine_Join_Filtered_Comp_Lists_filter_tail_andb
                _ _ _ f (fun _ => true) _ resultComp l2 cond l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
   computes_to_inv; subst.
  rewrite filter_and, filter_true in Comp_v'.
  eauto.
Qed.

Lemma refine_Join_Filtered_Comp_Lists_filter_hd_andb
: forall n heading headings
         (f : ilist2 (n := n) (B := @RawTuple) headings -> bool)
         (g : ilist2 (B := @RawTuple) (heading :: headings) -> bool)
         (ResultT : Type)
         (resultComp : ilist2 (B := @RawTuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (cond : ilist2 (B := @RawTuple) (heading :: headings) -> bool),
    (forall a : ilist2 (B := @RawTuple) headings,
     exists v : list RawTuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist2 (B := @RawTuple) headings),
      refine
        (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
         List_Query_In
           (filter
              (fun a : ilist2 (B := @RawTuple) (heading :: headings) =>
                 (f (ilist2_tl a) && g a)) l') resultComp)
        (l' <- Join_Filtered_Comp_Lists (filter f l1) l2 cond;
         List_Query_In (filter g l') resultComp).
Proof.
  intros; revert l2 H.
  unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - repeat setoid_rewrite refineEquiv_bind_unit; simpl; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    +  computes_to_inv; subst; computes_to_econstructor; eauto.
      unfold List_Query_In in Comp_v'.
      rewrite !filter_app, !filter_map, !map_app, !map_map in Comp_v'.
      apply FlattenCompList.flatten_CompList_app_inv' in Comp_v'.
      destruct_ex; split_and.
      assert (computes_to (l' <- l <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist2 (B := @RawTuple) headings =>
                                    l <- l2 l';
                                  ret (map (fun fa : RawTuple => icons2 fa l') l))
                                 (filter f l1));
                           ret (filter cond l);
                           List_Query_In (filter g l') resultComp) x0)
        as H'
          by (setoid_rewrite <- filter_and in H3;
              repeat econstructor; eauto;
              setoid_rewrite <- filter_and; eauto).
      pose (IHl1 l2 H _ H');  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
    + destruct (H a); eauto.
       computes_to_inv; subst; computes_to_econstructor; eauto.
      assert (computes_to (l' <- l <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist2 (B := @RawTuple) headings =>
                                    l <- l2 l';
                                  ret (map (fun fa : RawTuple => icons2 fa l') l))
                                 (filter f l1));
                           ret (filter cond l);
                           List_Query_In (filter g l') resultComp) v)
        as H' by  (repeat econstructor; eauto).
      pose (IHl1 l2 H _ H');  computes_to_inv; subst.
      econstructor; eauto.
      unfold List_Query_In.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite a_eq, filter_false; simpl; eauto.
Qed.

Lemma refine_Join_Filtered_Comp_Lists_filter_hd
: forall n heading headings
         (f : ilist2 (n := n) (B := @RawTuple) headings -> bool)
         (ResultT : Type)
         (resultComp : ilist2 (B := @RawTuple) (heading :: headings) ->
                       Comp (list ResultT))
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (cond : ilist2 (B := @RawTuple) (heading :: headings) -> bool),
    (forall a : ilist2 (B := @RawTuple) headings,
     exists v : list RawTuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist2 (B := @RawTuple) headings),
      refine
        (l' <- Join_Filtered_Comp_Lists l1 l2 cond;
         List_Query_In
           (filter
              (fun a : ilist2 (B := @RawTuple) (heading :: headings) =>
                 f (ilist2_tl a)) l') resultComp)
        (l' <- Join_Filtered_Comp_Lists (filter f l1) l2 cond;
         List_Query_In l' resultComp).
Proof.
  intros; pose proof (@refine_Join_Filtered_Comp_Lists_filter_hd_andb
                        _ _ _ f (fun _ => true) _ resultComp l2 cond H l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
   computes_to_inv; subst.
  rewrite filter_and, filter_true in Comp_v'.
  eauto.
Qed.

Lemma Join_Filtered_Comp_Lists_ExtensionalEq_filters
      {n}
      {A : Type}
      {f : A -> Type}
      {As : Vector.t A n}
      {a : A}
: forall (l' : list (ilist2 (B := f) As))
         (c : ilist2 (B := f) As -> Comp (list (f a)))
         (g g' : ilist2 (B := f) (a :: As) -> bool),
    ExtensionalEq g g'
    -> refine (Join_Filtered_Comp_Lists l' c g)
              (Join_Filtered_Comp_Lists l' c g').
Proof.
  unfold Join_Filtered_Comp_Lists; intros.
  f_equiv; intro.
  f_equiv; apply filter_by_equiv; eauto.
Qed.


Lemma refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb
: forall n heading1 heading2 headings
         (f g : ilist2 (n := S n) (B := @RawTuple) (heading1 :: headings) -> bool)
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (l2' : ilist2 (B := @RawTuple) (heading1 :: headings) -> Comp (list RawTuple))
         (cond1 : ilist2 (B := @RawTuple) (heading1 :: headings) -> bool)
         (cond2 : ilist2 (B := @RawTuple) (heading2 :: heading1 :: headings) -> bool),
  forall l1 : list (ilist2 (B := @RawTuple) headings),
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
: forall n heading1 heading2 headings
         (f : ilist2 (n := S n) (B := @RawTuple) (heading1 :: headings) -> bool)
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (l2' : ilist2 (B := @RawTuple) (heading1 :: headings) -> Comp (list RawTuple))
         (cond1 : ilist2 (B := @RawTuple) (heading1 :: headings) -> bool)
         (cond2 : ilist2 (B := @RawTuple) (heading2 :: heading1 :: headings) -> bool),
  forall l1 : list (ilist2 (B := @RawTuple) headings),
    refine
      (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
       Join_Filtered_Comp_Lists (filter f l) l2' cond2)
      (l <- Join_Filtered_Comp_Lists l1 l2 (fun a => cond1 a && f a);
       Join_Filtered_Comp_Lists l l2' cond2).
Proof.
  intros;
  pose proof (@refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb
                _ _ _ _ f (fun _ => true) l2 l2' cond1 cond2 l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
   computes_to_inv; subst.
  rewrite filter_and, filter_true in Comp_v'.
  eauto.
Qed.

Lemma refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb
: forall n heading1 heading2 headings
         (f : ilist2 (n := n) (B := @RawTuple) headings -> bool)
         (g : ilist2 (B := @RawTuple) (heading1 :: headings) -> bool)
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (l2' : ilist2 (B := @RawTuple) (heading1 :: headings) -> Comp (list RawTuple))
         (cond1 : ilist2 (B := @RawTuple) (heading1 :: headings) -> bool)
         (cond2 : ilist2 (B := @RawTuple) (heading2 :: heading1 :: headings) -> bool),
    (forall a : ilist2 (B := @RawTuple) headings,
     exists v : list RawTuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist2 (B := @RawTuple) headings),
      refine
        (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
         Join_Filtered_Comp_Lists  (filter (fun a : ilist2 (B := @RawTuple) (_ :: _) => f (ilist2_tl a) && g a) l) l2' cond2)
        (l <- Join_Filtered_Comp_Lists (filter f l1) l2 cond1;
         Join_Filtered_Comp_Lists (filter g l) l2' cond2).
Proof.
  intros; revert l2 l2' cond1 cond2 H.
  unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; induction l1; simpl;
  intros; simplify with monad laws.
  - repeat setoid_rewrite refineEquiv_bind_unit; simpl; reflexivity.
  - case_eq (f a); simpl; intros a_eq v Comp_v.
    +  computes_to_inv; subst; computes_to_econstructor; eauto.
      rewrite !filter_app, !filter_map, !map_app, !map_map in Comp_v'.
      apply FlattenCompList.flatten_CompList_app_inv' in Comp_v'.
      destruct_ex; split_and; subst.
      assert (computes_to (l <- l <- FlattenCompList.flatten_CompList
                             (map
                                (fun l' : ilist2 (B := @RawTuple) headings =>
                                   l <- l2 l';
                                 ret (map (fun fa : RawTuple => icons2 fa l') l))
                                (filter f l1));
                           ret (filter cond1 l);
                           l0 <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist2 (B := @RawTuple) (heading1 :: headings) =>
                                    l0 <- l2' l';
                                  ret (map (fun fa : RawTuple => icons2 fa l') l0))
                                 (filter g l));
                           ret (filter cond2 l0)) (filter cond2 x0)) as H'
          by (repeat computes_to_econstructor; eauto).
      pose (IHl1 l2 l2' cond1 cond2 H _ H');  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      computes_to_econstructor.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite filter_and, a_eq, filter_true.
      eapply FlattenCompList.flatten_CompList_app; eauto.
      rewrite !filter_app, <- c''; eauto.
    + destruct (H a); eauto.
       computes_to_inv; subst; computes_to_econstructor; eauto.
      assert (computes_to (l <- l <- FlattenCompList.flatten_CompList
                             (map
                                (fun l' : ilist2 (B := @RawTuple) headings =>
                                   l <- l2 l';
                                 ret (map (fun fa : RawTuple => icons2 fa l') l))
                                (filter f l1));
                           ret (filter cond1 l);
                           l0 <- FlattenCompList.flatten_CompList
                              (map
                                 (fun l' : ilist2 (B := @RawTuple) (heading1 :: headings) =>
                                    l0 <- l2' l';
                                  ret (map (fun fa : RawTuple => icons2 fa l') l0))
                                 (filter g l));
                           ret (filter cond2 l0)) (filter cond2 v1)) as H'
          by (repeat econstructor; eauto).
      pose (IHl1 l2 l2' cond1 cond2 H _ H');  computes_to_inv; subst.
      computes_to_econstructor; eauto.
      computes_to_econstructor.
      repeat rewrite filter_app, filter_map.
      repeat rewrite map_app, map_map; simpl.
      rewrite a_eq, filter_false; simpl; eauto.
      rewrite <- c''; eauto.
Qed.


Lemma refine_Join_Join_Filtered_Comp_Lists_filter_hd
: forall n heading1 heading2 headings
         (f : ilist2 (n := n) (B := @RawTuple) headings -> bool)
         (l2 : ilist2 (B := @RawTuple) headings -> Comp (list RawTuple))
         (l2' : ilist2 (B := @RawTuple) (heading1 :: headings) -> Comp (list RawTuple))
         (cond1 : ilist2 (B := @RawTuple) (heading1 :: headings) -> bool)
         (cond2 : ilist2 (B := @RawTuple) (heading2 :: heading1 :: headings) -> bool),
    (forall a : ilist2 (B := @RawTuple) headings,
     exists v : list RawTuple, refine (l2 a) (ret v)) ->
    forall l1 : list (ilist2 (B := @RawTuple) headings),
      refine
        (l <- Join_Filtered_Comp_Lists l1 l2 cond1;
         Join_Filtered_Comp_Lists  (filter (fun a : ilist2 (B := @RawTuple) (_ :: _) => f (ilist2_tl a)) l) l2' cond2)
        (l <- Join_Filtered_Comp_Lists (filter f l1) l2 cond1;
         Join_Filtered_Comp_Lists l l2' cond2).
Proof.
  intros; pose proof (@refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb
                        _ _ _ _ f (fun _ => true) l2 l2' cond1 cond2 H l1) as r.
  setoid_rewrite filter_true in r.
  intros v Comp_v.
  apply r in Comp_v.
   computes_to_inv; subst.
  rewrite filter_and, filter_true in Comp_v'.
  eauto.
Qed.


Lemma List_Query_In_Return
      {n}
      {ResultT}
      headings
      (l : list (ilist2 (n := n) (B := @RawTuple) headings))
      (r : ilist2 (B := @RawTuple) headings -> ResultT)
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
   computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  apply H; apply H1; auto.
  apply H2; apply H; auto.
Qed.

Add Parametric Morphism {A: Type}
    qsSchema qs R
:
  (fun bod => Query_For (@UnConstrQuery_In qsSchema qs _ R bod))
    with signature ((pointwise_relation RawTuple (@Equivalent_Ensembles A) ==> refine ))
      as refine_Query_For_In_Equivalent.
Proof.
  unfold impl, Query_For, pointwise_relation, UnConstrQuery_In, In, refine.
  intros;  computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  destruct (H1 _ H0); eexists; intuition; eauto.
  apply H; auto.
  destruct_ex; apply H2; eexists; intuition; eauto.
  apply H; auto.
Qed. *)

Lemma DropQSConstraintsQuery_In {A} :
  forall qs_schema qs R bod,
    refine (@Query_In A qs_schema qs R bod)
           (UnConstrQuery_In (DropQSConstraints qs) R bod).
Proof.
  intros; unfold Query_In, UnConstrQuery_In, GetRelation, GetUnConstrRelation,
          DropQSConstraints; rewrite <- ith_imap2.
  reflexivity.
Qed.

Lemma DropQSConstraintsQuery_In_UnderBinder {A B} :
  forall qs_schema qs R bod,
    (fun b : B => @Query_In A qs_schema qs R (bod b)) =
    (fun b : B => UnConstrQuery_In (DropQSConstraints qs) R (bod b)).
Proof.
    intros; unfold Query_In, UnConstrQuery_In, GetRelation, GetUnConstrRelation,
          DropQSConstraints; rewrite <- ith_imap2.
  reflexivity.
Qed.

(*Lemma Equivalent_Swap_In {ResultT}
      qsSchema qs R (bod : RawTuple -> Comp (list ResultT))
      enumR
      (enumerableR : EnsembleListEquivalence (GetUnConstrRelation qs R) enumR)
:
  refine
    (@UnConstrQuery_In qsSchema qs _ R (fun tup => @UnConstrQuery_In qsSchema qs _ R' (bod tup)))


Lemma Equivalent_Swap_In {ResultT}
      qsSchema qs R R' (bod : RawTuple -> RawTuple -> Comp (list ResultT))
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
  unfold refine; intros;  computes_to_inv; subst.
  econstructor.
  econstructor; eauto.
  econstructor 2 with (comp_a_value := x0).
  assert (forall a : RawTuple,
            (queryBod <- {queryBod : RawTuple -> list ResultT |
                    forall a0 : RawTuple, bod a0 a ↝ queryBod a0};
             {resultList : list ResultT |
              Permutation.Permutation resultList
                                      (flatten (map queryBod enumR))}) ↝ x0 a).
  { intros; generalize (H1 a); intros;  computes_to_inv.
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
   computes_to_inv; subst.

  induction x; simpl; subst.
  constructor 2 with (comp_a_value := []).
  econstructor.

  Focus 2.
  constructor.
[ | econstructor].
  F

  repeat (progress (destruct_ex; intuition)).
  induction x; simpl in *; subst.
  exists (@nil (@RawTuple (schemaHeading
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
      (bod : @RawTuple heading -> RawTuple -> Ensemble A)
      (P : @RawTuple heading -> Prop)
:
  pointwise_relation
    RawTuple Equivalent_Ensembles
    (fun tup' : RawTuple =>
       (@UnConstrQuery_In qsSchema qs _ R
                  (fun tup => Query_Where (P tup') (bod tup' tup))))
    (fun tup' : RawTuple =>
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
   computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  apply H; apply H1; auto.
  apply H2; apply H; auto.
Qed.

Add Parametric Morphism {A: Type}
    qsSchema qs R
:
  (fun bod => Query_For (@UnConstrQuery_In qsSchema qs _ R bod))
    with signature ((pointwise_relation RawTuple (@Equivalent_Ensembles A) ==> refine ))
      as refine_Query_For_In_Equivalent.
Proof.
  unfold impl, Query_For, pointwise_relation, UnConstrQuery_In, In, refine.
  intros;  computes_to_inv.
  econstructor; split_iff; split; intros; eauto.
  destruct (H1 _ H0); eexists; intuition; eauto.
  apply H; auto.
  destruct_ex; apply H2; eexists; intuition; eauto.
  apply H; auto.
Qed. *)

Lemma refine_Count_if {A} :
  forall (b : bool) (t : A),
    refine (Count (if b then (Return t)%QuerySpec else ret nil))
           (ret (if b then 1 else 0)).
Proof.
  intros; rewrite refine_Count.
  destruct b; simplify with monad laws; reflexivity.
Qed.

Add Parametric Morphism
    (n : nat)
    (A : Type)
    (f : A -> Type)
    (As : Vector.t A n)
    (a : A)
    (l' : list (ilist2 (B := f) As))
: (@Join_Comp_Lists _ A f As a l')
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
              (ret nil)).
Proof.
  unfold refine, Query_Where; intros.
  caseEq (dec a); rewrite H0 in H; computes_to_econstructor;
  split; intros; eauto.
  apply dec_decides_P in H0; intuition.
  apply Decides_false in H0; intuition.
   computes_to_inv; eauto.
Qed.

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
       {P : Ensemble (@RawTuple heading)}
       {P_dec : DecideableEnsemble P}
: DecideableEnsemble (fun x : IndexedRawTuple => P (indexedRawTuple x)) :=
  {| dec itup := @dec _ _ P_dec (indexedRawTuple itup)|}.
Proof.
  intuition; eapply dec_decides_P; simpl in *; eauto.
Defined.
