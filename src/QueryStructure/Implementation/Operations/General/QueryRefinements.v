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

Import Vectors.VectorDef.VectorNotations.
Import Lists.List.ListNotations.
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

Add Parametric Morphism heading ResultT P
  : (@QueryResultComp heading ResultT P)
    with signature (pointwise_relation _ refine ==> refine)
      as refine_refine_QueryResultComp.
Proof.
  intros.
  unfold QueryResultComp; intros.
  f_equiv.
  unfold pointwise_relation in *; intros.
  induction a; simpl; f_equiv; eauto.
  unfold pointwise_relation.
  intros; setoid_rewrite IHa; f_equiv.
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
  - setoid_rewrite IHl; unfold Query_Return; simplify with monad laws.
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


Lemma refine_In_Where_Intersection heading
  : forall R P (P_dec : DecideableEnsemble P),
    refine
      (QueryResultComp (Intersection (@IndexedRawTuple heading) R
                                     (fun r => (P (indexedElement r)))) (fun r => Query_Return r))
      (QueryResultComp R (fun r => Query_Where (P r)
                                               (Query_Return r))).
Proof.
  unfold refine, In, QueryResultComp; intros * ? x H.
  repeat computes_to_inv.
  revert R x H H'.
  induction v; simpl in *; intros; computes_to_inv; subst.
  - repeat computes_to_econstructor.
    instantiate (1 := @nil RawTuple); simpl.
    inversion H; intuition; subst.
    econstructor; split; eauto.
    repeat split; intros; eauto.
    eapply H0; inversion H2; subst; eauto.
    eapply H0; eauto.
    eapply in_map with (f := indexedElement) in H2; rewrite H1 in H2; destruct H2.
    computes_to_econstructor.
  - inversion H; destruct x; simpl in *; intuition;
    try discriminate; injections.
    assert (UnIndexedEnsembleListEquivalence
              (fun t : IndexedRawTuple => elementIndex t <> elementIndex i
                                          /\ R t) (map indexedElement x)).
    { econstructor; intuition eauto.
      inversion H1; subst.
      apply H0 in H4; intuition.
      subst; intuition eauto.
      econstructor; intros; subst.
      inversion H3; subst.
      apply H6; eapply in_map_iff.
      eexists; split; eauto.
      eapply H0; eauto.
      inversion H3; subst; eauto.
    }
    pose proof (IHv _ _ H1 H''); clear IHv; computes_to_inv.
    inversion H'; subst.
    refine pick val (List.app v0 v).
    econstructor; intuition; eauto.
    rewrite map_app; eapply FlattenCompList.flatten_CompList_app; eauto.
    case_eq (dec (indexedElement i)); intros.
    apply dec_decides_P in H6; apply H4 in H6; inversion H6; subst.
    repeat computes_to_econstructor.
    eapply Decides_false in H6; apply H5 in H6; subst; simpl;
    computes_to_econstructor.
    inversion H2; subst; intuition.
    case_eq (dec (indexedElement i)); intros.
    + apply dec_decides_P in H8; pose proof (H4 H8) as H'''; inversion H'''; subst.
      econstructor 1.
      instantiate (1 := List.app [i] x0); simpl; intuition eauto.
      inversion H4; subst; apply H0 in H10; intuition.
      right; eapply H6; econstructor; unfold In; eauto.
      split; eauto; intros; subst.
      inversion H3; subst; intuition eauto.
      apply H15; eapply in_map_iff.
      eexists; eauto.
      eapply H0; eauto.
      subst.
      econstructor.
      eapply H0; eauto.
      unfold In; eauto.
      econstructor; unfold In in *; eauto.
      eapply H0; eauto.
      rewrite <- H6 in H10; inversion H10; subst; unfold In in *; intuition.
      eapply H0 in H13; eauto.
      rewrite <- H6 in H10; inversion H10; subst; unfold In in *; intuition.
      inversion H3; subst; econstructor; eauto.
      intro; rewrite in_map_iff in H4; destruct_ex; intuition eauto.
      apply H11; rewrite in_map_iff; destruct_ex; intuition eauto.
      eexists; intuition eauto.
      eapply H6 in H13; inversion H13; subst.
      unfold In in H13.
      inversion H13; subst.
      inversion H15; subst; intuition.
    + eapply Decides_false in H8; pose proof (H5 H8); subst; simpl.
      inversion H2; subst; intuition.
      econstructor 1.
      instantiate (1 := x1); intuition eauto.
      eapply H7.
      repeat econstructor; eauto.
      destruct H5; subst.
      apply H0 in H5; intuition.
      subst; intuition.
      inversion H3; subst.
      apply H17; apply in_map_iff; eexists; eauto.
      destruct H5; eauto.
      destruct H5; eauto.
      eapply H7 in H5; destruct H5; destruct H5.
      econstructor; eauto.
Qed.

Lemma refine_Where_Intersection heading {ResultT}
  : forall R P (P_dec : DecideableEnsemble P) (bod : _ -> Comp (list ResultT)),
    FiniteEnsemble R
    -> refine
         (QueryResultComp (heading := heading) R (fun r => Query_Where (P r) (bod r)))
         (QueryResultComp (IndexedEnsemble_Intersection R P) bod)
.
Proof.
  unfold refine, In, QueryResultComp; intros * ? ? Fin_R v Comp_v.
  repeat computes_to_inv.
  destruct Fin_R as [? Fin_R].
  pose proof (UnIndexedEnsembleListEquivalence_filter P_dec Fin_R).
  pose proof (Permutation_UnIndexedEnsembleListEquivalence' H Comp_v).
  eapply PermutationFacts.permutation_filter in H0; destruct_ex;
  intuition subst.
  refine pick val x0; eauto using Permutation_UnIndexedEnsembleListEquivalence.
  repeat computes_to_econstructor; eauto.
  revert v Comp_v'; clear; induction x0; simpl; intros; eauto.
  case_eq (dec a); simpl in *; intro H; rewrite H in *;
  simpl in Comp_v'; computes_to_inv.
  - computes_to_inv; subst; repeat computes_to_econstructor.
    apply dec_decides_P in H; split; intros; intuition.
    eapply IHx0; eauto.
  - computes_to_inv; subst; repeat computes_to_econstructor.
    apply Decides_false in H; split; intros; intuition.
    eauto.
    simpl; computes_to_econstructor.
Qed.

Lemma refine_Where_Intersection' heading {ResultT}
        : forall R,
          FiniteEnsemble R
          -> forall P (bod : _ -> Comp (list ResultT)),
            (P \/ ~ P)
            -> refine
                 (QueryResultComp (heading := heading) R (fun r => Query_Where P (bod r)))
                 (Query_Where P (QueryResultComp R bod))
.
Proof.
  unfold refine, In, Query_Where, QueryResultComp; intros ? Fin_R ? ? ? v Comp_v.
  intuition; computes_to_inv; intuition.
  - computes_to_inv; refine pick val _; eauto.
    repeat computes_to_econstructor.
    eapply refine_flatten_CompList_func; eauto.
    intros * ? ? ?; computes_to_econstructor.
    computes_to_inv; intuition.
  - subst.
    destruct Fin_R as [? Fin_R].
    computes_to_econstructor; eauto.
    eapply refine_flatten_CompList_func.
    intros * ? ? ?; computes_to_econstructor ; intuition.
    revert H1.
    instantiate (1 := fun _ => ret nil); simpl; intros; computes_to_inv;
    subst; eauto.
    clear; induction x; simpl; repeat computes_to_econstructor; eauto.
Qed.

Lemma refine_Where' {A B} :
  forall (P : Ensemble A)
         (P_dec : DecideableEnsemble P)
         (bod : Comp (list B)),
  forall a,
    refine
      (if (dec a) then
         bod
       else
         (ret nil))
      (Where (P a) bod)%QuerySpec.
Proof.
  unfold refine, Query_Where; intros.
  computes_to_inv; intuition.
  caseEq (dec a).
  apply dec_decides_P in H; eauto.
  rewrite H1; eauto.
  unfold not; intros H'; apply dec_decides_P in H'; congruence.
Qed.


Lemma refine_Intersection_Where heading {ResultT}
  : forall R P (P_dec : DecideableEnsemble P)
           (bod : _ -> Comp (list ResultT)),
    refine
      (QueryResultComp (IndexedEnsemble_Intersection R P) bod)
      (QueryResultComp (heading := heading) R (fun r => Query_Where (P r) (bod r))).
Proof.
  unfold refine, In, QueryResultComp; intros * ? ? v Comp_v.
  repeat computes_to_inv.
  refine pick val _;
    eauto using UnIndexedEnsembleListEquivalence_filter.
  repeat computes_to_econstructor.
  revert v Comp_v'; clear; induction v0; intros; simpl in *; eauto.
  computes_to_inv; subst.
  apply (refine_Where' P_dec) in Comp_v'.
  find_if_inside; simpl.
  computes_to_econstructor; eauto.
  computes_to_inv; subst; simpl; eauto.
Qed.

Lemma refine_IndexedEnsemble_Intersection_Intersection heading
  : forall P Q R,
    refine {queriedList : list (@RawTuple heading) |
            UnIndexedEnsembleListEquivalence
              (IndexedEnsemble_Intersection
                 (IndexedEnsemble_Intersection
                    P Q) R)
           queriedList}
              {queriedList : list (@RawTuple heading) |
               UnIndexedEnsembleListEquivalence
                 (IndexedEnsemble_Intersection
                    P (fun tup => Q tup /\ R tup))
              queriedList}.
Proof.
  intros.
  eapply refineEquiv_iff_Pick; unfold pointwise_relation; intuition;
  eapply UnIndexedEnsembleListEquivalence_Same_set; eauto using IndexedEnsemble_Intersection_And.
  unfold Same_set, Included, In, IndexedEnsemble_Intersection; intuition eauto.
Qed.

Lemma refine_QueryResultComp_Intersection_Intersection heading {ResultT}
  : forall P Q R k,
    refine (@QueryResultComp heading ResultT
           (IndexedEnsemble_Intersection
              (IndexedEnsemble_Intersection
                 P Q)R) k)
           (QueryResultComp
              (IndexedEnsemble_Intersection
                 P (fun tup => Q tup /\ R tup))
              k).
Proof.
  intros; unfold QueryResultComp; rewrite refine_IndexedEnsemble_Intersection_Intersection; reflexivity.
Qed.

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

Lemma flatten_CompList_Return {A}
  : forall (l : list A),
    refine (FlattenCompList.flatten_CompList (map Query_Return l))
           (ret l).
Proof.
  induction l; simpl; eauto; f_equiv.
  setoid_rewrite IHl; unfold Query_Return; simplify with monad laws; reflexivity.
Qed.

Definition FiniteTables_AbsR
           {qs_schema}
           (r_o r_n : UnConstrQueryStructure qs_schema) :=
  r_o = r_n /\ forall idx, (FiniteEnsemble (GetUnConstrRelation r_o idx)).


Lemma GetRel_FiniteTableAbsR:
  forall (qsSchema : QueryStructureSchema) (qs qs' : UnConstrQueryStructure qsSchema)
         (Ridx : Fin.t (numRawQSschemaSchemas qsSchema)),
    FiniteTables_AbsR qs qs'
    -> GetUnConstrRelation qs Ridx = GetUnConstrRelation qs' Ridx.
Proof.
  unfold FiniteTables_AbsR; intros; intuition; subst; eauto.
Qed.

Lemma FiniteTable_FiniteTableAbsR
      {qsSchema}
  : forall (qs qs' : UnConstrQueryStructure qsSchema)
           (idx : Fin.t (numRawQSschemaSchemas qsSchema)),
    FiniteTables_AbsR qs qs'
    -> FiniteEnsemble (GetUnConstrRelation qs idx).
Proof.
  unfold FiniteTables_AbsR; intros; intuition; subst; eauto.
Qed.

Lemma FiniteTable_FiniteTableAbsR'
      {qsSchema}
  : forall (qs qs' : UnConstrQueryStructure qsSchema)
           (idx : Fin.t (numRawQSschemaSchemas qsSchema)),
    FiniteTables_AbsR qs qs'
    -> FiniteEnsemble (GetUnConstrRelation qs' idx).
Proof.
  unfold FiniteTables_AbsR; intros; intuition; subst; eauto.
Qed.

Lemma FiniteTables_AbsR_symmetry {qs_schema} :
  forall (r_o r_n : UnConstrQueryStructure qs_schema),
    FiniteTables_AbsR r_o r_n
    -> FiniteTables_AbsR r_n r_o.
Proof.
  unfold FiniteTables_AbsR; intuition subst; eauto.
Qed.

Lemma FiniteTables_AbsR_Insert
      {qs_schema}
  : forall r_o r_n idx tup,
    FiniteTables_AbsR r_o r_n
    -> UnConstrFreshIdx (ith2 r_o idx) (elementIndex tup)
    -> refine {r_n0 : UnConstrQueryStructure qs_schema |
               FiniteTables_AbsR
                 (UpdateUnConstrRelation
                    r_o idx
                    (EnsembleInsert tup
                                    (GetUnConstrRelation r_o idx))) r_n0}
              (ret (UpdateUnConstrRelation
                      r_n idx
                      (EnsembleInsert tup
                                      (GetUnConstrRelation r_n idx)))).
Proof.
  intros; refine pick val _; try split; eauto.
  - destruct H; subst; reflexivity.
  - destruct H; intros idx'; destruct (fin_eq_dec idx idx'); subst;
    unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite ith_replace2_Index_eq.
      destruct (H1 idx') as [l ?]; eexists (cons (indexedElement tup) l).
      eauto using UnIndexedEnsembleListEquivalence_Insert.
    + rewrite ith_replace2_Index_neq; eauto.
Qed.




Lemma FiniteTables_AbsR_Delete
      {qs_schema}
  : forall r_o r_n idx P (P_dec : DecideableEnsemble P),
    FiniteTables_AbsR r_o r_n
    -> refine {r_n0 : UnConstrQueryStructure qs_schema |
               FiniteTables_AbsR
                 (UpdateUnConstrRelation
                    r_o idx
                    (EnsembleDelete (GetUnConstrRelation r_o idx) P)) r_n0}
              (ret (UpdateUnConstrRelation
                      r_n idx
                      (EnsembleDelete (GetUnConstrRelation r_n idx) P))).
Proof.
  intros; refine pick val _; try split; eauto.
  - destruct H; subst; reflexivity.
  - destruct H; intros idx'; destruct (fin_eq_dec idx idx'); subst;
    unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite ith_replace2_Index_eq.
      destruct (H0 idx') as [? ?].
      eexists.
      eauto using UnIndexedEnsembleListEquivalence_Delete.
    + rewrite ith_replace2_Index_neq; eauto.
Qed.

Require Import Fiat.QueryStructure.Specification.Operations.Empty.
Lemma FiniteEnsemble_QSEmptySpec {qs_schema}
  : forall idx,
    FiniteEnsemble
      (GetUnConstrRelation
         (DropQSConstraints (QSEmptySpec qs_schema)) idx).
Proof.
  unfold QSEmptySpec, DropQSConstraints, GetUnConstrRelation.
  setoid_rewrite <- ith_imap2.
  unfold rawRels; intros; rewrite @Build_EmptyRelation_IsEmpty.
  simpl; eexists nil.
  eauto using UnIndexedEnsembleListEquivalence_Empty_set.
Qed.

Lemma FiniteTables_AbsR_QSEmptySpec
      {qs_schema}
  :  FiniteTables_AbsR
       (DropQSConstraints (QSEmptySpec qs_schema))
       (DropQSConstraints (QSEmptySpec qs_schema)).
Proof.
  unfold FiniteTables_AbsR; intuition.
  eapply FiniteEnsemble_QSEmptySpec.
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
  destruct b; unfold Query_Return; simplify with monad laws; reflexivity.
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

  Lemma refine_Query_Where_Cond :
    forall (ResultT : Type) (P Q : Prop)
           (body : Comp (list ResultT)),
      (P <-> Q)
      -> refine (Query_Where P body)
                (Query_Where Q body).
  Proof.
    unfold pointwise_relation, Query_Where; intros.
    intros ? ?; intuition; computes_to_inv; computes_to_econstructor.
    intuition; intros.
  Qed.

  Lemma refine_Query_Where_True_Cond :
    forall (ResultT : Type) (P : Prop )
           (body : Comp (list ResultT)),
      P
      -> refine (Query_Where P body) body.
  Proof.
    intros.
    etransitivity; intro.
    apply refine_Query_Where_Cond with (Q := True).
    intuition; intros.
    intros; computes_to_econstructor; intuition.
  Qed.

  Lemma refine_Query_Where_False_Cond :
    forall (ResultT : Type) (P : Prop )
           (body : Comp (list ResultT)),
      ~ P
      -> refine (Query_Where P body) (ret nil).
  Proof.
    intros.
    etransitivity; intro.
    apply refine_Query_Where_Cond with (Q := False).
    intuition; intros.
    intros; computes_to_econstructor; intuition;
      computes_to_inv; eauto.
  Qed.

  Lemma refine_QueryResultComp_body_Where_False
        {ResultT : Type}
        {heading}
        (body : @RawTuple heading -> Comp (list ResultT))
        P R
    :
      (forall tup, In _ R tup -> ~ P (indexedElement tup))
      -> FiniteEnsemble R
      -> refine (QueryResultComp R (fun tup => Query_Where (P tup) (body tup)))
                (ret nil).
  Proof.
    intros; unfold QueryResultComp.
    destruct H0.
    refine pick val _; eauto.
    simplify with monad laws.
    rewrite refine_flatten_CompList_func' with (f' := fun _ => ret nil).
    apply flatten_CompList_nil'.
    intros; computes_to_econstructor; computes_to_inv; subst;
      intuition.
    unfold UnIndexedEnsembleListEquivalence in H0; destruct_ex;
      intuition; subst.
    apply in_map_iff in H1; destruct_ex; intuition; subst.
    apply H in H2; intuition.
    apply H0; eauto.
  Qed.


  Lemma Query_Where_And_Sym {ResultT}
    : forall (P Q : Prop)
             (body : Comp (list ResultT)),
      refine (Query_Where (P /\ Q) body)
             (Query_Where (Q /\ P) body).
  Proof.
    intros; rewrite refine_Query_Where_Cond;
      try reflexivity; intuition.
  Qed.

  Lemma flatten_CompList_Prop {A}
    : forall (P : Ensemble A) (P_dec : DecideableEnsemble P) (As As' : list A),
      FlattenCompList.flatten_CompList (map (fun a : A => Query_Where (P a)
                                                                      (Query_Return a) ) As) ↝ As'
      -> forall a, List.In a As' -> P a.
  Proof.
    induction As; simpl; intros; computes_to_inv; subst; simpl in *; intuition.
    unfold Query_Where, Query_Return in H; computes_to_inv; intuition.
    destruct (dec a) eqn: ?.
    - rewrite dec_decides_P in Heqb.
      pose proof (H1 Heqb); computes_to_inv;
        subst; simpl in *; subst; intuition eauto.
      subst; eauto.
    - apply Decides_false in Heqb; apply H2 in Heqb; subst; simpl in *;
        eauto.
  Qed.

  Lemma flatten_CompList_Subset {A}
    : forall (P : Ensemble A) (P_dec : DecideableEnsemble P) (As As' : list A),
      FlattenCompList.flatten_CompList (map (fun a : A => Query_Where (P a)
                                                                      (Query_Return a) ) As) ↝ As'
      -> forall a, List.In a As' -> List.In a As.
  Proof.
    induction As; simpl; intros; computes_to_inv; subst; simpl in *; intuition.
    unfold Query_Where, Query_Return in H; computes_to_inv; intuition.
    destruct (dec a) eqn: ?.
    - rewrite dec_decides_P in Heqb.
      pose proof (H1 Heqb); computes_to_inv;
        subst; simpl in *; subst; intuition eauto.
    - apply Decides_false in Heqb; apply H2 in Heqb; subst; simpl in *;
        eauto.
  Qed.

  Lemma flatten_CompList_nil {A}
    : forall (P : Ensemble A) (P_dec : DecideableEnsemble P) (As : list A),
      FlattenCompList.flatten_CompList
        (map (fun a : A => Query_Where (P a)
                                       (Query_Return a)) As) ↝ nil
      -> forall a, List.In a As -> ~ P a.
  Proof.
    induction As; simpl; intros; computes_to_inv; subst; simpl in *; intuition.
    unfold Query_Where, Query_Return in H; computes_to_inv; intuition.
    destruct (dec a) eqn: ?.
    - rewrite dec_decides_P in Heqb.
      apply H0 in Heqb; computes_to_inv;
        subst; simpl in *; subst; intuition eauto.
      discriminate.
    - subst; apply H0 in H1; computes_to_inv;
        subst; simpl in *; subst; intuition eauto.
      discriminate.
    - eapply IHAs; eauto.
      apply app_eq_nil in H''; intuition; subst; eauto.
  Qed.

  Corollary For_In_Where_Prop {qs_schema}
    : forall idx r_o P l,
      DecideableEnsemble P
      -> Query_For (Query_In (qs_schema := qs_schema)
                             r_o idx (fun r : RawTuple => Query_Where (P r)
                                                                      (Query_Return r) )) ↝ l
      -> Forall P l.
  Proof.
    unfold Query_In, Query_For, QueryResultComp; intros; computes_to_inv.
    apply Forall_forall; intros.
    eapply flatten_CompList_Prop in H'0; eauto.
    symmetry in H'.
    eapply Permutation_in; eauto.
  Qed.

  Corollary For_UnConstrQuery_In_Where_Prop {qs_schema}
    : forall idx r_o P l,
      DecideableEnsemble P
      -> Query_For (UnConstrQuery_In (qsSchema := qs_schema)
                                     r_o idx (fun r : RawTuple => Query_Where (P r)
                                                                              (Query_Return r) )) ↝ l
      -> Forall P l.
  Proof.
    unfold UnConstrQuery_In, Query_For, QueryResultComp; intros; computes_to_inv.
    apply Forall_forall; intros.
    eapply flatten_CompList_Prop in H'0; eauto.
    symmetry in H'.
    eapply Permutation_in; eauto.
  Qed.

  Lemma refine_For_Map {resultT resultT'}
    : forall comp
             (f : resultT' -> resultT),
      refine (Query_For (results <- comp; ret (map f results)))
             (results <- Query_For comp; ret (map f results)).
  Proof.
    intros; unfold Query_For; autorewrite with monad laws.
    f_equiv; intro.
    intros ? ?; computes_to_inv; subst.
    computes_to_econstructor; rewrite Permutation_map; eauto.
  Qed.

  Corollary refine_UnConstrQuery_In_Query_Where_Cond
            {qs_schema}
    : forall (r_n : UnConstrQueryStructure qs_schema)
             Ridx
             (ResultT : Type)
             (P Q : _ -> Prop)
             (body : _ -> Comp (list ResultT)),
      (forall tup, P tup <-> Q tup) ->
      refine (UnConstrQuery_In r_n Ridx (fun tup => Query_Where (P tup) (body tup)))
             (UnConstrQuery_In r_n Ridx (fun tup => Query_Where (Q tup) (body tup))).
  Proof.
    intros; apply refine_UnConstrQuery_In; intro.
    apply refine_Query_Where_Cond; eauto.
  Qed.
