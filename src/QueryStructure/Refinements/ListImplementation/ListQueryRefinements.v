Require Import String Omega List FunctionalExtensionality Ensembles
        Sorting.Permutation Computation ADT ADTRefinement ADTNotation
        ADTRefinement.GeneralBuildADTRefinements
        QueryStructureSchema QueryQSSpecs QueryStructure
        GeneralQueryRefinements AdditionalLemmas SetEq
        ListQueryStructureRefinements.

Lemma refine_SetEq_self {A} :
  forall l : list A,
    refine {l' | SetEq l' l}%comp
           (ret l).
Proof.
  unfold SetEq, refine; intros; inversion_by computes_to_inv.
  econstructor; subst; split; eauto.
Qed.

(* Lemma Equivalent_In_EnsembleListEquivalence {ReturnT}
      (qs : QueryStructureHint) (R : _)
      (l : list _)
      (l' : Tuple -> list ReturnT)
      (bod : Tuple -> Comp (list ReturnT))
: EnsembleListEquivalence (GetRelation qsHint R) l ->
  pointwise_relation _ refine bod (fun tup => ret (l' tup))
  -> refine
       (@Query_In qs _ R bod)
       (ret (flatten (map l' l))).
Proof.
  intros.
  unfold Query_In, QueryResultComp.
  econstructor.
  econstructor.


  eauto.
Lemma Equivalent_UnConstr_In_EnsembleListEquivalence {ReturnT}
      qsSchema qs (R : _)
      (l : list _)
      (l' : Tuple -> list ReturnT)
      (bod : Tuple -> Comp (list ReturnT))
: EnsembleListEquivalence (GetUnConstrRelation qs R) l ->
  pointwise_relation _ refine bod (fun tup => ret (l' tup))
  -> refine
       (@UnConstrQuery_In qsSchema qs _ R bod)
       (ret (flatten (map l' l))).
Proof.

  econstructor 1 with (TraceT_map := id)
                        (TraceT'_map := id);
  intros; destruct_pairs; unfold id in *; auto;
  unfold UnConstrQuery_In in *; simpl in *; intuition.
  apply H; apply H1.
  apply H; apply H1.
Qed. *)

Definition Join_Lists {A B}
           (l : list A)
           (l' : list B)
: list (A * B) :=
  fold_right (@app _) nil (map (fun a => map (fun b => (a, b)) l') l).

Lemma In_fold_right_app {A}
: forall (l : list (list A))
         (l'' : list A)
         (a : A),
    List.In a (fold_right (@app _) l'' l) <->
    (List.In a l'' \/ (exists l', List.In l' l /\ List.In a l')).
Proof.
  induction l; simpl; intuition.
  destruct_ex; intuition.
  apply in_app_or in H; intuition; eauto.
  destruct (proj1 (IHl _ _) H0); intuition.
  destruct_ex; intuition; eauto.
  eapply in_or_app; right; eapply IHl; intuition.
  destruct_ex; intuition; subst; eauto.
  eapply in_or_app; left; eauto.
  eapply in_or_app; right; eapply IHl; eauto.
Qed.

Lemma In_Join_Lists {A B}
: forall (l : list A)
         (l' : list B)
         (a : A)
         (b : B),
    List.In (a, b) (Join_Lists l l') <->
    (List.In a l /\ List.In b l').
Proof.
  unfold Join_Lists; split; intros.
  apply In_fold_right_app in H; simpl in *; intuition;
  destruct_ex; intuition;
  apply in_map_iff in H0; destruct_ex; intuition; subst;
  apply in_map_iff in H1; destruct_ex; intuition; subst;
  simpl; congruence.
  intuition.
  apply In_fold_right_app; right.
  exists (map (fun b : B => (a, b)) l'); split;
  apply in_map_iff; eexists; intuition; eauto.
Qed.

Definition List_Query_In
           {QueryT ResultT}
           (queriedList : list QueryT)
           (resultComp : QueryT -> Comp (list ResultT))
  :=
    flatten_CompList (map resultComp queriedList).

Lemma refine_List_Query_In {ResultT}
      qsSchema qs R l resultComp
: EnsembleIndexedListEquivalence (GetUnConstrRelation qs R) l
  -> refine (@UnConstrQuery_In ResultT qsSchema qs R resultComp)
            (List_Query_In l resultComp).
Proof.
  intros; destruct H as [l' [eq_l_l' [eq_l_R equiv_l_R ]]].
  intros; unfold UnConstrQuery_In, QueryResultComp, List_Query_In;
  rewrite refine_pick_val; eauto; simplify with monad laws.
  subst; reflexivity.
Qed.

Lemma refine_Join_List_Query_In {QueryT ResultT}
      qsSchema qs R l' l resultComp
: EnsembleIndexedListEquivalence (GetUnConstrRelation qs R) l
  -> refine (List_Query_In (QueryT := QueryT) l'
                           (fun b => @UnConstrQuery_In ResultT qsSchema qs R (resultComp b)))
            (List_Query_In (Join_Lists l' l) (fun b => (resultComp (fst b) (snd b)))).
Proof.
  intros; unfold QueryResultComp, List_Query_In.
  rewrite refine_flatten_CompList_func.
  Focus 2.
  unfold pointwise_relation; intros.
  apply refine_List_Query_In; eassumption.
  unfold List_Query_In, flatten_CompList.
  induction l'; simpl.
  reflexivity.
  setoid_rewrite IHl'; clear IHl'.
  unfold Join_Lists; simpl; auto.
  simpl; rewrite map_app.
  rewrite map_map.
  repeat rewrite fold_right_app.
  simpl.
  assert (resultComp a = fun x : Tuple => resultComp a x) as eta by
      (apply functional_extensionality; auto); rewrite <- eta.
  induction (map (resultComp a) l); simpl;
  simplify with monad laws.
  - reflexivity.
  - setoid_rewrite <- IHl0.
    repeat setoid_rewrite refineEquiv_bind_bind.
    setoid_rewrite refineEquiv_bind_unit.
    setoid_rewrite app_assoc; reflexivity.
Qed.

Lemma refine_List_Query_In_Where {QueryT ResultT}
      l (P : Ensemble QueryT)
      (resultComp : QueryT -> Comp (list ResultT))
      (P_dec : DecideableEnsemble P)
: refine (List_Query_In (QueryT := QueryT) l
                           (fun b => Query_Where (P b) (resultComp b)))
            (List_Query_In (filter dec l) resultComp).
Proof.
  induction l; unfold List_Query_In, Query_Where in *; simpl.
  - reflexivity.
  - caseEq (dec a); simpl;
    setoid_rewrite <- IHl.
    + f_equiv; apply dec_decides_P in H;
      unfold refine; intro; econstructor; intuition.
    + unfold refine; intro; econstructor; intuition.
      simpl; eauto.
Qed.

Lemma refine_For_List {ResultT : Type}
      (bod : Comp (list ResultT))
: refine (Query_For bod) bod.
Proof.
  unfold Query_For, refine; intros; econstructor;
  eauto.
Qed.

Lemma refine_List_Query_In_Return {QueryT ResultT : Type}
      (l : list QueryT) (proj : QueryT -> ResultT)
: refine (List_Query_In l (fun tup => Query_Return (proj tup)))
         (ret (map proj l)) .
Proof.
  induction l; unfold Query_For, List_Query_In, Query_Return in *;
  simpl; intros.
  - reflexivity.
  - simplify with monad laws.
    rewrite IHl; simplify with monad laws.
    reflexivity.
Qed.

Lemma refine_List_For_Query_In_Return {QueryT ResultT : Type}
      (l : list QueryT) (proj : QueryT -> ResultT)
: refine (Query_For (List_Query_In l (fun tup => Query_Return (proj tup))))
         (ret (map proj l)) .
Proof.
  rewrite refine_List_Query_In_Return, refine_For_List.
  reflexivity.
Qed.

Lemma refine_List_For_Query_In_Return_Permutation :
  forall (QueryT ResultT : Type) (l : list QueryT) (proj : QueryT -> ResultT),
    refine
      (For (List_Query_In l (fun tup : QueryT => Return (proj tup))))%QuerySpec
      (Pick (fun l' => Permutation (map proj l) l')).
Proof.
  intros; rewrite refine_List_Query_In_Return;
  unfold Query_For; econstructor; eauto.
Qed.

Lemma refine_Permutation_Reflexivity :
  forall (ResultT : Type) (l : list ResultT),
    refine
      (Pick (fun l' => Permutation l l'))
      (ret l).
Proof.
  constructor; inversion_by computes_to_inv; subst; eauto.
Qed.

      (*Lemma Equivalent_Join_Lists {ReturnT TraceT heading}
      qsSchema qs R (l : list (@Tuple heading)) l'
      (bod : Tuple -> Tuple -> Ensemble (ReturnT * TraceT))
: EnsembleListEquivalence (GetUnConstrRelation qs R) l' ->
  Equivalent_Trace_Ensembles
    (fun tup' : ReturnT * (Tuple * (Tuple * TraceT)) =>
                           List.In (fst (snd tup')) l /\
                 (@UnConstrQuery_In qsSchema qs _ _ R (bod (fst (snd tup')))
                                    (fst tup', snd (snd tup'))))
    (fun tup' : ReturnT * (Tuple * (Tuple * TraceT)) =>
       List.In ((fst (snd tup')), fst (snd (snd tup'))) (Join_Lists l l') /\
       (bod (fst (snd tup')) (fst (snd (snd tup'))) (fst tup', snd (snd (snd tup'))))).
Proof.
  econstructor 1 with (TraceT_map := id)
                        (TraceT'_map := id);
  intros; destruct_pairs; unfold id in *; auto;
  unfold UnConstrQuery_In in *; simpl in *; intuition.
  - eapply In_Join_Lists; split; eauto.
    eapply H; eauto.
  - eapply (proj1 (In_Join_Lists _ _ _ _ ) H1) .
  - eapply H; eapply (proj1 (In_Join_Lists _ _ _ _ ) H1).
Qed.

Lemma Equivalent_List_In_Where {ReturnT TraceT TraceT'}
      (l : list TraceT)
      (P : Ensemble TraceT)
      (bod : TraceT -> Ensemble (ReturnT * TraceT'))
      (P_dec : DecideableEnsemble P)
:
  Equivalent_Trace_Ensembles
    (fun tup : ReturnT * (TraceT * TraceT') =>
       List.In (fst (snd tup)) l
       /\ Query_Where (P (fst (snd tup))) (bod (fst (snd tup)))
                      (fst tup, snd (snd tup)))
    (fun tup : ReturnT * (TraceT * TraceT') =>
       List.In (fst (snd tup)) (filter dec l)
       /\ bod (fst (snd tup)) (fst tup, snd (snd tup))) .
Proof.
  destruct P_dec.
  econstructor 1 with (TraceT_map := id)
                        (TraceT'_map := id);
  intros; destruct_pairs; unfold id in *; auto;
  unfold In, Query_Where in *; simpl in *; intuition.
  - eapply filter_In; split; eauto;
    eapply dec_decides_P; eauto.
  - eapply filter_In; eauto.
  - eapply dec_decides_P; eapply filter_In; eauto.
Qed.

Lemma refine_For_List_Return {ReturnT TraceT}
      (l : list _ )
      (extract : TraceT -> ReturnT)
: NoDup l
  -> refine
    (For (fun el : ReturnT * (TraceT * unit) =>
            List.In (fst (snd el)) l /\ Return (extract (fst (snd el))) (fst el, tt)))%QuerySpec
    (ret (map extract l)).
Proof.
  unfold refine; intros; inversion_by computes_to_inv; subst.
  econstructor; unfold In, Query_Return.
  eexists (map (fun el => (extract el, (el, tt))) l); split.
  rewrite map_map; simpl; f_equal.
  unfold EnsembleListEquivalence.
  split; intros.
  { induction l; simpl in *; econstructor; inversion H; subst; eauto.
    unfold not; intros; eapply H2.
    revert H0; clear; induction l; simpl; intros; intuition.
    injections; auto.
  }
  { unfold In; split; intros.
    eapply in_map_iff; destruct_ex; intuition; eauto.
    exists (fst (snd x)); destruct_pairs; simpl in *; split; eauto.
    f_equal; eauto.
    destruct u; eauto.
    eapply in_map_iff in H0; destruct_ex; intuition; eauto.
    subst; simpl; eauto.
    destruct_pairs; simpl in *; injections; auto.
  }
Qed.

Tactic Notation "implement" "queries" "for" "lists" :=
  unfold DropQSConstraints_AbsR in *; subst;
  repeat rewrite GetRelDropConstraints in *; subst; split_and;
  repeat (progress
            (try (setoid_rewrite Equivalent_UnConstr_In_EnsembleListEquivalence; simpl; eauto);
             try (setoid_rewrite Equivalent_List_In_Where with (P_dec := _); simpl);
             try (setoid_rewrite Equivalent_Join_Lists; eauto)));
  setoid_rewrite refine_For_List_Return; try simplify with monad laws.

Tactic Notation "implement" "query" "in" constr(queryName) "with" "lists" "under" hyp(AbsR) :=
    hone method queryName;
  [ unfold AbsR in *; split_and;
    setoid_rewrite refineEquiv_pick_ex_computes_to_and;
    simplify with monad laws;
    implement queries for lists;
    setoid_rewrite refineEquiv_pick_pair_pair;
    setoid_rewrite refineEquiv_pick_eq';
    repeat (rewrite refine_pick_val; [simplify with monad laws | eassumption]);
    finish honing
  |
  ].
 *)
