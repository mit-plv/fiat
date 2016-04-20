Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List
        Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.ADTRefinement.GeneralBuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.Common.SetEq
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.ListMorphisms
        Fiat.Common.List.FlattenList
        Fiat.QueryStructure.Specification.Operations.FlattenCompList.

Lemma refine_SetEq_self {A} :
  forall l : list A,
    refine {l' | SetEq l' l}%comp
           (ret l).
Proof.
  unfold SetEq, refine; intros; computes_to_inv.
  computes_to_econstructor; subst; split; eauto.
Qed.

(* [Query_For] is opaque, so we need to make it transparent in
   order to reason about it. *)
Local Transparent Query_For.

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
  flat_map (fun a => map (fun b => (a, b)) l') l.

Lemma In_fold_right_app {A} (* unused *)
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
  unfold Join_Lists;
  setoid_rewrite in_flat_map;
  setoid_rewrite in_map_iff.
  firstorder; congruence.
Qed.

Definition swap_pair {A B} (x: A * B) := (snd x, fst x).

Lemma swap_pair_fst {A B} :
  forall (x: A * B), fst (swap_pair x) = snd x.
Proof.
  reflexivity.
Qed.

Lemma swap_pair_snd :
  forall {A B} (x: A * B), snd (swap_pair x) = fst x.
Proof.
  reflexivity.
Qed.

Require Import Fiat.Common.List.ListFacts.

Ltac trickle_swap :=
  (* faster than just calling repeat first [ setoid_rewrite _ | setoid_rewrite _ ] *)
  repeat match goal with
           | [ |- context [ filter _ (map swap_pair _) ] ] =>
             setoid_rewrite filter_map with (g := swap_pair)
           | [ |- context [ map    _ (map swap_pair _) ] ] =>
             setoid_rewrite map_map with (f := swap_pair)
         end;
  try setoid_rewrite swap_pair_fst; (* TODO: broken *)
  try setoid_rewrite swap_pair_snd.

Lemma join_nil_r :
  forall {A B} s1,
    @Join_Lists A B s1 [] = [].
Proof.
  unfold Join_Lists;
  induction s1; simpl; intros;
  try rewrite flat_map_empty; reflexivity.
Qed.

Lemma join_nil_l :
  forall {A B} s2,
    @Join_Lists A B [] s2 = [].
Proof.
  unfold Join_Lists;
  induction s2; simpl; intros;
  reflexivity.
Qed.


Lemma swap_joins :
  forall {A B} s1 s2,
    Permutation
      (@Join_Lists A B s1 s2)
      (map swap_pair (Join_Lists s2 s1)).
Proof.
  induction s1; simpl; intros.

  - rewrite join_nil_r; trivial.
  - rewrite IHs1; unfold Join_Lists.
    replace (map (fun b : B => (a, b)) s2) with (map swap_pair (map (fun b : B => (b, a)) s2))
      by (induction s2; unfold swap_pair in *; simpl; try rewrite IHs2; firstorder).
    rewrite <- map_app; f_equiv; simpl.
    induction s2; simpl; trivial.
    constructor; rewrite <- IHs2.
    rewrite !app_assoc.
    apply Permutation_app_tail, Permutation_app_comm.
Qed.

Lemma filter_join_fst :
  forall {A B} f s1 s2,
    List.filter (fun x => f (fst x)) (@Join_Lists A B s1 s2) =
    Join_Lists (List.filter f s1) s2.
Proof.
  unfold Join_Lists; induction s1; intros; simpl.

  - reflexivity.
  - destruct (f a) eqn:eq_fa;
    rewrite filter_app, filter_map;
    simpl; rewrite eq_fa;
    [ rewrite filter_true | rewrite filter_false ];
    simpl; rewrite IHs1; reflexivity.
Qed.

Lemma filter_join_snd :
  forall {A B} f s1 s2,
    List.filter (fun x => f (snd x)) (@Join_Lists A B s1 s2) =
    Join_Lists s1 (List.filter f s2).
Proof.
  unfold Join_Lists; induction s2; intros; simpl.

  - rewrite !flat_map_empty; reflexivity.
  - rewrite !flat_map_flatten, !flatten_filter in IHs2 |- *.
    induction s1; simpl in *; trivial.
    destruct (f a) eqn:eq_fa; simpl in *.
    f_equal. rewrite IHs1.
    rewrite filter_map; reflexivity.
    rewrite <- !flat_map_flatten.
    apply filter_flat_map_join_snd.
    rewrite IHs1. rewrite filter_map.
    simpl; reflexivity.
    rewrite <- !flat_map_flatten.
    apply filter_flat_map_join_snd.
Qed.


Lemma filter_join_lists :
  forall {A B} (f: A * B -> bool) xs ys,
    filter f (Join_Lists xs ys) =
    (flat_map (fun x => map (fun y => (x, y)) (filter (fun y : B => f (x, y)) ys)) xs).
Proof.
  intros.
  unfold Join_Lists.
  rewrite filter_flat_map.
  setoid_rewrite filter_map.
  reflexivity.
Qed.

Lemma refine_List_Query_In {ResultT}
      qsSchema qs R l resultComp
: EnsembleIndexedListEquivalence (GetUnConstrRelation qs R) l
  -> refine (@UnConstrQuery_In ResultT qsSchema qs R resultComp)
            (List_Query_In l resultComp).
Proof.
  intros; destruct H as [l' [eq_l_l' [eq_l_R equiv_l_R ] ] ].
  intros; unfold UnConstrQuery_In, QueryResultComp, List_Query_In;
  rewrite refine_pick_val; unfold UnIndexedEnsembleListEquivalence; eauto.
  simplify with monad laws; subst; reflexivity.
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
  assert (resultComp a = fun x : RawTuple => resultComp a x) as eta by
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
    + apply Decides_false in H.
      unfold refine; intro; econstructor; intuition.
      econstructor; intuition.
      repeat econstructor; eauto.
Qed.

Lemma refine_For_List {ResultT : Type}
      (bod : Comp (list ResultT))
: refine (Query_For bod) bod.
Proof.
  unfold Query_For, refine; intros; computes_to_econstructor;
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
  unfold Query_For; computes_to_econstructor; eauto.
Qed.

Lemma refine_Permutation_Reflexivity :
  forall (ResultT : Type) (l : list ResultT),
    refine
      (Pick (fun l' => Permutation l l'))
      (ret l).
Proof.
  computes_to_constructor;  computes_to_inv; subst; eauto.
Qed.

Add Parametric Morphism {A B : Type} (l : list A)
: (@List_Query_In A B l)
    with signature (pointwise_relation _ refine ==> refine)
      as refine_List_Query_In_equiv.
Proof.
  unfold pointwise_relation, List_Query_In; intros.
  induction l; simpl.
  - reflexivity.
  - setoid_rewrite H; setoid_rewrite IHl; reflexivity.
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
  unfold refine; intros;  computes_to_inv; subst.
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
