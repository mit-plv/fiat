Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation
        ADTRefinement.GeneralBuildADTRefinements
        QueryStructureSchema QueryQSSpecs QueryStructure
        GeneralQueryRefinements AdditionalLemmas SetEq.

Lemma refine_SetEq_self {A} :
  forall l : list A,
    refine {l' | SetEq l' l}%comp
           (ret l).
Proof.
  unfold SetEq, refine; intros; inversion_by computes_to_inv.
  econstructor; subst; split; eauto.
Qed.

Lemma Equivalent_In_EnsembleListEquivalence {ReturnT TraceT}
      (qs : QueryStructureHint) (R : _)
      (l : list _)
      (bod : @Tuple _ -> Ensemble (ReturnT * TraceT))
: EnsembleListEquivalence (GetRelation qsHint R) l ->
  Equivalent_Trace_Ensembles
    (@Query_In qs _ _ R bod)
    (fun el => List.In (fst (snd el)) l
     /\ bod (fst (snd el)) (fst el, snd (snd el))).
Proof.
  econstructor 1 with (TraceT_map := id)
                        (TraceT'_map := id);
  intros; destruct_pairs; unfold id in *; auto;
  unfold Query_In in *; simpl in *; intuition.
  rewrite GetRelDropConstraints in *; apply H; apply H1.
  rewrite GetRelDropConstraints in *; apply H; apply H1.
Qed.

Lemma Equivalent_UnConstr_In_EnsembleListEquivalence
      {ReturnT TraceT}
      qsSchema qs (R : _)
      (l : list _)
      (bod : @Tuple _ -> Ensemble (ReturnT * TraceT))
: EnsembleListEquivalence (GetUnConstrRelation qs R) l
  -> Equivalent_Trace_Ensembles
       (@UnConstrQuery_In qsSchema qs _ _ R bod)
       (fun el => List.In (fst (snd el)) l
                  /\ bod (fst (snd el)) (fst el, snd (snd el))).
Proof.
  econstructor 1 with (TraceT_map := id)
                        (TraceT'_map := id);
  intros; destruct_pairs; unfold id in *; auto;
  unfold UnConstrQuery_In in *; simpl in *; intuition.
  apply H; apply H1.
  apply H; apply H1.
Qed.

Definition Join_Lists {A B}
           (l : list A)
           (l' : list B)
: list (A * B) :=
  fold_left (@app _) (map (fun a => map (fun b => (a, b)) l') l) nil.

Lemma In_fold_left_app {A}
: forall (l : list (list A))
         (l'' : list A)
         (a : A),
    List.In a (fold_left (@app _) l l'') <->
    (List.In a l'' \/ (exists l', List.In l' l /\ List.In a l')).
Proof.
  induction l; simpl; intuition.
  destruct_ex; intuition.
  destruct (proj1 (IHl _ _) H).
  apply in_app_or in H0; intuition; eauto.
  destruct_ex; intuition; eauto.
  eapply IHl; eauto using in_or_app.
  destruct_ex; intuition; subst; eauto.
  eapply IHl; eauto using in_or_app.
  eapply IHl; eauto using in_or_app.
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
  apply In_fold_left_app in H; simpl in *; intuition;
  destruct_ex; intuition;
  apply in_map_iff in H0; destruct_ex; intuition; subst;
  apply in_map_iff in H1; destruct_ex; intuition; subst;
  simpl; congruence.
  intuition.
  apply In_fold_left_app; right.
  exists (map (fun b : B => (a, b)) l'); split;
  apply in_map_iff; eexists; intuition; eauto.
Qed.

Lemma Equivalent_Join_Lists {ReturnT TraceT heading}
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
