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

Lemma Equivalent_In_EnsembleListEquivalence {A}
      (qs : QueryStructureHint) (R : _)
      (l : list _)
      bod
: EnsembleListEquivalence (GetRelation qsHint R) l ->
  Equivalent_Ensembles
    (@Query_In qs A R bod)
    (fun a => exists tup, List.In tup l /\ bod tup a).
Proof.
  split; intros; unfold In in *.
  destruct H0; eexists; intuition; eauto.
  eapply H; eauto.
  rewrite GetRelDropConstraints in H1; apply H1.
  destruct H0; intuition; eexists; split; eauto.
  rewrite GetRelDropConstraints; eapply H; eauto.
Qed.

Lemma Equivalent_UnConstr_In_EnsembleListEquivalence {A}
      qsSchema qs R l bod
: EnsembleListEquivalence (GetUnConstrRelation qs R) l ->
  Equivalent_Ensembles
    (@UnConstrQuery_In qsSchema qs A R bod)
    (fun a => exists tup, List.In tup l /\ bod tup a).
Proof.
  split; intros; unfold In in *.
  destruct H0; eexists; intuition; eauto.
  eapply H; eauto.
  destruct H0; intuition; eexists; split; eauto.
  eapply H; eauto.
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

Lemma Equivalent_Join_Lists {A B}
      qsSchema qs R (l : list B) l' bod
: EnsembleListEquivalence (GetUnConstrRelation qs R) l' ->
  Equivalent_Ensembles
    (fun a => exists b, List.In b l /\
                        (@UnConstrQuery_In qsSchema qs A R (bod b) a))
    (fun a => exists b, List.In b (Join_Lists l l') /\
                        (bod (fst b) (snd b) a)).
Proof.
  split; intros; unfold In in *.
  - destruct H0; intuition; destruct H2; eexists; intuition; eauto.
    unfold EnsembleListEquivalence in H.
    apply In_Join_Lists; split; eauto.
    eapply H; unfold In; apply H2.
    simpl; auto.
  - destruct_ex; intuition; destruct x; eexists; intuition.
    eapply (In_Join_Lists l l'); eauto.
    eexists; intuition; eauto.
    apply H; eapply (In_Join_Lists l l'); eauto.
Qed.

Lemma Equivalent_List_In_Where {A B : Type}
      (l : list B)
      (P : Ensemble B)
      (bod : B -> Ensemble A)
      (P_dec : DecideableEnsemble P)
:
  Equivalent_Ensembles
    (fun a : A => exists b, List.In b l /\ Query_Where (P b) (bod b) a)
    (fun a : A => exists b, List.In b (filter dec l) /\ (bod b) a)
.
Proof.
  destruct P_dec; split; intros; unfold In, Query_Where in *.
  destruct H; eexists; intuition; eauto.
  eapply filter_In; split; eauto.
  eapply dec_decides_P; eauto.
  destruct H; intuition; eexists; split; eauto.
  eapply filter_In; eauto.
  intuition; eauto using filter_In.
  eapply dec_decides_P; eapply filter_In; eauto.
Qed.

Lemma refine_For_List_Return {A B}
      (l : list B)
      (extract : B -> A)
: refine
    (For (fun a : A =>
            exists b : B,
              List.In b l /\ Return (extract b) a))%QuerySpec
    (ret (map extract l)).
Proof.
  unfold refine; intros; inversion_by computes_to_inv; subst.
  econstructor; unfold In, Query_Return; split; intros.
  eapply in_map_iff in H; destruct_ex; intuition; eauto.
  eapply in_map_iff; destruct_ex; intuition; eauto.
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
