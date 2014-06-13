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

Class Equivalent_Trace_Ensembles {ReturnT TraceT TraceT' : Type}
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
    finish honing | ].
