Require Import String List FunctionalExtensionality Ensembles Common
        Computation BuildADTRefinements
        QueryStructureSchema QueryQSSpecs QueryStructure.

Definition UnConstrQuery_In qsSchema (qs : UnConstrQueryStructure qsSchema) {A} (R : _)
           (bod : @Tuple _ -> Ensemble A)
           (a : A) :=
  exists tup, (GetUnConstrRelation qs R) tup /\
              bod tup a.

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

Definition Equivalent_Ensembles {A : Type}
           (P Q : Ensemble A) := forall a, P a <-> Q a.

Lemma Equivalent_Swap_In {A}
      qsSchema qs R R' (bod : Tuple -> Tuple -> Ensemble A)
:
  Equivalent_Ensembles
    (@UnConstrQuery_In qsSchema qs _ R (fun tup => @UnConstrQuery_In qsSchema qs _ R' (bod tup)))
    (@UnConstrQuery_In qsSchema qs _ R' (fun tup => @UnConstrQuery_In qsSchema qs _ R
                                             (fun tup' => bod tup' tup))).
Proof.
  unfold Equivalent_Ensembles, UnConstrQuery_In; split; intros;
  repeat (progress (destruct_ex; intuition)); eexists;
  split; eauto.
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

Lemma refineEquiv_For_DropQSConstraints A qsSchema qs :
  forall bod,
      refine
     {H1 |
      exists or' : QueryStructure qsSchema * list A,
       (queryRes <- (For bod)%QuerySpec;
        ret (qs, queryRes)) ↝ or' /\
       DropQSConstraints_SiR (fst or') (fst H1) /\ snd or' = snd H1}
     (b <- (For bod)%QuerySpec;
      ret (DropQSConstraints qs, b) ) .
Proof.
  setoid_rewrite refineEquiv_pick_ex_computes_to_bind_and;
  intros; f_equiv; unfold pointwise_relation; intros.
  setoid_rewrite refineEquiv_pick_ex_computes_to_and;
  setoid_rewrite refineEquiv_bind_unit; simpl;
  unfold DropQSConstraints_SiR;
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
        H : DropQSConstraints_SiR _ _ |- _ =>
        unfold DropQSConstraints_SiR in H; rewrite H
    end; simplify with monad laws;
    finish honing | ].
