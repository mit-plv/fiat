Require Import Coq.Strings.String Coq.Lists.List Coq.Sorting.Permutation
        Coq.Logic.FunctionalExtensionality
        ADTSynthesis.ADTNotation Coq.Sets.Ensembles ADTSynthesis.Common
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

Instance DecideableEnsemble_EqDec {A B : Type}
         (B_eq_dec : Query_eq B)
         (f f' : A -> B)
         : DecideableEnsemble (fun a => eq (f a) (f' a)) :=
  {| dec a := if A_eq_dec (f a) (f' a) then true else false |}.
Proof.
  intros; find_if_inside; split; congruence.
Defined.

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
