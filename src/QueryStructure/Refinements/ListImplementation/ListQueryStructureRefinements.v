Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Computation ADTSynthesis.ADT ADTSynthesis.ADTRefinement ADTSynthesis.ADTNotation ADTSynthesis.QueryStructure.QueryStructureSchema
        ADTSynthesis.ADTRefinement.BuildADTRefinements ADTSynthesis.QueryStructure.QuerySpecs.QueryQSSpecs ADTSynthesis.QueryStructure.QuerySpecs.InsertQSSpecs ADTSynthesis.QueryStructure.QuerySpecs.EmptyQSSpecs
        ADTSynthesis.QueryStructure.QueryStructure ADTSynthesis.QueryStructure.Refinements.GeneralInsertRefinements
        ADTSynthesis.QueryStructure.Refinements.GeneralQueryRefinements ADTSynthesis.QueryStructure.SetEq ADTSynthesis.QueryStructure.AdditionalLemmas ADTSynthesis.QueryStructure.IndexedEnsembles.

Lemma EnsembleIndexedListEquivalence_lift_property {heading} {P: @Tuple heading -> Prop} :
  forall (sequence: list (@Tuple heading)) (ensemble: @IndexedTuple heading -> Prop),
    EnsembleIndexedListEquivalence ensemble sequence ->
    ((forall item,
        List.In item sequence -> P item) <->
     (forall item,
        Ensembles.In _ ensemble item -> P (indexedTuple item))).
Proof.
  intros * equiv;
  destruct equiv as [_ [ l' (is_map & _ & equiv) ] ];
  subst.
  setoid_rewrite equiv.
  setoid_rewrite in_map_iff.
  unfold IndexedTuple, indexedTuple in *.
  split; intros; firstorder; subst; intuition.
Qed.

Lemma EnsembleIndexedListEquivalence_pick_new_index {heading} :
  forall (ens : Ensemble (@IndexedTuple heading)) seq,
    EnsembleIndexedListEquivalence ens seq ->
    exists bound,
      UnConstrFreshIdx ens bound.
Proof.
  intros * (indexes & equiv) ** .
  destruct_ex; eexists x; eauto.
Qed.

  Lemma EnsembleListEquivalence_Empty :
    forall qsSchema Ridx,
      EnsembleListEquivalence
        (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qsSchema))
                             Ridx) [].
  Proof.
    intros; rewrite GetRelDropConstraints; simpl; split; simpl; intros;
    unfold GetRelation, In in *.
    + econstructor.
    + rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
  Qed.

  Lemma EnsembleIndexedListEquivalence_Empty :
    forall qsSchema Ridx,
      EnsembleIndexedListEquivalence
        (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qsSchema))
                             Ridx) [].
  Proof.
    intros; rewrite GetRelDropConstraints; simpl; split; simpl; intros;
    unfold GetRelation, In in *.
    + rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
      exists 0; unfold UnConstrFreshIdx; intros; intuition.
    + eexists []; intuition; econstructor.
      - econstructor.
      - unfold In; split; intros.
        * rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
        * intuition.
  Qed.

Ltac implement_empty_list constrName RepAbsR :=
  hone constructor constrName;
  [ unfold RepAbsR, DropQSConstraints_AbsR;
    repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
    repeat setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws;
    repeat rewrite refineEquiv_pick_pair;
    repeat (rewrite refine_pick_val;
            [simplify with monad laws
            | apply EnsembleIndexedListEquivalence_Empty]);
        subst_body; higher_order_1_reflexivity
  | ].

(*Tactic Notation "implement" "using" "lists" "under" constr(Rep_AbsR) :=
    let AbsR_Hyp := fresh in
    pose Rep_AbsR as AbsR_Hyp;
      unfold Rep_AbsR in AbsR_Hyp;
      hone representation using AbsR_Hyp;
      repeat match goal with
                 |- context[
                        (const ?R ( _ : _ ) : rep :=
                           { _ | exists _, _ })%consDef] =>
                 implement_empty_list R AbsR_Hyp
             end;
      repeat
        match goal with
            |- context [ (meth ?R ( _ : rep , _ : _ ) : _ :=
                            {nr' | forall or , _ } )%methDef] =>
            first [ implement insert in R with lists under AbsR_Hyp
                  | implement query in R with lists under AbsR_Hyp ]
        end.
*)
