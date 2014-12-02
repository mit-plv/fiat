Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List
        Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Computation ADTSynthesis.ADT
        ADTSynthesis.Common.Ensembles.EnsembleListEquivalence
        ADTSynthesis.ADTRefinement
        ADTSynthesis.ADTNotation
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.Specification.Operations.Empty
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.Common.SetEq
        ADTSynthesis.Common.Ensembles.IndexedEnsembles.

Lemma EnsembleIndexedListEquivalence_lift_property {heading} {P: @Tuple heading -> Prop} :
  forall (sequence: list (@Tuple heading)) (ensemble: @IndexedTuple heading -> Prop),
    EnsembleIndexedListEquivalence ensemble sequence ->
    ((forall item,
        List.In item sequence -> P item) <->
     (forall item,
        Ensembles.In _ ensemble item -> P (indexedTuple item))).
Proof.
  intros * equiv;
  destruct equiv as [? [ l' (is_map & equiv & ?) ] ];
  setoid_rewrite equiv.
  unfold IndexedTuple, indexedTuple in *.
  split; intros; firstorder; subst; intuition.
  eapply H1; eapply in_map_iff; eauto.
  rewrite in_map_iff in H2; destruct_ex; intuition.
  subst; eauto.
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
  + eexists []; intuition.
  - unfold In in *; intuition.
    rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
  - econstructor.
Qed.
