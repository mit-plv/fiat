Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List
        Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Computation Fiat.ADT
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Operations.Empty
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.SetEq
        Fiat.Common.Ensembles.IndexedEnsembles.

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

Lemma ith_Bounded_BuildEmptyRelations
: forall ns idx, ith_Bounded relName (Build_EmptyRelations ns) idx = EmptyRelation _.
Proof.
  unfold ith_Bounded, nth_Bounded; simpl.
  destruct idx as [idx [n In_n ]]; simpl in *.
  revert idx n In_n; clear; induction ns; destruct n; simpl;
  intros; try discriminate; eauto.
Qed.
