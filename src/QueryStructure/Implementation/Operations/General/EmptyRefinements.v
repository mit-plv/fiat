Require Import Coq.Strings.String
        Coq.omega.Omega
        Coq.Lists.List
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.SetEq
        Fiat.Common.ilist2
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Computation
        Fiat.ADT
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Operations.Empty
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

Lemma EnsembleIndexedListEquivalence_lift_property {heading}
      {P: @RawTuple heading -> Prop} :
  forall (sequence: list (@RawTuple heading))
         (ensemble: IndexedEnsemble ),
    EnsembleIndexedListEquivalence ensemble sequence ->
    ((forall item,
        List.In item sequence -> P item) <->
     (forall item,
        Ensembles.In _ ensemble item -> P (indexedRawTuple item))).
Proof.
  intros * equiv;
  destruct equiv as [? [ l' (is_map & equiv & ?) ] ];
  setoid_rewrite equiv.
  unfold IndexedRawTuple, indexedRawTuple in *.
  split; intros; firstorder; subst; intuition.
  eapply H1; eapply in_map_iff; eauto.
  rewrite in_map_iff in H2; destruct_ex; intuition.
  subst; eauto.
Qed.

Lemma EnsembleIndexedListEquivalence_pick_new_index {heading} :
  forall (ens : Ensemble (@IndexedRawTuple heading)) seq,
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
      (GetUnConstrRelation (imap2 rawRel (Build_EmptyRelations (qschemaSchemas qsSchema)))
                           Ridx) [].
Proof.
  intros; simpl; split; simpl; intros;
  unfold GetRelation, In in *.
  + econstructor.
  + unfold GetUnConstrRelation; rewrite <- ith_imap2;
    rewrite Build_EmptyRelation_IsEmpty; simpl in *; intuition.
Qed.

Lemma EnsembleIndexedListEquivalence_Empty :
  forall qsSchema Ridx,
    EnsembleIndexedListEquivalence
      (GetUnConstrRelation (imap2 rawRel (Build_EmptyRelations (qschemaSchemas qsSchema)))
                           Ridx) [].
Proof.
  intros; simpl; split; simpl; intros;
  unfold GetRelation, In in *.
  + unfold GetUnConstrRelation; rewrite <- ith_imap2;
    rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
    exists 0; unfold UnConstrFreshIdx; intros; intuition.
  + eexists []; intuition.
  - unfold In in *; intuition.
    unfold GetUnConstrRelation in *; rewrite <- ith_imap2 in *;
    rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
  - econstructor.
Qed.

Lemma ith_Bounded_BuildEmptyRelations {n}
: forall ns idx, ith2 (Build_EmptyRelations (n := n) ns) idx = EmptyRelation _.
Proof.
  induction ns; intros.
  - inversion idx; subst.
  - revert ns IHns. pattern n, idx.
    apply Fin.caseS; simpl; intros; eauto.
Qed.
