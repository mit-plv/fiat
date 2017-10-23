Require Import Coq.Strings.String
        Coq.omega.Omega
        Coq.Lists.List
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.List.ListFacts
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.ilist2
        Fiat.Computation
        Fiat.Computation.Refinements.Iterate_Decide_Comp
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Mutate
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.Common.Ensembles.EnsembleListEquivalence.

(* Facts about implements delete operations. *)

Section MutateRefinements.

  Hint Resolve crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesAttributeConstraints
       SatisfiesTupleConstraints.

  Arguments GetUnConstrRelation : simpl never.
  Arguments UpdateUnConstrRelation : simpl never.
  Arguments replace_BoundedIndex : simpl never.
  Arguments BuildQueryStructureConstraints : simpl never.
  Arguments BuildQueryStructureConstraints' : simpl never.

  Program
    Definition Mutate_Valid
    (qsSchema : QueryStructureSchema)
    (qs : QueryStructure qsSchema)
    (Ridx : _)
    (MutatedTuples : @IndexedEnsemble RawTuple)
    (attrConstr :
       (forall tup : IndexedRawTuple,
         GetRelation qs Ridx tup
         -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
       -> MutationPreservesAttributeConstraints MutatedTuples (SatisfiesAttributeConstraints Ridx))
    (tupConstr :
       (forall tup tup' : IndexedRawTuple,
          elementIndex tup <> elementIndex tup'
          -> GetRelation qs Ridx tup
          -> GetRelation qs Ridx tup'
          -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup')) ->
       MutationPreservesTupleConstraints MutatedTuples (SatisfiesTupleConstraints Ridx))
    (* And is compatible with the cross-schema constraints. *)
    (CrossConstr :
       (@Iterate_Ensemble_BoundedIndex_filter
          _ (fun Ridx' =>
             forall tup' : IndexedRawTuple,
               GetUnConstrRelation (DropQSConstraints qs) Ridx tup' ->
               SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup') (GetRelation qs Ridx'))
          (fun idx => if fin_eq_dec Ridx idx then false else true)
       ) ->
       (forall Ridx',
          (Ridx' <> Ridx) ->
          MutationPreservesCrossConstraints MutatedTuples (GetRelation qs Ridx')
                                            (SatisfiesCrossRelationConstraints Ridx Ridx')))
    (CrossConstr' :
       (@Iterate_Ensemble_BoundedIndex_filter
          _
          (fun Ridx' =>
             forall tup' : IndexedRawTuple,
               GetUnConstrRelation (DropQSConstraints qs) Ridx' tup' ->
               SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup') (GetRelation qs Ridx))
          (fun idx => if fin_eq_dec Ridx idx then false else true)) ->
       (forall Ridx',
          (Ridx' <> Ridx) ->
          MutationPreservesCrossConstraints (GetRelation qs Ridx')
                                            MutatedTuples
                                            (SatisfiesCrossRelationConstraints Ridx' Ridx)))
  : QueryStructure qsSchema :=
    {| rawRels :=
         UpdateRelation (rawRels qs) Ridx {| rawRel := MutatedTuples|}
    |}.
  Next Obligation.
    unfold MutationPreservesAttributeConstraints,
    SatisfiesAttributeConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ith2 (rawRels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (attrConstraints  (Vector.nth
                         (Vector.map schemaRaw (QSschemaSchemas qsSchema))
                         Ridx)); eauto.
  Qed.
  Next Obligation.
    unfold MutationPreservesTupleConstraints,
    SatisfiesTupleConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ith2 (rawRels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (tupleConstraints
       (Vector.nth (Vector.map schemaRaw (QSschemaSchemas qsSchema)) Ridx)); eauto.
  Qed.
  Next Obligation.
    unfold MutationPreservesCrossConstraints,
    SatisfiesCrossRelationConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation, UpdateRelation in *.
    case_eq (BuildQueryStructureConstraints qsSchema idx idx'); eauto.
    destruct (fin_eq_dec Ridx idx'); subst; intros.
    - rewrite ith_replace2_Index_eq; simpl.
      rewrite ith_replace2_Index_neq in H1; eauto.
      generalize (fun c => CrossConstr' c idx H0).
      rewrite H; intros H'; eapply H'; eauto.
      eapply (Iterate_Ensemble_filter_neq
                (fun Ridx' =>
                   forall tup' : IndexedRawTuple,
                     GetUnConstrRelation (DropQSConstraints qs) Ridx' tup' ->
                     match BuildQueryStructureConstraints qsSchema Ridx' idx' with
                       | Some CrossConstr => CrossConstr (indexedElement tup') (GetRelation qs idx')
                       | None => True
                     end)).
      intros; generalize (crossConstr qs idx0 idx').
      rewrite GetRelDropConstraints in H3.
      destruct (BuildQueryStructureConstraints qsSchema idx0 idx');
        eauto.
    - rewrite ith_replace2_Index_neq; eauto using string_dec.
      destruct (fin_eq_dec Ridx idx); subst.
      + rewrite ith_replace2_Index_eq in H1; simpl in *; eauto.
      generalize (fun c => CrossConstr c idx' (not_eq_sym n) _ H1).
      rewrite H; intros H'; eapply H'; eauto.
      eapply (Iterate_Ensemble_filter_neq
                (fun Ridx' =>
                   forall tup' : IndexedRawTuple,
                     GetUnConstrRelation (DropQSConstraints qs) idx tup' ->
                     match BuildQueryStructureConstraints qsSchema idx Ridx' with
                       | Some CrossConstr => CrossConstr (indexedElement tup') (GetRelation qs Ridx')
                       | None => True
                     end)); intros.
      destruct (fin_eq_dec idx0 idx); subst; try congruence.
      case_eq (BuildQueryStructureConstraints qsSchema idx idx0); intros; eauto.
      pose (crossConstr qs idx idx0) as crossConstr'; rewrite H4 in crossConstr'.
      eapply crossConstr'; eauto.
      unfold GetUnConstrRelation, DropQSConstraints in H3.
      rewrite <- ith_imap2 in H3; eauto.
      + rewrite ith_replace2_Index_neq in H1; eauto using string_dec.
        pose (crossConstr qs idx idx') as crossConstr'; rewrite H in crossConstr';
        eapply crossConstr'; eauto.
  Qed.

  Lemma QSMutateSpec_refine :
    forall (qsSchema : QueryStructureSchema)
           (qs : QueryStructure qsSchema)
           Ridx (MutatedTuples : IndexedEnsemble ),
      refine
        (Pick (QSMutateSpec qs Ridx MutatedTuples))
        (attributeConstr <- {b |
                       (forall tup,
                          GetRelation qs Ridx tup
                          -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                       -> decides b
                                  (MutationPreservesAttributeConstraints
                                     MutatedTuples
                                     (SatisfiesAttributeConstraints Ridx))};
         tupleConstr <- {b |
                         (forall tup tup',
                            elementIndex tup <> elementIndex tup'
                            -> GetRelation qs Ridx tup
                            -> GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))
                         -> decides b
                               (MutationPreservesTupleConstraints
                                  MutatedTuples
                                  (SatisfiesTupleConstraints Ridx))};
         crossConstr <- {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetRelation qs Ridx') tup'
                              -> SatisfiesCrossRelationConstraints
                                   Ridx' Ridx (indexedElement tup') (GetRelation qs Ridx))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      (GetRelation qs Ridx')
                                      MutatedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx))};
         crossConstr' <- {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetRelation qs Ridx) tup'
                              -> SatisfiesCrossRelationConstraints
                                   Ridx Ridx' (indexedElement tup') (GetRelation qs Ridx'))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      MutatedTuples
                                      (GetRelation qs Ridx')
                                      (SatisfiesCrossRelationConstraints Ridx Ridx'))};
         match attributeConstr, tupleConstr, crossConstr, crossConstr' with
           | true, true, true, true =>
             {qs' |
              (forall Ridx',
                 Ridx <> Ridx' ->
                 GetRelation qs Ridx' =
                 GetRelation qs' Ridx')
              /\ forall t,
                   GetRelation qs' Ridx t <-> MutatedTuples t
             }

           | _, _, _, _ => ret qs
         end).
  Proof.
    intros qsSchema qs Ridx MutatedTuples v Comp_v.
    computes_to_inv.
    assert (decides v0
                      (MutationPreservesAttributeConstraints
                         MutatedTuples
                       (SatisfiesAttributeConstraints Ridx)))
      as H0' by
          (apply Comp_v; intros;
           unfold SatisfiesAttributeConstraints, QSGetNRelSchema, GetNRelSchema;
           pose proof (rawAttrconstr ((ith2 (rawRels qs) Ridx))) as H';
           destruct (attrConstraints (Vector.nth (qschemaSchemas qsSchema) Ridx));
           [apply H' | ]; eauto); clear Comp_v.
    assert (decides v1
                    (MutationPreservesTupleConstraints
                       MutatedTuples
                       (SatisfiesTupleConstraints Ridx)))
      as H1'
        by
          (apply Comp_v';
           unfold SatisfiesTupleConstraints, QSGetNRelSchema, GetNRelSchema;
           pose proof (rawTupleconstr ((ith2 (rawRels qs) Ridx))) as H';
           destruct (tupleConstraints (Vector.nth (qschemaSchemas qsSchema) Ridx));
           [apply H' | ]; eauto); clear Comp_v'.
    assert (decides v2
                    (forall Ridx',
                       Ridx' <> Ridx ->
                       MutationPreservesCrossConstraints
                         (GetRelation qs Ridx')
                         MutatedTuples
                         (SatisfiesCrossRelationConstraints Ridx' Ridx)))
      as H2' by
          (apply Comp_v''; intros;
           pose proof (crossConstr qs Ridx' Ridx);
           unfold SatisfiesCrossRelationConstraints; simpl;
           destruct (BuildQueryStructureConstraints qsSchema Ridx' Ridx); eauto); clear Comp_v''.

    assert (decides v3
                    (forall Ridx',
                       Ridx' <> Ridx ->
                       MutationPreservesCrossConstraints
                         MutatedTuples
                         (GetRelation qs Ridx')
                         (SatisfiesCrossRelationConstraints Ridx Ridx')))
      as H3' by
          (apply Comp_v'''; intros;
           pose proof (crossConstr qs Ridx Ridx');
           unfold SatisfiesCrossRelationConstraints; simpl;
           destruct (BuildQueryStructureConstraints qsSchema Ridx Ridx'); eauto); clear Comp_v'''.

    destruct v0; destruct v1; destruct v2; destruct v3;
    try solve
        [computes_to_econstructor; computes_to_inv; subst; unfold QSMutateSpec; simpl in *; right; subst; intuition].
    computes_to_inv; subst;
    computes_to_econstructor; unfold QSMutateSpec; simpl in *; left; intuition eauto.
    - rewrite <- H; eauto.
    - rewrite <- H; eauto.
    - unfold Same_set, Included, In; eauto; intuition; eapply H0; eauto.
    - rewrite H; intuition.
  Qed.

  Lemma QSMutateSpec_UnConstr_refine' :
    forall qsSchema qs Ridx or MutatedTuples,
      @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        {or' | QSMutateSpec or Ridx MutatedTuples or'}
        (attributeConstr <- {b |
                             (forall tup,
                                GetUnConstrRelation qs Ridx tup
                                -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                             -> decides b
                                        (MutationPreservesAttributeConstraints
                                           MutatedTuples
                                           (SatisfiesAttributeConstraints Ridx))};
         tupleConstr <- {b |
                         (forall tup tup',
                            elementIndex tup <> elementIndex tup'
                            -> GetUnConstrRelation qs Ridx tup
                            -> GetUnConstrRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))
                       -> decides b
                               (MutationPreservesTupleConstraints
                                  MutatedTuples
                                  (SatisfiesTupleConstraints Ridx))};
         crossConstr <- {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetUnConstrRelation qs Ridx') tup'
                              -> SatisfiesCrossRelationConstraints
                                   Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      (GetUnConstrRelation qs Ridx')
                                      MutatedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx))};
         crossConstr' <- {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetUnConstrRelation qs Ridx tup')
                              -> SatisfiesCrossRelationConstraints
                                   Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      MutatedTuples
                                      (GetUnConstrRelation qs Ridx')
                                      (SatisfiesCrossRelationConstraints Ridx Ridx'))};
         match attributeConstr, tupleConstr, crossConstr, crossConstr' with
           | true, true, true, true =>
             {or' | DropQSConstraints_AbsR or' (UpdateUnConstrRelation qs Ridx MutatedTuples)}
           | _, _, _, _ => ret or
         end).
  Proof.
    unfold DropQSConstraints_AbsR; intros; subst.
    setoid_rewrite QSMutateSpec_refine.
    repeat setoid_rewrite refineEquiv_bind_bind.
    rewrite !GetRelDropConstraints.
    f_equiv; unfold pointwise_relation; intros.
    f_equiv; unfold pointwise_relation; intros.
    f_equiv; unfold pointwise_relation; intros.
    { intros v Comp_v; subst; computes_to_inv;
      unfold decides, If_Then_Else in *; find_if_inside; intros; computes_to_econstructor; intros.
      - rewrite <- GetRelDropConstraints in *; eapply Comp_v; intros; eauto;
        eapply H; eauto; rewrite <- GetRelDropConstraints; eauto.
      - unfold not; intros; eapply Comp_v; intros.
        + eapply H; eauto; rewrite <- GetRelDropConstraints; eauto.
        + rewrite GetRelDropConstraints; eauto.
    }
    f_equiv; unfold pointwise_relation; intros.
    { intros v Comp_v; subst; computes_to_inv;
      unfold decides, If_Then_Else in *; find_if_inside; intros; computes_to_econstructor; intros.
      - rewrite <- GetRelDropConstraints in *; eapply Comp_v; intros; eauto.
        rewrite GetRelDropConstraints; eapply H; eauto.
      - unfold not; intros; eapply Comp_v; intros.
        + rewrite GetRelDropConstraints; eauto.
        + rewrite GetRelDropConstraints; eauto.
    }
    repeat find_if_inside; try reflexivity.
    intros v Comp_v; computes_to_inv; subst; computes_to_econstructor;
    simpl.
    rewrite <- GetRelDropConstraints;
      setoid_rewrite <- GetRelDropConstraints; subst; rewrite Comp_v;
      split; intros;
      unfold GetUnConstrRelation, DropQSConstraints, UpdateUnConstrRelation.
    rewrite ith_replace2_Index_neq;
    eauto using string_dec.
    rewrite ith_replace2_Index_eq;
    intuition.
  Qed.

  Lemma ComplementIntersection {A} :
    forall (ens : Ensemble A) (a : A),
      ~ In _ (Intersection A ens (Complement A ens)) a.
  Proof.
    unfold In, not; intros; inversion H; subst.
    unfold Complement, In in *; tauto.
  Qed.

  Corollary ComplementIntersectionIndexedList {heading}
  : forall (ens : Ensemble (@IndexedRawTuple heading)),
      UnIndexedEnsembleListEquivalence
        (Intersection IndexedRawTuple ens
                      (Complement IndexedRawTuple ens))
        [].

  Proof.
    unfold UnIndexedEnsembleListEquivalence.
    exists (@nil (@IndexedRawTuple heading)); simpl; intuition.
    - exfalso; eapply ComplementIntersection; eauto.
    - constructor.
  Qed.

    Lemma ibound_check_dec {n} :
    forall b a,
            (fun idx =>
             if fin_eq_dec (m := n) b idx then false else true) a = true <->
            (fun idx => b <> idx) a.
  Proof.
    intros; simpl; find_if_inside; intuition.
  Qed.

  Lemma refine_Iterate_MutationPreservesCrossConstraints
  : forall qsSchema qs Ridx MutatedTuples or,
      @DropQSConstraints_AbsR qsSchema or qs
      ->
    ((forall Ridx',
     Ridx' <> Ridx ->
     forall tup' : IndexedRawTuple,
     GetRelation or Ridx tup' ->
     SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup')
       (GetUnConstrRelation (DropQSConstraints or) Ridx')) ->
    forall Ridx',
    Ridx' <> Ridx ->
    MutationPreservesCrossConstraints MutatedTuples
      (GetUnConstrRelation (DropQSConstraints or) Ridx')
      (SatisfiesCrossRelationConstraints Ridx Ridx')) ->
   Iterate_Ensemble_BoundedIndex_filter
     (fun Ridx' =>
      forall tup' : IndexedRawTuple,
      GetUnConstrRelation (DropQSConstraints or) Ridx tup' ->
      SatisfiesCrossRelationConstraints Ridx Ridx'
                                        (indexedElement tup') (GetRelation or Ridx'))
     (fun idx => if fin_eq_dec Ridx idx then false else true) ->
   forall Ridx',
   Ridx' <> Ridx ->
   MutationPreservesCrossConstraints
     MutatedTuples (GetRelation or Ridx')
     (SatisfiesCrossRelationConstraints Ridx Ridx').
  Proof.
    intros; rewrite <- GetRelDropConstraints in *; eapply H0; eauto.
    intros; rewrite GetRelDropConstraints in *.
    intros; eapply (proj1 (Iterate_Ensemble_BoundedIndex_filter_equiv
                          _
                          (Build_DecideableEnsemble _ _ (ibound_check_dec _) )) H1); 
    try rewrite GetRelDropConstraints; eauto.
  Qed.

  Lemma refine_Iterate_MutationPreservesCrossConstraints'
  : forall qsSchema qs Ridx MutatedTuples or,
      @DropQSConstraints_AbsR qsSchema or qs
      ->
    ((forall Ridx' ,
     Ridx' <> Ridx ->
     forall tup' : IndexedRawTuple,
       GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
     SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
       (GetRelation or Ridx)) ->
    forall Ridx' ,
    Ridx' <> Ridx ->
    MutationPreservesCrossConstraints
      (GetUnConstrRelation (DropQSConstraints or) Ridx')
      MutatedTuples
      (SatisfiesCrossRelationConstraints Ridx' Ridx)) ->
      Iterate_Ensemble_BoundedIndex_filter
        (fun Ridx' =>
           forall tup' : IndexedRawTuple,
             GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
             SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
                                               (GetRelation or Ridx))
        (fun idx => if fin_eq_dec Ridx idx then false else true) ->
  forall Ridx',
  Ridx' <> Ridx ->
  MutationPreservesCrossConstraints (GetRelation or Ridx') MutatedTuples
                                    (SatisfiesCrossRelationConstraints Ridx' Ridx).
    intros; rewrite <- GetRelDropConstraints in *; eapply H0; eauto.
    intros; eapply (proj1 (Iterate_Ensemble_BoundedIndex_filter_equiv
                             _
                             (Build_DecideableEnsemble _ _ (ibound_check_dec _) )) H1); eauto.
  Qed.

  Lemma QSMutateSpec_UnConstr_refine :
    forall qsSchema qs Ridx MutatedTuples or
           refined_attrConstr refined_tupleConstr
           refined_crossConstr refined_crossConstr',
      @DropQSConstraints_AbsR qsSchema or qs
      -> refine {b | (forall tup,
                        GetUnConstrRelation qs Ridx tup
                        -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                     ->  decides b (MutationPreservesAttributeConstraints
                                      MutatedTuples
                                      (SatisfiesAttributeConstraints Ridx))}
                refined_attrConstr
      -> refine {b | (forall tup tup',
                        elementIndex tup <> elementIndex tup'
                          -> GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))
                     ->  decides b (MutationPreservesTupleConstraints
                                      MutatedTuples
                                      (SatisfiesTupleConstraints Ridx))}
                refined_tupleConstr
      -> refine {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetUnConstrRelation qs Ridx') tup'
                              -> SatisfiesCrossRelationConstraints
                                   Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      (GetUnConstrRelation qs Ridx')
                                      MutatedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx))}

           (* @Iterate_Decide_Comp_Pre
                           _
                           ((fun Ridx' =>
                               Ridx' <> Ridx
                               -> MutationPreservesCrossConstraints
                                    (GetUnConstrRelation qs Ridx')
                                    MutatedTuples
                                    (SatisfiesCrossRelationConstraints Ridx' Ridx)))
                           (@Iterate_Ensemble_BoundedIndex_filter
                              _ (fun idx =>
                                   if (fin_eq_dec (ibound Ridx) idx)
                                   then false else true)
                              (fun Ridx' =>
                                 forall tup',
                                   (GetUnConstrRelation qs Ridx') tup'
                                   -> SatisfiesCrossRelationConstraints
                                        Ridx' Ridx (indexedElement tup')
                                        (GetUnConstrRelation qs Ridx)))
           *)
                refined_crossConstr
      -> refine {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetUnConstrRelation qs Ridx tup')
                              -> SatisfiesCrossRelationConstraints
                                   Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      MutatedTuples
                                      (GetUnConstrRelation qs Ridx')
                                      (SatisfiesCrossRelationConstraints Ridx Ridx'))}
           (*@Iterate_Decide_Comp_Pre
                           _
                           ((fun Ridx' =>
                               Ridx' <> Ridx
                               -> MutationPreservesCrossConstraints
                                    MutatedTuples
                                    (GetUnConstrRelation qs Ridx')
                                    (SatisfiesCrossRelationConstraints Ridx Ridx')))
                           (@Iterate_Ensemble_BoundedIndex_filter
                              _ (fun idx =>
                                   if (fin_eq_dec (ibound Ridx) idx)
                                   then false else true)
                              (fun Ridx' =>
                                 forall tup',
                                   (GetUnConstrRelation qs Ridx) tup'
                                   -> SatisfiesCrossRelationConstraints
                                        Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx')))
                *)
                refined_crossConstr'
      ->
      refine
        (or' <- QSMutate or Ridx MutatedTuples;
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        (attrConstr <- refined_attrConstr;
         tupleConstr <- refined_tupleConstr;
         crossConstr <- refined_crossConstr;
         crossConstr' <- refined_crossConstr';
            match attrConstr, tupleConstr, crossConstr, crossConstr' with
              | true, true, true, true =>
                mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                     (Intersection _
                                                   (GetRelation or Ridx)
                                                   (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs Ridx MutatedTuples) Ridx))));
              ret (UpdateUnConstrRelation qs Ridx MutatedTuples, mutated)
              | _, _, _, _ => ret (DropQSConstraints or, [])
            end).
  Proof.
    intros; unfold QSMutate; simplify with monad laws.
    setoid_rewrite (@QSMutateSpec_UnConstr_refine' _ qs Ridx); eauto.
    setoid_rewrite <- H0; setoid_rewrite <- H1.
    setoid_rewrite <- H2; setoid_rewrite <- H3.
    simplify with monad laws;
      repeat (eapply refine_under_bind; intros; eauto); eauto.
    repeat find_if_inside;
      try solve
          [simplify with monad laws; refine pick val _;
           [ simplify with monad laws; refine pick val (DropQSConstraints or);
             try simplify with monad laws
           | eauto using ComplementIntersectionIndexedList]; reflexivity
          ].
     computes_to_inv; simpl in *.
    unfold DropQSConstraints_AbsR in *; subst.
    repeat rewrite (fun Ridx => GetRelDropConstraints or Ridx) in *.
    refine pick val
           (Mutate_Valid
              or H4 H5
              (refine_Iterate_MutationPreservesCrossConstraints (refl_equal _) H7)
              (refine_Iterate_MutationPreservesCrossConstraints' (refl_equal _) H6));
      [ simplify with monad laws
      | unfold Mutate_Valid, DropQSConstraints,
        UpdateRelation, UpdateUnConstrRelation; simpl;
        repeat rewrite imap_replace2_Index by eauto using string_dec;
        simpl; try reflexivity].
    f_equiv.
    - unfold GetRelation, GetUnConstrRelation, Mutate_Valid,
      UpdateRelation, DropQSConstraints, UpdateUnConstrRelation; simpl;
      repeat rewrite ith_replace2_Index_eq; reflexivity.
    - unfold pointwise_relation; intros.
      refine pick val _;
        [ simplify with monad laws; reflexivity
        | unfold GetRelation, GetUnConstrRelation, Mutate_Valid,
          UpdateRelation, DropQSConstraints, UpdateUnConstrRelation; simpl;
          rewrite imap_replace2_Index by eauto using string_dec; try reflexivity ].
  Qed.

  Local Transparent QSMutate.

  Lemma refine_SatisfiesAttributeConstraintsMutate
  : forall qsSchema qs Ridx MutatedTuples,
      refine
        {b | (forall tup,
                GetUnConstrRelation qs Ridx tup
                -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                     -> decides b (MutationPreservesAttributeConstraints
                                     MutatedTuples
                                     (SatisfiesAttributeConstraints Ridx))}
        match attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx) with
          | Some Constr =>
            {b | (forall tup,
                          GetUnConstrRelation qs Ridx tup
                          -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                 -> decides b (MutationPreservesAttributeConstraints
                                 MutatedTuples
                                 (SatisfiesAttributeConstraints Ridx)) }
          | None => ret true
        end.
  Proof.
    intros; unfold MutationPreservesAttributeConstraints, SatisfiesAttributeConstraints.
    destruct (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)); try reflexivity.
    intros v Comp_v; computes_to_econstructor; computes_to_inv; subst.
    simpl; tauto.
  Qed.

  Lemma refine_SatisfiesTupleConstraintsMutate
  : forall qsSchema qs Ridx MutatedTuples,
      refine
        {b | (forall tup tup',
                elementIndex tup <> elementIndex tup'
                -> GetUnConstrRelation qs Ridx tup
                -> GetUnConstrRelation qs Ridx tup'
                -> SatisfiesTupleConstraints Ridx (indexedElement tup)
                                             (indexedElement tup'))
                     -> decides b (MutationPreservesTupleConstraints
                                     MutatedTuples
                                     (SatisfiesTupleConstraints Ridx))}
        match tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx) with
          | Some Constr =>
            {b | (forall tup tup',
                    elementIndex tup <> elementIndex tup'
                    -> GetUnConstrRelation qs Ridx tup
                    -> GetUnConstrRelation qs Ridx tup'
                    -> Constr (indexedElement tup)
                                                 (indexedElement tup'))
                 -> decides b
                            (MutationPreservesTupleConstraints
                               MutatedTuples
                               Constr) }
          | None => ret true
        end.
  Proof.
    intros; unfold MutationPreservesTupleConstraints, SatisfiesTupleConstraints;
    destruct (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)); try reflexivity.
    intros v Comp_v; computes_to_econstructor;  computes_to_inv; subst;
    econstructor;  computes_to_inv; subst; simpl; tauto.
  Qed.

  Lemma refine_SatisfiesCrossConstraintsMutate
  : forall  qsSchema qs Ridx MutatedTuples,
      refine
        {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetUnConstrRelation qs Ridx') tup'
                              -> SatisfiesCrossRelationConstraints
                                   Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      (GetUnConstrRelation qs Ridx')
                                      MutatedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx))}
        (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              (
                                                (MutationPreservesCrossConstraints
                                                   (GetUnConstrRelation qs Ridx')
                                                   MutatedTuples
                                                   CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                                     (fun idx =>
                                        if (fin_eq_dec Ridx idx)
                                        then false else true)
        )).
  Proof.
    intros; simpl.
    unfold MutationPreservesCrossConstraints.
    setoid_rewrite <- refine_Iterate_Decide_Comp_Pre.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex_Pre.
    eapply refine_Iterate_Decide_Comp_equiv_Pre; eauto using string_dec.
    - unfold SatisfiesCrossRelationConstraints; intros.
      destruct (fin_eq_dec Ridx idx);
        [congruence
        | destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto].
    - unfold not; intros; eapply H.
      unfold SatisfiesCrossRelationConstraints in *.
      destruct (fin_eq_dec Ridx idx);
      [ eauto
      | destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto].
    - setoid_rewrite <- Iterate_Ensemble_filter_neq; eauto using string_dec.
  Qed.

  Lemma refine_SatisfiesCrossConstraintsMutate'
  : forall   qsSchema qs Ridx MutatedTuples,
      refine
        {b |
         (forall Ridx',
             Ridx' <> Ridx ->
             forall tup',
               (GetUnConstrRelation qs Ridx tup')
               -> SatisfiesCrossRelationConstraints
                    Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
         -> decides
              b
              (forall Ridx',
                  Ridx' <> Ridx
                  -> MutationPreservesCrossConstraints
                       MutatedTuples
                       (GetUnConstrRelation qs Ridx')
                       (SatisfiesCrossRelationConstraints Ridx Ridx'))}
        (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx
                                                                         Ridx'
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              (
                                                (MutationPreservesCrossConstraints
                                                   MutatedTuples
                                                   (GetUnConstrRelation qs Ridx')
                                                   CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx) tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                                     (fun idx =>
                                        if (fin_eq_dec Ridx idx)
                                        then false else true)
        )).
  Proof.
    intros; simpl.
    unfold MutationPreservesCrossConstraints.
    setoid_rewrite <- refine_Iterate_Decide_Comp_Pre.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex_Pre.
    eapply refine_Iterate_Decide_Comp_equiv_Pre; eauto using string_dec.
    - unfold SatisfiesCrossRelationConstraints; intros.
      destruct (fin_eq_dec Ridx idx);
        [congruence
        | destruct (BuildQueryStructureConstraints qsSchema Ridx idx); eauto].
    - unfold not; intros; eapply H.
      unfold SatisfiesCrossRelationConstraints in *.
      destruct (fin_eq_dec Ridx idx);
      [ eauto
      | destruct (BuildQueryStructureConstraints qsSchema Ridx idx); eauto].
    - setoid_rewrite <- Iterate_Ensemble_filter_neq; eauto using string_dec.
  Qed.

  Definition UpdateUnConstrRelationMutateC {qsSchema} (qs : UnConstrQueryStructure qsSchema) Ridx MutatedTuples :=
    ret (UpdateUnConstrRelation qs Ridx MutatedTuples).

  Lemma QSMutateSpec_refine_subgoals' ResultT :
    forall qsSchema (qs : QueryStructure qsSchema) qs' Ridx
           default success refined_schConstr_self
           refined_schConstr refined_qsConstr refined_qsConstr'
           MutatedTuples
           (k : _ -> Comp ResultT),
      DropQSConstraints_AbsR qs qs'
      -> refine {b | (forall tup,
                         GetUnConstrRelation qs' Ridx tup
                         -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                     ->  decides b (MutationPreservesAttributeConstraints
                                      MutatedTuples
                                      (SatisfiesAttributeConstraints Ridx))}
                refined_schConstr_self
      -> refine {b | (forall tup tup',
                        elementIndex tup <> elementIndex tup'
                          -> GetUnConstrRelation qs' Ridx tup
                          -> GetUnConstrRelation qs' Ridx tup'
                          -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))
                     ->  decides b (MutationPreservesTupleConstraints
                                      MutatedTuples
                                      (SatisfiesTupleConstraints Ridx))}
                refined_schConstr
      -> refine {b |
                         (forall Ridx',
                            Ridx' <> Ridx ->
                            forall tup',
                              (GetUnConstrRelation qs' Ridx') tup'
                              -> SatisfiesCrossRelationConstraints
                                   Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs' Ridx))
                         -> decides
                              b
                              (forall Ridx',
                                 Ridx' <> Ridx
                                 -> MutationPreservesCrossConstraints
                                      (GetUnConstrRelation qs' Ridx')
                                      MutatedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx))}
                refined_qsConstr
      -> refine         {b |
         (forall Ridx',
             Ridx' <> Ridx ->
             forall tup',
               (GetUnConstrRelation qs' Ridx tup')
               -> SatisfiesCrossRelationConstraints
                    Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs' Ridx'))
         -> decides
              b
              (forall Ridx',
                  Ridx' <> Ridx
                  -> MutationPreservesCrossConstraints
                       MutatedTuples
                       (GetUnConstrRelation qs' Ridx')
                       (SatisfiesCrossRelationConstraints Ridx Ridx'))}
                        refined_qsConstr'
      -> (forall qs'' qs''' mutated,
             DropQSConstraints_AbsR qs'' qs'''
             -> (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs'' Ridx')
             -> (forall t,
                    GetRelation qs'' Ridx t <-> MutatedTuples t)
             -> UnIndexedEnsembleListEquivalence
                                    (Intersection _
                                                  (GetRelation qs Ridx)
                                                  (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs' Ridx MutatedTuples) Ridx))) mutated
             -> refine (k (qs'', mutated))
                       (success qs''' mutated))
      -> refine (k (qs, [ ])) default
      -> refine
           (qs' <- QSMutate qs Ridx MutatedTuples; k qs')
           (schConstr_self <- refined_schConstr_self;
             schConstr <- refined_schConstr;
             qsConstr <- refined_qsConstr;
             qsConstr' <- refined_qsConstr';
             match schConstr_self, schConstr, qsConstr, qsConstr' with
             | true, true, true, true =>
               mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                    (Intersection _
                                                  (GetRelation qs Ridx)
                                                  (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs' Ridx MutatedTuples) Ridx))));
                 qs'' <- UpdateUnConstrRelationMutateC qs' Ridx MutatedTuples;
                 success qs'' mutated
             | _, _, _, _ => default
             end).
  Proof.
    intros.
    unfold QSMutate.
    simplify with monad laws.
    setoid_rewrite QSMutateSpec_refine.
    simplify with monad laws.
    apply refine_under_bind_both.
    rewrite <- H0, <- H, (GetRelDropConstraints qs); reflexivity.
    rewrite <- !GetRelDropConstraints; rewrite !H.
    intros; repeat (apply refine_under_bind_both;
            [repeat rewrite <- (GetRelDropConstraints qs); eauto
            | intros]).
    - computes_to_inv; eauto.
      rewrite <- H2.
      intros v Comp_v; computes_to_inv; computes_to_econstructor; intros.
      setoid_rewrite <- GetRelDropConstraints; rewrite H.
      eapply Comp_v; intros; eapply H8; eauto.
      rewrite <- GetRelDropConstraints, H; eauto.
    - computes_to_inv; eauto.
      rewrite <- H3.
      intros v Comp_v; computes_to_inv; computes_to_econstructor; intros.
      setoid_rewrite <- GetRelDropConstraints; rewrite H.
      eapply Comp_v; intros.
      rewrite <- H, GetRelDropConstraints; eapply H9; eauto.
    - repeat find_if_inside; try simplify with monad laws;
      try solve [rewrite refine_SuccessfulInsert_Bind; eauto].
      +  computes_to_inv; simpl in *.
         assert (Iterate_Ensemble_BoundedIndex_filter
                   (fun Ridx' : Fin.t (numRawQSschemaSchemas qsSchema) =>
                      forall tup' : IndexedRawTuple,
                        GetUnConstrRelation (DropQSConstraints qs) Ridx' tup' ->
                        SatisfiesCrossRelationConstraints Ridx' Ridx
                                                          (indexedElement tup') (GetRelation qs Ridx))
                   (fun idx : Fin.t (numRawQSschemaSchemas qsSchema) =>
                      if fin_eq_dec Ridx idx then false else true) ->
                 forall Ridx' : Fin.t (numRawQSschemaSchemas qsSchema),
                   Ridx' <> Ridx ->
                   MutationPreservesCrossConstraints (GetRelation qs Ridx') MutatedTuples
                                                     (SatisfiesCrossRelationConstraints Ridx' Ridx))
           as H8' by
               (intros; eapply H8; intros; eauto;
         rewrite <- H, GetRelDropConstraints;
         rewrite <- GetRelDropConstraints, H in H13;
         intros; eapply (proj1 (Iterate_Ensemble_BoundedIndex_filter_equiv
                                  _
                                  (Build_DecideableEnsemble _ _ (ibound_check_dec _) )) H10); eauto;
         rewrite H; eauto).
         assert (Iterate_Ensemble_BoundedIndex_filter
                   (fun Ridx' : Fin.t (numRawQSschemaSchemas qsSchema) =>
                      forall tup' : IndexedRawTuple,
                        GetUnConstrRelation (DropQSConstraints qs) Ridx tup' ->
                        SatisfiesCrossRelationConstraints (qsSchema := qsSchema) Ridx Ridx'
                                                          (indexedElement tup') (GetRelation qs Ridx'))
                   (fun idx : Fin.t (numRawQSschemaSchemas qsSchema) =>
                      if fin_eq_dec Ridx idx then false else true) ->
                 forall Ridx' : Fin.t (numRawQSschemaSchemas qsSchema),
                   Ridx' <> Ridx ->
                   MutationPreservesCrossConstraints MutatedTuples
                                                     (GetRelation qs Ridx') (SatisfiesCrossRelationConstraints (qsSchema := qsSchema) Ridx Ridx')) as H9' by
               (intros; eapply H9; intros; eauto;
                intros; eapply (proj1 (Iterate_Ensemble_BoundedIndex_filter_equiv
                                         _
                                         (Build_DecideableEnsemble _ _ (ibound_check_dec _) )) H10); eauto;
                rewrite H; eauto).
         assert ((forall tup tup' : IndexedRawTuple,
                     elementIndex tup <> elementIndex tup' ->
                     GetRelation qs Ridx tup ->
                     GetRelation qs Ridx tup' ->
                     SatisfiesTupleConstraints (qsSchema := qsSchema) Ridx (indexedElement tup) (indexedElement tup')) ->
                 MutationPreservesTupleConstraints MutatedTuples
                                                   (SatisfiesTupleConstraints (qsSchema := qsSchema) Ridx))
           as H7' by
               (intros; eapply H7; intros; eauto;
                rewrite <- H, GetRelDropConstraints in H12, H13; eauto).
         assert ((forall tup : IndexedRawTuple,
                    GetRelation qs Ridx tup ->
    SatisfiesAttributeConstraints (qsSchema := qsSchema) Ridx (indexedElement tup)) ->
         MutationPreservesAttributeConstraints MutatedTuples
                                               (SatisfiesAttributeConstraints (qsSchema := qsSchema) Ridx)) as H6' by
               (intros; eapply H6; intros; eauto;
                rewrite <- H, GetRelDropConstraints in H11; eauto).
         refine pick val (Mutate_Valid qs (MutatedTuples := MutatedTuples) H6' H7' H9' H8').
         rewrite <- !H, !GetRelDropConstraints.
         simplify with monad laws.
         eapply refine_under_bind_both.
         unfold Mutate_Valid; simpl.
         unfold UpdateRelation.
         unfold GetRelation; simpl.
         rewrite ilist2.ith_replace2_Index_eq; simpl.
         unfold GetUnConstrRelation, UpdateUnConstrRelation.
         rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
         intros.
         unfold UpdateUnConstrRelationMutateC; rewrite refineEquiv_bind_unit.
         eapply H4.
         unfold DropQSConstraints_AbsR, DropQSConstraints, Mutate_Valid; simpl.
         unfold UpdateRelation.
         rewrite ilist2.imap_replace2_Index; simpl; reflexivity.
         intros; unfold Mutate_Valid, GetRelation, UpdateRelation; simpl.
         rewrite ilist2.ith_replace2_Index_neq; simpl; eauto.
         intros; unfold Mutate_Valid, GetRelation, UpdateRelation; simpl.
         rewrite ilist2.ith_replace2_Index_eq; simpl; eauto.
         reflexivity.
         apply Pick_inv in H10.
         revert H10.
         unfold Mutate_Valid, GetRelation, UpdateRelation; simpl.
         rewrite ilist2.ith_replace2_Index_eq; simpl; eauto.
         unfold GetUnConstrRelation, UpdateUnConstrRelation.
         rewrite ilist2.ith_replace2_Index_eq; simpl; eauto.
         split.
         unfold Mutate_Valid, GetRelation, UpdateRelation; simpl.
         intros; rewrite ilist2.ith_replace2_Index_neq; simpl; eauto.
         unfold Mutate_Valid, GetRelation, UpdateRelation; simpl.
         intros; rewrite ilist2.ith_replace2_Index_eq; simpl; eauto.
         reflexivity.
      + refine pick val _.
        simplify with monad laws; eauto.
        rewrite <- H, GetRelDropConstraints.
        eapply ComplementIntersectionIndexedList.
      + refine pick val _.
        simplify with monad laws; eauto.
        rewrite <- H, GetRelDropConstraints.
        eapply ComplementIntersectionIndexedList.
      + refine pick val _.
        simplify with monad laws; eauto.
        rewrite <- H, GetRelDropConstraints.
        eapply ComplementIntersectionIndexedList.
      + refine pick val _.
        simplify with monad laws; eauto.
        rewrite <- H, GetRelDropConstraints.
        eapply ComplementIntersectionIndexedList.
  Qed.

  Lemma QSMutateSpec_refine_subgoals ResultT :
    forall qsSchema (qs : QueryStructure qsSchema) qs' Ridx
           default success refined_schConstr_self
           refined_schConstr refined_qsConstr refined_qsConstr'
           MutatedTuples
           (k : _ -> Comp ResultT),
      DropQSConstraints_AbsR qs qs'
      -> refine match attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx) with
                | Some Constr =>
                  {b | (forall tup,
                           GetUnConstrRelation qs' Ridx tup
                           -> SatisfiesAttributeConstraints Ridx (indexedElement tup))
                       -> decides b (MutationPreservesAttributeConstraints
                                       MutatedTuples
                                       (SatisfiesAttributeConstraints Ridx)) }
                | None => ret true
                end
                refined_schConstr_self
      -> refine match tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx) with
                | Some Constr =>
                  {b | (forall tup tup',
                           elementIndex tup <> elementIndex tup'
                           -> GetUnConstrRelation qs' Ridx tup
                           -> GetUnConstrRelation qs' Ridx tup'
                           -> Constr (indexedElement tup)
                                                        (indexedElement tup'))
                       -> decides b
                                  (MutationPreservesTupleConstraints
                                     MutatedTuples
                                     Constr) }
                | None => ret true
                end
                refined_schConstr
      -> refine (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              (
                                                (MutationPreservesCrossConstraints
                                                   (GetUnConstrRelation qs' Ridx')
                                                   MutatedTuples
                                                   CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs' Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs' Ridx))
                                     (fun idx =>
                                        if (fin_eq_dec Ridx idx)
                                        then false else true)
                )) refined_qsConstr
      -> refine (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx
                                                                         Ridx'
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              (
                                                (MutationPreservesCrossConstraints
                                                   MutatedTuples
                                                   (GetUnConstrRelation qs' Ridx')
                                                   CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs' Ridx) tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs' Ridx'))
                                     (fun idx =>
                                        if (fin_eq_dec Ridx idx)
                                        then false else true)
        ))
                refined_qsConstr'
      -> (forall qs'' qs''' mutated,
             DropQSConstraints_AbsR qs'' qs'''
             -> (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs'' Ridx')
             -> (forall t,
                    GetRelation qs'' Ridx t <-> MutatedTuples t)
             -> UnIndexedEnsembleListEquivalence
                                    (Intersection _
                                                  (GetRelation qs Ridx)
                                                  (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs' Ridx MutatedTuples) Ridx))) mutated
             -> refine (k (qs'', mutated))
                       (success qs''' mutated))
      -> refine (k (qs, [ ])) default
      -> refine
           (qs' <- QSMutate qs Ridx MutatedTuples; k qs')
           (schConstr_self <- refined_schConstr_self;
             schConstr <- refined_schConstr;
             qsConstr <- refined_qsConstr;
             qsConstr' <- refined_qsConstr';
             match schConstr_self, schConstr, qsConstr, qsConstr' with
             | true, true, true, true =>
               mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                    (Intersection _
                                                  (GetRelation qs Ridx)
                                                  (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs' Ridx MutatedTuples) Ridx))));
                 qs'' <- UpdateUnConstrRelationMutateC qs' Ridx MutatedTuples;
                 success qs'' mutated
             | _, _, _, _ => default
             end).
  Proof.
    intros; rewrite QSMutateSpec_refine_subgoals'; eauto; f_equiv.
    rewrite refine_SatisfiesAttributeConstraintsMutate; eauto.
    rewrite refine_SatisfiesTupleConstraintsMutate; eauto.
    rewrite refine_SatisfiesCrossConstraintsMutate; eauto.
    rewrite refine_SatisfiesCrossConstraintsMutate'; eauto.
  Qed.

  Lemma QSMutateSpec_UnConstr_refine_opt :
    forall qsSchema qs Ridx MutatedTuples or,
      @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        (or' <- QSMutate or Ridx MutatedTuples;
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        match (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)),
              (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)) with
          | Some aConstr, Some tConstr =>
            attrConstr <- {b | (forall tup,
                                  GetUnConstrRelation qs Ridx tup
                                  -> aConstr (indexedElement tup))
                                  -> decides b (MutationPreservesAttributeConstraints
                                                  MutatedTuples
                                                  aConstr) };
              tupleConstr <- {b | (forall tup tup',
                                     elementIndex tup <> elementIndex tup'
                                     -> GetUnConstrRelation qs Ridx tup
                                     -> GetUnConstrRelation qs Ridx tup'
                                     -> tConstr (indexedElement tup) (indexedElement tup'))
                                  -> decides b (MutationPreservesTupleConstraints
                                                  MutatedTuples
                                                  tConstr) };
              crossConstr <- (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' => if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                     (GetUnConstrRelation qs Ridx')
                                                     MutatedTuples
                                                 CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                                     (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              crossConstr' <- (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx
                                                                         Ridx'
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                  MutatedTuples
                                                  (GetUnConstrRelation qs Ridx')
                                                  CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx) tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                                     (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              match attrConstr, tupleConstr, crossConstr, crossConstr' with
                | true, true, true, true =>
                  mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                       (Intersection _
                                                     (GetRelation or Ridx)
                                                     (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs Ridx MutatedTuples) Ridx))));
                    ret (UpdateUnConstrRelation qs Ridx MutatedTuples, mutated)
                | _, _, _, _ => ret (DropQSConstraints or, [])
              end
          | Some aConstr, None =>
            attrConstr <- {b | (forall tup,
                                  GetUnConstrRelation qs Ridx tup
                                  -> aConstr (indexedElement tup))
                               -> decides b (MutationPreservesAttributeConstraints
                                               MutatedTuples
                                               aConstr) };
              crossConstr <- (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                     (GetUnConstrRelation qs Ridx')
                                                     MutatedTuples
                                                 CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                                  (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              crossConstr' <- (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx
                                                                         Ridx'
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                  MutatedTuples
                                                  (GetUnConstrRelation qs Ridx')
                                                  CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx) tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                                     (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              match attrConstr, crossConstr, crossConstr' with
                | true, true, true =>
                  mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                       (Intersection _
                                                     (GetRelation or Ridx)
                                                     (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs Ridx MutatedTuples) Ridx))));
                    ret (UpdateUnConstrRelation qs Ridx MutatedTuples, mutated)
                | _, _, _ => ret (DropQSConstraints or, [])
            end
          | None, Some tConstr =>
              tupleConstr <- {b | (forall tup tup',
                                     elementIndex tup <> elementIndex tup'
                                     -> GetUnConstrRelation qs Ridx tup
                                     -> GetUnConstrRelation qs Ridx tup'
                                     -> tConstr (indexedElement tup) (indexedElement tup'))
                                  -> decides b (MutationPreservesTupleConstraints
                                                  MutatedTuples
                                                  tConstr) };
              crossConstr <- (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx'  =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                     (GetUnConstrRelation qs Ridx')
                                                     MutatedTuples
                                                 CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                             (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              crossConstr' <- (Iterate_Decide_Comp_opt_Pre _
                                 (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx
                                                                         Ridx'
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                  MutatedTuples
                                                  (GetUnConstrRelation qs Ridx')
                                                  CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx) tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                              (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              match tupleConstr, crossConstr, crossConstr' with
                | true, true, true =>
                  mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                       (Intersection _
                                                     (GetRelation or Ridx)
                                                     (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs Ridx MutatedTuples) Ridx))));
                    ret (UpdateUnConstrRelation qs Ridx MutatedTuples, mutated)
                | _, _, _ => ret (DropQSConstraints or, [])
              end
          | None, None =>
                          crossConstr <- (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                     (GetUnConstrRelation qs Ridx')
                                                     MutatedTuples
                                                 CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))
                                         (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              crossConstr' <- (Iterate_Decide_Comp_opt_Pre _
                                 (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx
                                                                         Ridx'
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((MutationPreservesCrossConstraints
                                                  MutatedTuples
                                                  (GetUnConstrRelation qs Ridx')
                                                  CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx) tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx Ridx' (indexedElement tup') (GetUnConstrRelation qs Ridx'))
                              (fun idx =>
                                          if (fin_eq_dec Ridx idx)
                                          then false else true)));
              match crossConstr, crossConstr' with
                | true, true =>
                  mutated   <- Pick (UnIndexedEnsembleListEquivalence
                                       (Intersection _
                                                     (GetRelation or Ridx)
                                                     (Complement _ (GetUnConstrRelation (UpdateUnConstrRelation qs Ridx MutatedTuples) Ridx))));
                    ret (UpdateUnConstrRelation qs Ridx MutatedTuples, mutated)
                | _, _ => ret (DropQSConstraints or, [])
              end
        end.
  Proof.
    intros; rewrite QSMutateSpec_UnConstr_refine;
    eauto using
          refine_SatisfiesTupleConstraintsMutate,
    refine_SatisfiesAttributeConstraintsMutate,
    refine_SatisfiesCrossConstraintsMutate,
    refine_SatisfiesCrossConstraintsMutate'.
    - unfold SatisfiesTupleConstraints, SatisfiesAttributeConstraints.
      destruct (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)).
      + destruct (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)).
        reflexivity.
        simplify with monad laws; f_equiv.
      + simplify with monad laws; f_equiv.
        destruct (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)).
        reflexivity.
        simplify with monad laws; f_equiv.
  Qed.

End MutateRefinements.
