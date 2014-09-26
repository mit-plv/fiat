Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation Schema QueryStructureSchema
        BuildADTRefinements QueryStructure IndexedEnsembles
        QuerySpecs.QueryQSSpecs QuerySpecs.DeleteQSSpecs
        ConstraintChecksRefinements ListQueryStructureRefinements
        Common.IterateBoundedIndex Common.DecideableEnsembles.

(* Facts about implements delete operations. *)

Section DeleteRefinements.

  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesSchemaConstraints.

  Arguments GetUnConstrRelation : simpl never.
  Arguments UpdateUnConstrRelation : simpl never.
  Arguments replace_BoundedIndex : simpl never.
  Arguments BuildQueryStructureConstraints : simpl never.
  Arguments BuildQueryStructureConstraints' : simpl never.

  Program
    Definition Delete_Valid
    (qsSchema : QueryStructureSchema)
    (qs : QueryStructure qsSchema)
    (Ridx : _)
    (DeletedTuples :
       Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
    (schConstr :
       (forall tup tup' : IndexedTuple,
         GetRelation qs Ridx tup ->
         GetRelation qs Ridx tup' -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup')) ->
         DeletePreservesSchemaConstraints (GetRelation qs Ridx) DeletedTuples
                                          (SatisfiesSchemaConstraints Ridx))
    (* And is compatible with the cross-schema constraints. *)
    (crossConstr' :
       (@Iterate_Ensemble_BoundedIndex_filter
          (map relName (qschemaSchemas qsSchema))
          (fun idx : nat => if eq_nat_dec (ibound Ridx) idx then false else true)
          (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
             forall tup' : IndexedTuple,
               GetUnConstrRelation (DropQSConstraints qs) Ridx' tup' ->
               SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup') (GetRelation qs Ridx))) ->

       (forall Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)),
          (Ridx' <> Ridx) ->
     DeletePreservesCrossConstraints (GetRelation qs Ridx)
       (GetRelation qs Ridx') DeletedTuples
       (SatisfiesCrossRelationConstraints Ridx' Ridx)))
  : QueryStructure qsSchema :=
    {| rels :=
         UpdateRelation _ (rels qs) Ridx {| rel := EnsembleDelete (GetRelation qs Ridx) DeletedTuples|}
    |}.
  Next Obligation.
    unfold GetRelation.
    unfold SatisfiesSchemaConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ith_Bounded _ (rels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (schemaConstraints
                (relSchema (nth_Bounded relName (qschemaSchemas qsSchema) Ridx))); eauto.
    intros; eapply schConstr; eauto.
  Defined.
  Next Obligation.
    generalize (crossConstr qs idx idx') as crossConstr''.
    case_eq (BuildQueryStructureConstraints qsSchema idx idx'); eauto.

    unfold SatisfiesCrossRelationConstraints, UpdateRelation in *;
      destruct (BoundedString_eq_dec Ridx idx'); subst; intros.

    - rewrite ith_replace_BoundIndex_eq; simpl.
      rewrite ith_replace_BoundIndex_neq in H1; eauto using string_dec.
      generalize (fun c => crossConstr' c idx H0).
      rewrite H; intros H'; eapply H'; eauto.
      eapply (Iterate_Ensemble_filter_neq
                string_dec
                _
                (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                   forall tup' : IndexedTuple,
                     GetUnConstrRelation (DropQSConstraints qs) Ridx' tup' ->
                     match BuildQueryStructureConstraints qsSchema Ridx' idx' with
                       | Some CrossConstr => CrossConstr (indexedElement tup') (GetRelation qs idx')
                       | None => True
                     end)).
      intros; generalize (crossConstr qs idx0 idx').
      rewrite GetRelDropConstraints in H3.
      destruct (BuildQueryStructureConstraints qsSchema idx0 idx');
        eauto.
    - rewrite ith_replace_BoundIndex_neq in *; eauto using string_dec.
      destruct (BoundedString_eq_dec Ridx idx); subst.
      + rewrite ith_replace_BoundIndex_eq in H1; simpl in *; eauto.
        unfold EnsembleDelete in H1; destruct H1; subst; eauto.
      + rewrite ith_replace_BoundIndex_neq in H1; eauto using string_dec.
  Qed.

  Lemma QSDeleteSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))),
      refine
        (Pick (QSDeleteSpec {| qsHint := qs |} Ridx DeletedTuples))
        (schConstr <- {b |
                       (forall tup tup',
                          GetRelation qs Ridx tup
                          -> GetRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup'))
                       -> decides b
                               (DeletePreservesSchemaConstraints
                                  (GetRelation qs Ridx)
                                  DeletedTuples
                                  (SatisfiesSchemaConstraints Ridx))};
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
                                 -> DeletePreservesCrossConstraints
                                      (GetRelation qs Ridx)
                                      (GetRelation qs Ridx')
                                      DeletedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx))};
         match schConstr, crossConstr with
           | true, true =>
             {qs' |
              (forall Ridx',
                 Ridx <> Ridx' ->
                 GetRelation qsHint Ridx' =
                 GetRelation qs' Ridx')
              /\ forall t,
                   GetRelation qs' Ridx t <->
                   (EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples t)
             }

           | _, _ => ret qsHint
         end).
  Proof.
    intros qsSchema qs Ridx DeletedTuples v Comp_v.
    do 2 (apply_in_hyp computes_to_inv; destruct_ex; split_and).
    repeat (apply_in_hyp computes_to_inv; destruct_ex; split_and); simpl in *.
    assert (decides x
                    (DeletePreservesSchemaConstraints
                       (GetRelation qs Ridx)
                       DeletedTuples (SatisfiesSchemaConstraints Ridx)))
      as H0'
        by
          (apply H0;
           unfold SatisfiesSchemaConstraints, QSGetNRelSchema, GetNRelSchema;
           pose proof (constr ((ith_Bounded relName (rels qs) Ridx))) as H';
           destruct (schemaConstraints
                       (relSchema (nth_Bounded relName (qschemaSchemas qsSchema) Ridx)));
           [apply H' | ]; eauto); clear H0.
    assert (decides x0
                    (forall Ridx' : BoundedString,
                       Ridx' <> Ridx ->
                       DeletePreservesCrossConstraints
                         (GetRelation qs Ridx)
                         (GetRelation qs Ridx') DeletedTuples
                         (SatisfiesCrossRelationConstraints Ridx' Ridx)))
      as H1' by
          (apply H1; intros;
           pose proof (crossConstr qs Ridx' Ridx);
           unfold SatisfiesCrossRelationConstraints;
           destruct (BuildQueryStructureConstraints qsSchema Ridx' Ridx); eauto); clear H1.
    destruct x; destruct x0;
    try solve
        [econstructor; unfold QSDeleteSpec; intuition; right; subst; intuition].
  Qed.

  Lemma ComplementIntersection {A} :
    forall (ens : Ensemble A) (a : A),
      ~ In _ (Intersection A ens (Complement A ens)) a.
  Proof.
    unfold In, not; intros; inversion H; subst.
    unfold Complement, In in *; tauto.
  Qed.

  Corollary ComplementIntersectionIndexedList {heading}
  : forall (ens : Ensemble (@IndexedTuple heading)),
      UnIndexedEnsembleListEquivalence
        (Intersection IndexedTuple ens
                      (Complement IndexedTuple ens))
        [].

  Proof.
    unfold UnIndexedEnsembleListEquivalence.
    exists (@nil (@IndexedTuple heading)); simpl; intuition.
    unfold EnsembleListEquivalence; intuition.
    - constructor.
    - exfalso; eapply ComplementIntersection; eauto.
  Qed.

  Lemma QSDeleteSpec_UnConstr_refine' :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (or : QueryStructure qsSchema)
           DeletedTuples,
      DropQSConstraints_AbsR or qs ->
      refine
        (or' <- (qs'       <- Pick (QSDeleteSpec {|qsHint := or |} Ridx DeletedTuples);
                 deleted   <- Pick (UnIndexedEnsembleListEquivalence
                                      (Intersection _
                                                    (GetRelation or Ridx)
                                                    (Complement _ (GetRelation qs' Ridx))));
                 ret (qs', deleted));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        (schConstr <- {b |
                       (forall tup tup',
                          GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup'))
                       -> decides b
                               (DeletePreservesSchemaConstraints
                                  (GetUnConstrRelation qs Ridx)
                                  DeletedTuples
                                  (SatisfiesSchemaConstraints Ridx))};
         crossConstr <- (@Iterate_Decide_Comp_Pre
                           _
                           ((fun Ridx' =>
                               Ridx' <> Ridx
                               -> DeletePreservesCrossConstraints
                                    (GetUnConstrRelation qs Ridx)
                                    (GetUnConstrRelation qs Ridx')
                                    DeletedTuples
                                    (SatisfiesCrossRelationConstraints Ridx' Ridx)))
                           (@Iterate_Ensemble_BoundedIndex_filter
                              _ (fun idx =>
                                    if (eq_nat_dec (ibound Ridx) idx)
                                    then false else true)
                              (fun Ridx' =>
                                 forall tup',
                                   (GetUnConstrRelation qs Ridx') tup'
                                   -> SatisfiesCrossRelationConstraints
                                        Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))));
         match schConstr, crossConstr with
           | true, true =>
             deleted   <- Pick (UnIndexedEnsembleListEquivalence
                                  (Intersection _
                                                (GetUnConstrRelation qs Ridx)
                                                (Complement _ (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples))));

           ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
           | _, _ => ret (qs, [])
         end).
  Proof.
    intros.
    setoid_rewrite refineEquiv_pick_eq'.
    unfold DropQSConstraints_AbsR in *; intros; subst.
    rewrite QSDeleteSpec_refine.
    unfold refine; intros; subst.
    do 2 (apply_in_hyp computes_to_inv; destruct_ex; split_and).
    repeat rewrite GetRelDropConstraints in *.
    (* This assert is gross. Need to eliminate them. *)
    assert (
        (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          Ridx' <> Ridx ->
          DeletePreservesCrossConstraints (GetRelation or Ridx)
            (GetUnConstrRelation (DropQSConstraints or) Ridx') DeletedTuples
            (SatisfiesCrossRelationConstraints Ridx' Ridx))
        = fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          Ridx' <> Ridx ->
          DeletePreservesCrossConstraints (GetRelation or Ridx)
            (GetRelation or Ridx') DeletedTuples
            (SatisfiesCrossRelationConstraints Ridx' Ridx))
      as rewriteSat
        by (apply functional_extensionality; intros; repeat rewrite GetRelDropConstraints;
            reflexivity); rewrite rewriteSat in H1; clear rewriteSat.
    (* Resume not-terribleness *)
    generalize (Iterate_Decide_Comp_BoundedIndex_Pre _ _ _ _ H1) as H1'; intros.
    simpl in *; revert H1.
    repeat apply_in_hyp computes_to_inv; destruct_ex;
    intuition; apply_in_hyp computes_to_inv; subst.
    econstructor 2 with
    (comp_a_value := match x as x', x0 as x0'
                           return (_ -> decides x' _) ->
                                  (_ -> decides x0' _) -> _
                     with
                       | true, true =>
                         fun H0 H1 =>
                           (@Delete_Valid _ or Ridx DeletedTuples H0 H1, snd v)
                       | _, _ => fun _ _ => (or, [])
                     end H0 H1').
    econstructor 2 with
    (comp_a_value := match x as x', x0 as x0'
                           return (_ -> decides x' _) ->
                                  (_ -> decides x0' _)  -> _
                     with
                       | true, true =>
                         fun H0 H1 =>
                           @Delete_Valid _ or Ridx DeletedTuples H0 H1
                       | _, _ => fun _ _ => or
                     end H0 H1').
    repeat (econstructor; eauto).
    instantiate (1 := x0); destruct x0; simpl in *; intros; eauto;
    eapply H1'; eauto.
    eapply (Iterate_Ensemble_filter_neq
              string_dec
              _
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                 forall tup' : IndexedTuple,
                   GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
                   match BuildQueryStructureConstraints qsSchema Ridx' Ridx with
                     | Some CrossConstr => CrossConstr (indexedElement tup') (GetRelation or Ridx)
                     | None => True
                   end)).
    intros; eapply H; try rewrite <- GetRelDropConstraints; eauto.
    eapply (Iterate_Ensemble_filter_neq
              string_dec
              _
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                 forall tup' : IndexedTuple,
                   GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
                   match BuildQueryStructureConstraints qsSchema Ridx' Ridx with
                     | Some CrossConstr => CrossConstr (indexedElement tup') (GetRelation or Ridx)
                     | None => True
                   end)).
    intros; eapply H; try rewrite <- GetRelDropConstraints; eauto.
    repeat find_if_inside; try econstructor; simpl in *.
    unfold GetRelation, Delete_Valid, UpdateUnConstrRelation,
    UpdateRelation, EnsembleDelete; simpl. split; intros; eauto.
    rewrite ith_replace_BoundIndex_neq; eauto using string_dec; simpl.
    rewrite ith_replace_BoundIndex_eq; unfold EnsembleInsert, GetRelation;
    simpl; intuition.
    econstructor.
    econstructor 3 with (v :=  match x as x', x0 as x0'
                                     return (_ -> decides x' _) ->
                                            (_ -> decides x0' _) ->
                                            _
                               with
                                 | true, true =>
                                   fun H H0 => (snd v)
                                 | _, _=> fun _ _ => []
                               end H0 H1').
    repeat find_if_inside; simpl;
    try (solve [unfold not; let H := fresh in intros H; eapply NIntup; eapply H;
                                              unfold EnsembleInsert; eauto]).
    simpl in *.
    destruct_ex; intuition.
    unfold GetRelation, Delete_Valid, UpdateUnConstrRelation,
    UpdateRelation, EnsembleDelete; simpl.
    rewrite ith_replace_BoundIndex_eq; simpl; eauto.
    repeat apply_in_hyp computes_to_inv; subst; simpl; eauto.
    eauto using ComplementIntersectionIndexedList.
    eauto using ComplementIntersectionIndexedList.

    repeat find_if_inside; subst; repeat econstructor.

    simpl.
    repeat find_if_inside; subst; repeat econstructor.
    unfold DropQSConstraints, Delete_Valid, EnsembleDelete; simpl.
    destruct_ex; intuition.
    repeat apply_in_hyp computes_to_inv; subst; simpl; eauto.
    unfold GetRelation, Delete_Valid, UpdateUnConstrRelation,
    UpdateRelation, EnsembleDelete; simpl.
    unfold GetRelation, Delete_Valid, UpdateUnConstrRelation,
    UpdateRelation; rewrite imap_replace_BoundedIndex; simpl; eauto using string_dec.
  Qed.

  Lemma QSDeleteSpec_UnConstr_refine :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema )
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (or : QueryStructure qsSchema)
           refined_schConstr refined_crossConstr,
      DropQSConstraints_AbsR or qs
      -> refine {b | (forall tup tup',
                          GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup'))
                     ->  decides b (DeletePreservesSchemaConstraints
                                      (GetUnConstrRelation qs Ridx)
                                      DeletedTuples
                                      (SatisfiesSchemaConstraints Ridx))}
                refined_schConstr
      -> refine (@Iterate_Decide_Comp_Pre
                           _
                           ((fun Ridx' =>
                               Ridx' <> Ridx
                               -> DeletePreservesCrossConstraints
                                    (GetUnConstrRelation qs Ridx)
                                    (GetUnConstrRelation qs Ridx')
                                    DeletedTuples
                                    (SatisfiesCrossRelationConstraints Ridx' Ridx)))
                           (@Iterate_Ensemble_BoundedIndex_filter
                              _ (fun idx =>
                                   if (eq_nat_dec (ibound Ridx) idx)
                                   then false else true)
                              (fun Ridx' =>
                                 forall tup',
                                   (GetUnConstrRelation qs Ridx') tup'
                                   -> SatisfiesCrossRelationConstraints
                                        Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx)))
                )
                refined_crossConstr
      -> refine
           (or' <- (qs'       <- Pick (QSDeleteSpec {|qsHint := or |} Ridx DeletedTuples);
                    deleted   <- Pick (UnIndexedEnsembleListEquivalence
                                         (Intersection _
                                                       (GetRelation or Ridx)
                                                       (Complement _ (GetRelation qs' Ridx))));
                    ret (qs', deleted));
            nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
            ret (nr', snd or'))
           (schConstr <- refined_schConstr;
            crossConstr <- refined_crossConstr;
            match schConstr, crossConstr with
              | true, true =>
                deleted   <- Pick (UnIndexedEnsembleListEquivalence
                                     (Intersection _
                                                   (GetUnConstrRelation qs Ridx)
                                                   (Complement _ (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples))));
              ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
              | _, _ => ret (qs, [])
            end).
  Proof.
    intros.
    setoid_rewrite (@QSDeleteSpec_UnConstr_refine' _ qs Ridx).
    setoid_rewrite <- H0; setoid_rewrite <- H1.
    repeat (f_equiv; unfold pointwise_relation; intros).
    unfold DropQSConstraints_AbsR in *; subst.
    reflexivity.
  Qed.

  Local Transparent QSDelete.

  Lemma refine_SatisfiesCrossConstraintsDelete
  : forall (qsSchema : QueryStructureSchema)
           (qs : UnConstrQueryStructure qsSchema) (Ridx : BoundedString)
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))),
      refine
        (Iterate_Decide_Comp_Pre (map relName (qschemaSchemas qsSchema))
                             ((fun Ridx' =>
                                 Ridx' <> Ridx
                                 -> DeletePreservesCrossConstraints
                                      (GetUnConstrRelation qs Ridx)
                                      (GetUnConstrRelation qs Ridx')
                                      DeletedTuples
                                      (SatisfiesCrossRelationConstraints Ridx' Ridx)))
                             (@Iterate_Ensemble_BoundedIndex_filter
                              _ (fun idx =>
                                   if (eq_nat_dec (ibound Ridx) idx)
                                   then false else true)
                              (fun Ridx' =>
                                 forall tup',
                                   (GetUnConstrRelation qs Ridx') tup'
                                   -> SatisfiesCrossRelationConstraints
                                        Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx)))
)
        (Iterate_Decide_Comp_opt'_Pre string
                                  (map relName (qschemaSchemas qsSchema))
                                  []
                                  (fun
                                      Ridx' : BoundedIndex
                                                ([] ++
                                                    map relName (qschemaSchemas qsSchema)) =>
                                      if BoundedString_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              (
                                                (DeletePreservesCrossConstraints
                                                 (GetUnConstrRelation qs Ridx)
                                                 (GetUnConstrRelation qs Ridx')
                                                 DeletedTuples
                                                 CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _ (fun idx =>
                                          if (eq_nat_dec (ibound Ridx) idx)
                                          then false else true)
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx)))).
  Proof.
    intros; simpl.
    unfold DeletePreservesCrossConstraints.
    setoid_rewrite <- refine_Iterate_Decide_Comp_Pre.
    unfold SatisfiesCrossRelationConstraints.
    apply refine_Iterate_Decide_Comp_equiv_Pre; simpl; intros.
    apply string_dec.
    destruct (BoundedString_eq_dec Ridx idx); subst.
    congruence.
    destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
    intro; eapply H.
    destruct (BoundedString_eq_dec Ridx idx); subst; eauto.
    destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
    eauto.
  Qed.

  Lemma refine_SatisfiesSchemaConstraintsDelete
  : forall (qsSchema : QueryStructureSchema)
           (qs : UnConstrQueryStructure qsSchema) (Ridx : BoundedString)
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))),
      refine
        {b | (forall tup tup',
                          GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup'))
                     -> decides b (DeletePreservesSchemaConstraints
                                      (GetUnConstrRelation qs Ridx)
                                      DeletedTuples
                                      (SatisfiesSchemaConstraints Ridx))}
        match schemaConstraints (QSGetNRelSchema qsSchema Ridx) with
          | Some Constr =>
            {b | (forall tup tup',
                          GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup'))
                 -> decides b (DeletePreservesSchemaConstraints
                                 (GetUnConstrRelation qs Ridx)
                                 DeletedTuples
                                 (SatisfiesSchemaConstraints Ridx)) }
          | None => ret true
        end.
  Proof.
    intros; unfold DeletePreservesSchemaConstraints, SatisfiesSchemaConstraints;
    destruct (schemaConstraints (QSGetNRelSchema qsSchema Ridx)); try reflexivity.
    intros v Comp_v; econstructor; inversion_by computes_to_inv; subst;
    simpl; tauto.
  Qed.

  Definition QSDeletedTuples
             qsSchema (qs : UnConstrQueryStructure qsSchema )
             (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
             (DeletedTuples :
                Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))) :=
    (UnIndexedEnsembleListEquivalence
       (Intersection _
                     (GetUnConstrRelation qs Ridx)
                     (Complement _ (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)))).

  Lemma QSDeleteSpec_UnConstr_refine_opt :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema )
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (or : QueryStructure qsSchema),
      DropQSConstraints_AbsR or qs ->
      refine
        (or' <- (qs'       <- Pick (QSDeleteSpec {|qsHint := or |} Ridx DeletedTuples);
                 deleted   <- Pick (UnIndexedEnsembleListEquivalence
                                      (Intersection _
                                                    (GetRelation or Ridx)
                                                    (Complement _ (GetRelation qs' Ridx))));
                 ret (qs', deleted));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        match (schemaConstraints (QSGetNRelSchema qsSchema Ridx)) with
            Some Constr =>
            schConstr <- {b | (forall tup tup',
                          GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx (indexedElement tup) (indexedElement tup'))
                 -> decides b (DeletePreservesSchemaConstraints
                                 (GetUnConstrRelation qs Ridx)
                                 DeletedTuples
                                 (SatisfiesSchemaConstraints Ridx)) };
              crossConstr <- (Iterate_Decide_Comp_opt'_Pre string
                                                       (map relName (qschemaSchemas qsSchema))
                                  []
                                  (fun
                                      Ridx' : BoundedIndex
                                                ([] ++
                                                    map relName (qschemaSchemas qsSchema)) =>
                                      if BoundedString_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match
                                          BuildQueryStructureConstraints qsSchema Ridx'
                                                                         Ridx
                                        with
                                          | Some CrossConstr =>
                                            Some
                                              ((DeletePreservesCrossConstraints
                                                     (GetUnConstrRelation qs Ridx)
                                                     (GetUnConstrRelation qs Ridx')
                                                     DeletedTuples
                                                 CrossConstr))
                                          | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _ (fun idx =>
                                          if (eq_nat_dec (ibound Ridx) idx)
                                          then false else true)
                                     (fun Ridx' =>
                                        forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))));
              match schConstr, crossConstr with
                | true, true =>
                  deleted   <- Pick (QSDeletedTuples qs Ridx DeletedTuples);
                    ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
                | _, _ => ret (qs, [])
              end
          | None =>
            crossConstr <- (Iterate_Decide_Comp_opt'_Pre
                              string
                              (map relName (qschemaSchemas qsSchema))
                              []
                              (fun Ridx' : BoundedIndex
                                                ([] ++
                                                    map relName (qschemaSchemas qsSchema))=>
                                 if BoundedString_eq_dec Ridx Ridx'
                                 then None
                                 else
                                   match
                                     BuildQueryStructureConstraints qsSchema Ridx'
                                                                    Ridx
                                   with
                                     | Some CrossConstr =>
                                       Some
                                         (DeletePreservesCrossConstraints
                                            (GetUnConstrRelation qs Ridx)
                                            (GetUnConstrRelation qs Ridx')
                                            DeletedTuples
                                            CrossConstr)
                                     | None => None
                            end)
                              (@Iterate_Ensemble_BoundedIndex_filter
                                 _ (fun idx =>
                                      if (eq_nat_dec (ibound Ridx) idx)
                                      then false else true)
                                 (fun Ridx' =>
                                    forall tup',
                                      (GetUnConstrRelation qs Ridx') tup'
                                      -> SatisfiesCrossRelationConstraints
                                           Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs Ridx))));
              match crossConstr with
                | true =>
                  deleted   <- Pick (QSDeletedTuples qs Ridx DeletedTuples);
                    ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
                | false => ret (qs, [])
              end
        end.
  Proof.
    unfold QSDeletedTuples.
    intros; rewrite QSDeleteSpec_UnConstr_refine;
    eauto using
          refine_SatisfiesSchemaConstraintsDelete,
    refine_SatisfiesCrossConstraintsDelete.
    destruct (schemaConstraints (QSGetNRelSchema qsSchema Ridx)).
    reflexivity.
    simplify with monad laws.
    f_equiv.
  Qed.

  Require Import AdditionalPermutationLemmas GeneralQueryRefinements
          AdditionalLemmas.

  Lemma EnsembleComplementIntersection {A}
  : forall E (P : Ensemble A),
      DecideableEnsemble P
      -> forall (a : @IndexedElement A),
           (In _ (Intersection _ E
                               (Complement _ (EnsembleDelete E P))) a
            <-> In _ (Intersection _ E 
                                   (fun itup => P (indexedElement itup))) a).
  Proof.
    unfold EnsembleDelete, Complement, In in *; intuition;
    destruct H; constructor; eauto; unfold In in *.
    - case_eq (dec (indexedElement x)); intros.
      + eapply dec_decides_P; eauto.
      + exfalso; apply H0; constructor; unfold In; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
    - intros H'; destruct H'; unfold In in *; eauto.
  Qed.

  Lemma DeletedTuplesIntersection {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (P : Ensemble Tuple),
      DecideableEnsemble P
      -> refine {x | QSDeletedTuples qs Ridx P x}
                {x | UnIndexedEnsembleListEquivalence
                       (Intersection _ (GetUnConstrRelation qs Ridx) 
                                     (fun itup => P (indexedElement itup))) x}.
  Proof.
    intros qs Ridx P P_dec v Comp_v; inversion_by computes_to_inv.
    constructor.
    unfold QSDeletedTuples, UnIndexedEnsembleListEquivalence in *; destruct_ex;
    intuition; subst.
    eexists; intuition.
    unfold EnsembleListEquivalence in *; intuition; eauto with typeclass_instances.
    + eapply H0; eapply EnsembleComplementIntersection; eauto with typeclass_instances.
    + eapply EnsembleComplementIntersection; eauto with typeclass_instances.
      eapply H0; eauto.
  Qed.

  Local Transparent Query_For.

  Lemma DeletedTuplesFor {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (P : Ensemble Tuple),
      DecideableEnsemble P
      -> refine {x | QSDeletedTuples qs Ridx P x}
                (For (UnConstrQuery_In qs Ridx
                                       (fun tup => Where (P tup) Return tup))).
  Proof.
    intros qs Ridx P P_dec v Comp_v; rewrite DeletedTuplesIntersection by auto.
    constructor.
    unfold UnIndexedEnsembleListEquivalence.
    unfold Query_For in *; apply computes_to_inv in Comp_v; simpl in *;
    destruct Comp_v as [l [Comp_v Perm_l_v]].
    unfold UnConstrQuery_In, QueryResultComp in *; inversion_by computes_to_inv.
    remember (GetUnConstrRelation qs Ridx); clear Hequ.
    revert P_dec u v l Perm_l_v H1 H0; clear; induction x; simpl; intros.
    - inversion_by computes_to_inv; subst.
      exists (@nil (@IndexedTuple
                      (schemaHeading
                         (relSchema
                            (@nth_Bounded NamedSchema string relName
                                          (qschemaSchemas qsSchema) Ridx)))));
        simpl; split; eauto.
      rewrite Permutation_nil by eauto; reflexivity.
      + unfold EnsembleListEquivalence in *; intuition.
        destruct H0; eapply H1; eauto.
    - inversion_by computes_to_inv; subst.
      unfold UnConstrRelation in u.
      case_eq (@dec _ P P_dec (indexedElement a)); intros.
      + apply computes_to_inv in H1; simpl in *; intuition.
        apply dec_decides_P in H; apply H3 in H.
        apply computes_to_inv in H; simpl in *; subst; simpl in *.
        pose proof (PermutationConsSplit _ _ _ Perm_l_v); destruct_ex; subst.
        destruct (H1 (fun x => u x /\ x <> a) (app x0 x2) x1); intuition eauto.
        * eapply Permutation_cons_inv; rewrite Permutation_middle; eassumption.
        * unfold EnsembleListEquivalence in *; intuition.
          inversion H; subst; eauto.
          unfold In in *; intuition.
          apply H5 in H6; destruct H6; subst; eauto; congruence.
          unfold In; intuition.
          apply H5; simpl; intuition.
          inversion H; subst; eauto.
        * symmetry in H5; pose proof (app_map_inv _ _ _ _ H5); destruct_ex;
          intuition; subst.
          exists (app x4 (a :: x5)); simpl; rewrite map_app; intuition.
          { unfold EnsembleListEquivalence in *; intuition.
            - apply NoDup_app_swap; simpl; constructor; eauto.
              inversion H; subst; unfold not; intros; apply H10.
              assert (List.In a (x4 ++ x5)) as In_a by
                                                (apply in_or_app; apply in_app_or in H6; intuition).
              apply H8 in In_a; destruct In_a; unfold In in *; intuition.
              apply H7 in H13; simpl in H13; intuition.
              + apply NoDup_app_swap; eauto.
            - destruct H6; unfold In in *; apply H7 in H6; simpl in *; intuition.
              apply in_or_app; simpl; intuition.
              assert (u x0) as u_x0 by (apply H7; eauto).
              assert (List.In x0 (x4 ++ x5)) as In_x0
                                               by (apply H8; constructor; unfold In; intuition; subst;
                                                   inversion H; subst; eauto).
              apply in_or_app; simpl; apply in_app_or in In_x0; intuition.
            - unfold In.
              assert (List.In x0 (x4 ++ x5) \/ x0 = a)
                as In_x0
                  by (apply in_app_or in H6; simpl in H6; intuition).
              intuition.
              apply H8 in H9; destruct H9; unfold In in *; intuition.
              constructor; eauto.
              subst; constructor; eauto.
              apply H7; simpl; eauto.
              case_eq (@dec _ P P_dec (indexedElement a)); intros.
              apply dec_decides_P; eauto.
              assert (~ P (indexedElement a)) as H''
                               by (unfold not; intros H'; apply dec_decides_P in H'; congruence);
                apply H4 in H''; discriminate.
          }
      + apply computes_to_inv in H1; simpl in *; intuition.
        assert (~ P (indexedElement a)) as H''
                         by (unfold not; intros H'; apply dec_decides_P in H'; congruence);
          apply H4 in H''; subst.
        destruct (H1 (fun x => u x /\ x <> a) v x1); intuition eauto.
        * unfold EnsembleListEquivalence in *; intuition.
          inversion H5; subst; eauto.
          destruct H0; apply H6 in H0; simpl in H0; intuition.
          simpl in H6; constructor.
          apply H6; eauto.
          inversion H5; intros; subst; eauto.
        * eexists; split; eauto.
          unfold EnsembleListEquivalence in *; intuition.
          destruct H7; intuition.
          eapply H9; constructor; unfold In in *; subst; intuition.
          subst; apply_in_hyp dec_decides_P; congruence.
          constructor;
            apply H9 in H7; destruct H7; unfold In in *; intuition.
  Qed.

End DeleteRefinements.

Tactic Notation "remove" "trivial" "deletion" "checks" :=
  repeat rewrite refineEquiv_bind_bind;
  etransitivity;
  [ repeat (apply refine_bind;
            [reflexivity
            | match goal with
                | |- context [Bind (Delete _ from _ where _)%QuerySpec _] =>
                  unfold pointwise_relation; intros
              end
           ] );
    (* Pull out the relation we're inserting into and then
     rewrite [QSInsertSpec] *)
    match goal with
        H : DropQSConstraints_AbsR ?r_o ?r_n
        |- context [QSDelete ?qs ?R ?P] =>
        (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                   after we've drilled under a bind, this tactic will fail because
                   typeclass resolution breaks down. Generalizing and applying gets
                   around this problem for reasons unknown. *)
        let H' := fresh in
        pose proof (@QSDeleteSpec_UnConstr_refine_opt
                      _ r_n R P r_o H) as H';
          apply H'
    end
  | cbv beta; simpl schemaConstraints; cbv iota;
    simpl map; simpl app;
    simpl relName in *; simpl schemaHeading in *;
    pose_string_ids; simpl;
    simplify with monad laws;
    try rewrite <- GetRelDropConstraints;
    repeat match goal with
             | H : DropQSConstraints_AbsR ?qs ?uqs |- _ =>
               rewrite H in *
           end
  ].

Tactic Notation "drop" "constraints" "from" "delete" constr(methname) :=
  hone method methname;
  [ remove trivial deletion checks;
    finish honing
  | ].
