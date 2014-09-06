Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryStructure EnsembleListEquivalence
        QuerySpecs.QueryQSSpecs QuerySpecs.DeleteQSSpecs
        ConstraintChecksRefinements ListQueryStructureRefinements.

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
       forall tup tup',
         EnsembleDelete (GetRelation qs Ridx) DeletedTuples tup
         -> EnsembleDelete (GetRelation qs Ridx) DeletedTuples tup'
         -> SatisfiesSchemaConstraints Ridx tup tup')
    (* And is compatible with the cross-schema constraints. *)
    (crossConstr' :
       forall Ridx',
         Ridx' <> Ridx ->
         forall tup',
           (GetRelation qs Ridx') tup'
           -> SatisfiesCrossRelationConstraints
                Ridx' Ridx tup'
                (EnsembleDelete (GetRelation qs Ridx) DeletedTuples))
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
  Defined.
  Next Obligation.
    caseEq (BuildQueryStructureConstraints qsSchema idx idx'); eauto.
    unfold SatisfiesCrossRelationConstraints, UpdateRelation in *;
      destruct (BoundedString_eq_dec Ridx idx'); subst.

    - rewrite ith_replace_BoundIndex_eq; simpl.
      rewrite ith_replace_BoundIndex_neq in H1; eauto using string_dec.
      generalize (crossConstr' idx H0 _ H1); rewrite H; eauto.
    - rewrite ith_replace_BoundIndex_neq in *; eauto using string_dec.
      destruct (BoundedString_eq_dec Ridx idx); subst.
      + rewrite ith_replace_BoundIndex_eq in H1; simpl in *; eauto.
        unfold EnsembleDelete in H1; destruct H1; subst; eauto.
        * pose proof (crossConstr qs idx idx') as X; rewrite H in X; eauto.
      + rewrite ith_replace_BoundIndex_neq in H1; eauto using string_dec.
        pose proof (crossConstr qs idx idx') as X; rewrite H in X; eauto.
  Qed.

  Lemma QSDeleteSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))),
      refine
        (Pick (QSDeleteSpec {| qsHint := qs |} Ridx DeletedTuples))
        (schConstr <- {b |
                       decides
                         b
                         (forall tup tup',
                            EnsembleDelete (GetRelation qs Ridx) DeletedTuples tup
                            -> EnsembleDelete (GetRelation qs Ridx) DeletedTuples tup'
                            -> SatisfiesSchemaConstraints Ridx tup tup')
                      };
         crossConstr <- {b |
                         decides
                           b
                           (forall Ridx',
                              Ridx' <> Ridx ->
                              forall tup',
                                (GetRelation qs Ridx') tup'
                                -> SatisfiesCrossRelationConstraints
                                     Ridx' Ridx tup'
                                     (EnsembleDelete (GetRelation qs Ridx) DeletedTuples))
                        };
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
    destruct x; destruct x0;
    repeat (apply_in_hyp computes_to_inv; destruct_ex; split_and); simpl in * ;
    solve
      [econstructor; unfold QSDeleteSpec; eauto; right; subst; intuition ].
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
    unfold EnsembleListEquivalence.EnsembleListEquivalence; intuition.
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
                       decides
                         b
                         (forall tup tup',
                            EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup
                            -> EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup'
                            -> SatisfiesSchemaConstraints Ridx tup tup')
                      };
         crossConstr <- (@Iterate_Decide_Comp _
                                              (fun Ridx' =>
                                                 Ridx' <> Ridx ->
                                                 forall tup',
                                                   (GetUnConstrRelation qs Ridx') tup'
                                                   -> SatisfiesCrossRelationConstraints
                                                        Ridx' Ridx tup'
                                                        (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)));
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
    (* These assert are gross. Need to eliminate them. *)
    assert (
        (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
           Ridx' <> Ridx ->
           forall tup' : IndexedTuple,
             GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
             SatisfiesCrossRelationConstraints Ridx' Ridx tup'
                                               (EnsembleDelete (GetRelation or Ridx) DeletedTuples))
        = fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
            Ridx' <> Ridx ->
            forall tup' : IndexedTuple,
              GetRelation or Ridx' tup' ->
              SatisfiesCrossRelationConstraints Ridx' Ridx tup'
                                                (EnsembleDelete (GetRelation or Ridx) DeletedTuples))
      as rewriteSat
        by (apply functional_extensionality; intros; repeat rewrite GetRelDropConstraints;
            reflexivity); rewrite rewriteSat in H1; clear rewriteSat.
    (* Resume not-terribleness *)
    generalize (Iterate_Decide_Comp_BoundedIndex _ _ _ H1) as H1'; intros.
    simpl in *; revert H1.
    repeat apply_in_hyp computes_to_inv; destruct_ex;
    intuition; apply_in_hyp computes_to_inv; subst.
    econstructor 2 with
    (comp_a_value := match x as x', x0 as x0'
                           return decides x' _ ->
                                  decides x0' _  -> _
                     with
                       | true, true =>
                         fun H0 H1 =>
                           (@Delete_Valid _ or Ridx DeletedTuples H0 H1, snd v)
                       | _, _ => fun _ _ => (or, [])
                     end H0 H1').
    econstructor 2 with
    (comp_a_value := match x as x', x0 as x0'
                           return decides x' _ ->
                                  decides x0' _  -> _
                     with
                       | true, true =>
                         fun H0 H1 =>
                           @Delete_Valid _ or Ridx DeletedTuples H0 H1
                       | _, _ => fun _ _ => or
                     end H0 H1').
    repeat (econstructor; eauto).
    repeat find_if_inside; try econstructor; simpl in *.
    unfold GetRelation, Delete_Valid, UpdateUnConstrRelation,
    UpdateRelation, EnsembleDelete; simpl; split; intros; eauto.
    rewrite ith_replace_BoundIndex_neq; eauto using string_dec; simpl.
    rewrite ith_replace_BoundIndex_eq; unfold EnsembleInsert, GetRelation;
    simpl; intuition.
    econstructor.
    econstructor 3 with (v :=  match x as x', x0 as x0'
                                     return decides x' _ ->
                                            decides x0' _ ->
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
      -> refine {b | decides
                       b
                       (forall tup tup',
                          EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup
                          -> EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup'
                          -> SatisfiesSchemaConstraints Ridx tup tup') }
                refined_schConstr
      -> refine ((@Iterate_Decide_Comp _
                                       (fun Ridx' =>
                                          Ridx' <> Ridx ->
                                          forall tup',
                                            (GetUnConstrRelation qs Ridx') tup'
                                            -> SatisfiesCrossRelationConstraints
                                                 Ridx' Ridx tup'
                                                 (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples))))
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
        (Iterate_Decide_Comp (map relName (qschemaSchemas qsSchema))
                             (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                                Ridx' <> Ridx ->
                                forall tup' : IndexedTuple,
                                  GetUnConstrRelation qs Ridx' tup' ->
                                  SatisfiesCrossRelationConstraints Ridx' Ridx tup'
                                                                    (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)))
        (Iterate_Decide_Comp_opt' string
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
                                              (forall tup' : IndexedTuple,
                                                 GetUnConstrRelation qs Ridx' tup' ->
                                                 CrossConstr tup'
                                                             (EnsembleDelete
                                                                (GetUnConstrRelation qs Ridx)
                                                                DeletedTuples))
                                          | None => None
                                        end)).
  Proof.
    intros; simpl.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints.
    apply refine_Iterate_Decide_Comp_equiv; simpl; intros.
    apply string_dec.
    destruct (BoundedString_eq_dec Ridx idx); subst.
    congruence.
    destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
    intro; eapply H.
    destruct (BoundedString_eq_dec Ridx idx); subst; eauto.
    destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
  Qed.

  Lemma refine_SatisfiesSchemaConstraintsDelete
  : forall (qsSchema : QueryStructureSchema)
           (qs : UnConstrQueryStructure qsSchema) (Ridx : BoundedString)
           (DeletedTuples :
              Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))),
      refine
        {b |
         decides b
                 (forall tup tup',
                    EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup
                    -> EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup'
                    -> SatisfiesSchemaConstraints Ridx tup tup') }
        match schemaConstraints (QSGetNRelSchema qsSchema Ridx) with
          | Some Constr =>
            {b | decides
                   b
                   (forall tup tup',
                      EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup
                      -> EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup'
                      -> Constr tup tup') }
          | None => ret true
        end.
  Proof.
    intros; unfold SatisfiesSchemaConstraints;
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
            schConstr <- {b | decides
                                b
                                (forall tup tup',
                                   EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup
                                   -> EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples tup'
                                   -> Constr tup tup') };
              crossConstr <- (@Iterate_Decide_Comp_opt'
                                _ _ []
                                (fun Ridx' =>
                                   if (BoundedString_eq_dec Ridx Ridx') then
                                     None
                                   else
                                     match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                       | Some CrossConstr =>
                                         Some (
                                             forall tup',
                                               (GetUnConstrRelation qs Ridx') tup'
                                               -> CrossConstr (indexedTuple tup') (
                                                                (EnsembleDelete
                                                                   (GetUnConstrRelation qs Ridx)
                                                                   DeletedTuples)))
                                       | None => None
                                     end));
              match schConstr, crossConstr with
                | true, true =>
                  deleted   <- Pick (QSDeletedTuples qs Ridx DeletedTuples);
                    ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
                | _, _ => ret (qs, [])
              end
          | None =>
            crossConstr <- (@Iterate_Decide_Comp_opt'
                              _ _ []
                              (fun Ridx' =>
                                 if (BoundedString_eq_dec Ridx Ridx') then
                                   None
                                 else
                                   match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                     | Some CrossConstr =>
                                       Some (
                                           forall tup',
                                             (GetUnConstrRelation qs Ridx') tup'
                                             -> CrossConstr (indexedTuple tup') (
                                                              (EnsembleDelete
                                                                 (GetUnConstrRelation qs Ridx)
                                                                 DeletedTuples)))
                                     | None => None
                                   end));
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
  : forall (E P : Ensemble A),
      DecideableEnsemble P
      -> forall (a : A),
           (In _ (Intersection _ E
                               (Complement _ (EnsembleDelete E P))) a
            <-> In _ (Intersection _ E P) a).
  Proof.
    unfold EnsembleDelete, Complement, In in *; intuition;
    destruct H; constructor; eauto; unfold In in *.
    - case_eq (GeneralQueryRefinements.dec x); intros.
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
                       (Intersection _ (GetUnConstrRelation qs Ridx) P) x}.
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
      case_eq (@GeneralQueryRefinements.dec _ P P_dec a); intros.
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
              case_eq (@GeneralQueryRefinements.dec _ P P_dec a); intros.
              apply dec_decides_P; eauto.
              assert (~ P a) as H''
                               by (unfold not; intros H'; apply dec_decides_P in H'; congruence);
                apply H4 in H''; discriminate.
          }
      + apply computes_to_inv in H1; simpl in *; intuition.
        assert (~ P a) as H''
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
