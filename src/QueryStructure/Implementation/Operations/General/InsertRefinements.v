Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List
        Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Computation
        ADTSynthesis.ADT
        ADTSynthesis.ADTRefinement
        ADTSynthesis.ADTNotation
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.QueryStructure.Specification.Operations.Query
        ADTSynthesis.QueryStructure.Specification.Operations.Insert
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements.

(* Facts about implements insert operations. *)

Section InsertRefinements.

  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesTupleConstraints
       SatisfiesAttributeConstraints.

  Arguments GetUnConstrRelation : simpl never.
  Arguments UpdateUnConstrRelation : simpl never.
  Arguments replace_BoundedIndex : simpl never.
  Arguments BuildQueryStructureConstraints : simpl never.
  Arguments BuildQueryStructureConstraints' : simpl never.

  Program
    Definition Insert_Valid
    (qsSchema : QueryStructureSchema)
    (qs : QueryStructure qsSchema)
    (Ridx : _)
    (tup : @IndexedTuple (QSGetNRelSchemaHeading qsSchema Ridx))
    (schConstr : forall tup',
                   GetRelation qs Ridx tup' ->
                   SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))
    (schConstr' : forall tup',
                   GetRelation qs Ridx tup' ->
                   SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))
    (schConstr_self :
       @SatisfiesAttributeConstraints qsSchema Ridx (indexedElement tup))
    (qsConstr : forall Ridx',
                  SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup) (GetRelation qs Ridx'))
    (qsConstr' : forall Ridx',
                   Ridx' <> Ridx ->
                   forall tup',
                     GetRelation qs Ridx' tup'
                     -> SatisfiesCrossRelationConstraints
                     Ridx' Ridx (indexedElement tup')
                     (EnsembleInsert tup (GetRelation qs Ridx)))
  : QueryStructure qsSchema :=
    {| rels :=
         UpdateRelation _ (rels qs) Ridx {| rel := EnsembleInsert tup (GetRelation qs Ridx)|}
    |}.
  Next Obligation.
    unfold GetRelation.
    unfold SatisfiesAttributeConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ith_Bounded _ (rels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (attrConstraints
                (relSchema (nth_Bounded relName (qschemaSchemas qsSchema) Ridx)));
      eauto;
    unfold EnsembleInsert in *; simpl in *; intuition; subst; eauto.
  Defined.
  Next Obligation.
    unfold GetRelation.
    unfold SatisfiesTupleConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ith_Bounded _ (rels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (tupleConstraints
                (relSchema (nth_Bounded relName (qschemaSchemas qsSchema) Ridx)));
      eauto.
    unfold EnsembleInsert in *; simpl in *; intuition; subst; eauto.
    congruence.
  Qed.
  Next Obligation.
    caseEq (BuildQueryStructureConstraints qsSchema idx idx'); eauto.
    unfold SatisfiesCrossRelationConstraints, UpdateRelation in *;
    destruct (BoundedString_eq_dec Ridx idx'); subst.

    - rewrite ith_replace_BoundIndex_eq; simpl.
      rewrite ith_replace_BoundIndex_neq in H1; eauto using string_dec.
      generalize (qsConstr' idx H0 _ H1); rewrite H; eauto.
    - rewrite ith_replace_BoundIndex_neq in *; eauto using string_dec.
      destruct (BoundedString_eq_dec Ridx idx); subst.
      + rewrite ith_replace_BoundIndex_eq in H1; simpl in *; eauto.
        unfold EnsembleInsert in H1; destruct H1; subst; eauto.
        * generalize (qsConstr idx'); rewrite H; eauto.
        * pose proof (crossConstr qs idx idx') as X; rewrite H in X; eauto.
      + rewrite ith_replace_BoundIndex_neq in H1; eauto using string_dec.
        pose proof (crossConstr qs idx idx') as X; rewrite H in X; eauto.
  Qed.

  Lemma QSInsertSpec_refine' :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr_self <-
                           {b |
                            decides b
                         (SatisfiesAttributeConstraints Ridx (indexedElement tup))};
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))};
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))};
            qsConstr <- {b | decides b
              (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup) (GetRelation qs Ridx'))};
            qsConstr' <- {b | decides
                                b
                                (forall Ridx',
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     (GetRelation qs Ridx') tup'
                                     -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx (indexedElement tup')
                                       (EnsembleInsert tup (GetRelation qs Ridx)))};
            match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (EnsembleInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _ , _, _, _ => default
            end).
  Proof.
    intros qsSchema qs Ridx tup default v Comp_v;
    computes_to_inv;
      destruct v0;
      [ destruct v1;
        [ destruct v2;
          [ destruct v3;
            [ destruct v4;
              [ repeat (computes_to_inv; destruct_ex; split_and); simpl in *;
                computes_to_econstructor; unfold QSInsertSpec; eauto |
              ]
            | ]
          | ]
        |  ]
      |  ];
      cbv delta [decides] beta in *; simpl in *;
      repeat (computes_to_inv; destruct_ex); eauto;
      computes_to_econstructor; unfold QSInsertSpec; intros;
      solve [elimtype False; intuition].
  Qed.

  Lemma QSInsertSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr_self <- {b | decides b
                                           (SatisfiesAttributeConstraints Ridx (indexedElement tup))};
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))};
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))};
            qsConstr <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   SatisfiesCrossRelationConstraints
                                     Ridx Ridx' (indexedElement tup)
                                     (GetRelation qsHint Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetRelation qsHint Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx (indexedElement tup')
                                       (EnsembleInsert tup (GetRelation qs Ridx))));
            match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (EnsembleInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _, _, _, _ => default
            end).
  Proof.
    intros.
    rewrite QSInsertSpec_refine'; f_equiv.
    unfold pointwise_relation; intros.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine' :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @IndexedTuple (schemaHeading (QSGetNRelSchema qsSchema Ridx)))
           (or : QueryStructure qsSchema)
           (NIntup : ~ GetUnConstrRelation qs Ridx tup),
      DropQSConstraints_AbsR or qs ->
      refine
        (or' <- (qs' <- Pick (QSInsertSpec {| qsHint := or |} Ridx tup);
                 b <- Pick (SuccessfulInsertSpec {| qsHint := or |} Ridx qs' tup);
                 ret (qs', b));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        (schConstr_self <- {b | decides b (SatisfiesAttributeConstraints Ridx (indexedElement tup))};
         schConstr <-
                   {b | decides b
                      (forall tup',
                         GetUnConstrRelation qs Ridx tup'
                         -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))};
         schConstr' <-
                    {b |
                     decides
                       b
                       (forall tup',
                          GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))};
         qsConstr <- (@Iterate_Decide_Comp _
                                           (fun Ridx' =>
                                              SatisfiesCrossRelationConstraints
                                     Ridx Ridx' (indexedElement tup)
                                     (GetUnConstrRelation qs Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetUnConstrRelation qs Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx (indexedElement tup')
                                       (EnsembleInsert tup (GetUnConstrRelation qs Ridx))));
            match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                ret (UpdateUnConstrRelation qs Ridx (EnsembleInsert tup (GetUnConstrRelation qs Ridx)), true)
              | _, _, _, _, _ => ret (qs, false)
            end).
  Proof.
    intros.
    setoid_rewrite refineEquiv_pick_eq'.
    unfold DropQSConstraints_AbsR in *; intros; subst.
    rewrite QSInsertSpec_refine with (default := ret or).
    unfold refine; intros; subst.
      computes_to_inv.
      repeat rewrite GetRelDropConstraints in *.
      (* These assert are gross. Need to eliminate them. *)
      assert ((fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup)
            (GetUnConstrRelation (DropQSConstraints or) Ridx')) =
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                 SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup)
                                                   (GetRelation or Ridx'))) as rewriteSat
        by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
            reflexivity); rewrite rewriteSat in H'''; clear rewriteSat.
      assert ((fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          Ridx' <> Ridx ->
          forall
            tup' : @IndexedTuple
                     (schemaHeading
                        (relSchema
                           (nth_Bounded relName (qschemaSchemas qsSchema)
                              Ridx'))),
          GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
          SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
            (EnsembleInsert tup (GetRelation or Ridx))) =
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
      Ridx' <> Ridx ->
      forall
        tup' : @IndexedTuple
                 (schemaHeading
                    (relSchema
                       (nth_Bounded relName (qschemaSchemas qsSchema) Ridx'))),
      GetRelation or Ridx' tup' ->
      SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
                                        (EnsembleInsert tup (GetRelation or Ridx))))
          as rewriteSat
            by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
                reflexivity); rewrite rewriteSat in H''''; clear rewriteSat.
      (* Resume not-terribleness *)
      generalize (Iterate_Decide_Comp_BoundedIndex _ _ _ H''') as H3';
      generalize (Iterate_Decide_Comp_BoundedIndex _ _ _ H'''') as H4'; intros.
      revert H''' H''''.
      computes_to_inv.
      intros.
      eapply BindComputes with (a := match v0 as x', v1 as x0', v2 as x1', v3 as x2', v4 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => (@Insert_Valid _ or Ridx tup H0 H1 H H2 H3, true)
                          | _, _, _, _, _ => fun _ _ _ _ _ => (or, false)
                        end H H' H'' H3' H4').
      eapply BindComputes with (a :=
                                  match v0 as x', v1 as x0', v2 as x1', v3 as x2', v4 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => @Insert_Valid _ or Ridx tup H0 H1 H H2 H3
                          | _, _, _, _, _ => fun _ _ _ _ _ => or
                        end H H' H'' H3' H4').
      repeat (computes_to_econstructor; eauto).
      repeat find_if_inside; try computes_to_econstructor; simpl in *.
      unfold GetRelation, Insert_Valid, UpdateUnConstrRelation,
      UpdateRelation, EnsembleInsert ; simpl; split; intros; eauto.
      rewrite ith_replace_BoundIndex_neq; eauto using string_dec; simpl.
      rewrite ith_replace_BoundIndex_eq; unfold EnsembleInsert, GetRelation;
      simpl; intuition.
      computes_to_econstructor.
      eapply PickComputes with (a :=  match v0 as x', v1 as x0', v2 as x1', v3 as x2', v4 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => true
                          | _, _, _, _, _ => fun _ _ _ _ _ => false
                        end H H' H'' H3' H4').
      repeat find_if_inside; simpl;
      try (solve [unfold not; let H := fresh in intros H; eapply NIntup; eapply H;
      unfold EnsembleInsert; eauto]).
      intros; rewrite <- GetRelDropConstraints.
      unfold Insert_Valid, GetUnConstrRelation, DropQSConstraints,
      UpdateRelation; simpl.
      rewrite <- ith_Bounded_imap, ith_replace_BoundIndex_eq; simpl;
      tauto.

      repeat find_if_inside; subst; repeat computes_to_econstructor.

      simpl.
      repeat find_if_inside; subst; repeat computes_to_econstructor.
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl.
      unfold GetRelation, Insert_Valid, UpdateUnConstrRelation,
      UpdateRelation; rewrite imap_replace_BoundedIndex; simpl; eauto using string_dec.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
  Qed.

  Lemma freshIdx2UnConstr {qsSchema} qs Ridx
  : refine {bound | forall tup : IndexedElement,
                      @GetUnConstrRelation qsSchema qs Ridx tup ->
                      tupleIndex tup <> bound}
           {bound | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) bound}.
  Proof.
    unfold UnConstrFreshIdx; intros v Comp_v; computes_to_econstructor.
    computes_to_inv; intros.
    unfold tupleIndex in *; apply Comp_v in H; omega.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema )
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx)))
           (or : QueryStructure qsSchema)
           refined_schConstr_self refined_schConstr refined_schConstr'
           refined_qsConstr refined_qsConstr',
      refine {b | decides b (SatisfiesAttributeConstraints Ridx tup)}
             refined_schConstr_self
      -> refine {b | decides b
                             (forall tup',
                                GetUnConstrRelation qs Ridx tup'
                                -> SatisfiesTupleConstraints Ridx tup (indexedElement tup'))}
                refined_schConstr
      -> refine
           {b |
            decides
              b
              (forall tup',
                 GetUnConstrRelation qs Ridx tup'
                 -> SatisfiesTupleConstraints Ridx (indexedElement tup') tup)}
           refined_schConstr'
      -> refine
           (@Iterate_Decide_Comp _
                                 (fun Ridx' =>
                                    SatisfiesCrossRelationConstraints
                                      Ridx Ridx' tup
                                      (GetUnConstrRelation qs Ridx')))
           refined_qsConstr
      -> (forall idx,
            refine
              (@Iterate_Decide_Comp _
                                    (fun Ridx' =>
                                       Ridx' <> Ridx
                                       -> forall tup',
                                            (GetUnConstrRelation qs Ridx') tup'
                                            -> SatisfiesCrossRelationConstraints
                                                 Ridx' Ridx (indexedElement tup')
                                                 (EnsembleInsert
                                                    {| elementIndex := idx;
                                                       indexedElement := tup |}
                                                    (GetUnConstrRelation qs Ridx))))
              (refined_qsConstr' idx))
      -> DropQSConstraints_AbsR or qs ->
      refine
        (or' <- (idx <- Pick (freshIdx {| qsHint := or |} Ridx);
                 qs' <- Pick (QSInsertSpec {| qsHint := or |} Ridx
                                          {| elementIndex := idx;
                                             indexedElement := tup |});
                 b <- Pick (SuccessfulInsertSpec {| qsHint := or |} Ridx qs'
                                                 {| elementIndex := idx;
                                                    indexedElement := tup |});
                 ret (qs', b));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        (idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx};
         (schConstr_self <- refined_schConstr_self;
          schConstr <- refined_schConstr;
          schConstr' <- refined_schConstr';
          qsConstr <- refined_qsConstr ;
          qsConstr' <- (refined_qsConstr' idx);
          match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
                | true, true, true, true, true =>
                  ret (UpdateUnConstrRelation qs Ridx
                                          (EnsembleInsert
                                             {| elementIndex := idx;
                                                indexedElement := tup |}
                                                   (GetUnConstrRelation qs Ridx)), true)
                | _, _, _, _, _ => ret (qs, false)
              end)).
  Proof.
    intros.
    simplify with monad laws.
    unfold freshIdx.
    simpl.
    rewrite <- GetRelDropConstraints.
    unfold DropQSConstraints_AbsR in *; subst.
    rewrite freshIdx2UnConstr.
    apply refine_bind_pick; intros.
    setoid_rewrite <- H; setoid_rewrite <- H0; setoid_rewrite <- H1;
    setoid_rewrite <- H2; setoid_rewrite <- (H3 a).
    setoid_rewrite <- (QSInsertSpec_UnConstr_refine' _ {| elementIndex := a; indexedElement := tup |}).
    repeat setoid_rewrite refineEquiv_bind_bind.
    setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold DropQSConstraints_AbsR in *; subst.
    f_equiv; intros.
    unfold UnConstrFreshIdx, not in *; intros.
    apply H4 in H5; simpl in *; omega.
    reflexivity.
  Qed.

  Lemma refine_SatisfiesCrossConstraints'
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
    forall idx,
      refine
        (@Iterate_Decide_Comp _
                              (fun Ridx' =>
                Ridx' <> Ridx
                -> forall tup',
                     (GetUnConstrRelation qs Ridx') tup'
                     -> SatisfiesCrossRelationConstraints
                          Ridx' Ridx (indexedElement tup')
                          (EnsembleInsert
                             {| elementIndex := idx;
                                indexedElement := tup |}
                             (GetUnConstrRelation qs Ridx))))
             (@Iterate_Decide_Comp_opt' _ _ []
                                        (fun Ridx' =>
                                           if (BoundedString_eq_dec Ridx Ridx') then
                                             None
                                           else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetUnConstrRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end)).
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints.
    apply refine_Iterate_Decide_Comp_equiv; simpl; intros.
    apply string_dec.
    destruct (BoundedString_eq_dec Ridx idx0); subst.
    congruence.
    destruct (BuildQueryStructureConstraints qsSchema idx0 Ridx); eauto.
    intro; eapply H.
    destruct (BoundedString_eq_dec Ridx idx0); subst; eauto.
    destruct (BuildQueryStructureConstraints qsSchema idx0 Ridx); eauto.
  Qed.

  Local Transparent QSInsert.

  Lemma QSInsertSpec_UnConstr_refine_opt :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema )
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx)))
           (or : QueryStructure qsSchema),
      DropQSConstraints_AbsR or qs ->
      refine
        (or' <- (idx <- Pick (freshIdx {| qsHint := or |} Ridx);
                 qs' <- Pick (QSInsertSpec {| qsHint := or |} Ridx
                                          {| elementIndex := idx;
                                             indexedElement := tup |});
                 b <- Pick (SuccessfulInsertSpec {| qsHint := or |} Ridx qs'
                                                 {| elementIndex := idx;
                                                    indexedElement := tup |});
                 ret (qs', b));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        match (attrConstraints (QSGetNRelSchema qsSchema Ridx)),
              (tupleConstraints (QSGetNRelSchema qsSchema Ridx)) with
            Some aConstr, Some tConstr =>
            idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx} ;
            (schConstr_self <- {b | decides b (aConstr tup) };
                   schConstr <- {b | decides b
                                             (forall tup',
                                                GetUnConstrRelation qs Ridx tup'
                                                -> tConstr tup (indexedElement tup'))};
                   schConstr' <- {b | decides b
                                              (forall tup',
                                                   GetUnConstrRelation qs Ridx tup'
                                                   -> tConstr (indexedElement tup') tup)};
                   qsConstr <- (@Iterate_Decide_Comp_opt' _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt' _ _ []
                                        (fun Ridx' =>
                                           if (BoundedString_eq_dec Ridx Ridx') then
                                             None
                                           else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetUnConstrRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end));
                   match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
                     | true, true, true, true, true =>
                       ret (UpdateUnConstrRelation qs Ridx
                                                   (EnsembleInsert
                                                      {| elementIndex := idx;
                                                         indexedElement := tup |}
                                                      (GetUnConstrRelation qs Ridx)), true)
                     | _, _, _, _, _ => ret (qs, false)
                       end)
              | Some aConstr, None =>
                idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx} ;
                  (schConstr_self <- {b | decides b (aConstr tup) };
                   qsConstr <- (@Iterate_Decide_Comp_opt' _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt' _ _ []
                                        (fun Ridx' =>
                                           if (BoundedString_eq_dec Ridx Ridx') then
                                             None
                                           else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetUnConstrRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end));
                   match schConstr_self, qsConstr, qsConstr' with
                     | true, true, true =>
                       ret (UpdateUnConstrRelation qs Ridx
                                                   (EnsembleInsert
                                                      {| elementIndex := idx;
                                                         indexedElement := tup |}
                                                      (GetUnConstrRelation qs Ridx)), true)
                     | _, _, _ => ret (qs, false)
                       end)
              | None, Some tConstr =>
                idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx} ;
                  (schConstr <- {b | decides b
                                             (forall tup',
                                                GetUnConstrRelation qs Ridx tup'
                                                -> tConstr tup (indexedElement tup'))};
                   schConstr' <- {b | decides b
                                              (forall tup',
                                                   GetUnConstrRelation qs Ridx tup'
                                                   -> tConstr (indexedElement tup') tup)};
                   qsConstr <- (@Iterate_Decide_Comp_opt' _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt' _ _ []
                                        (fun Ridx' =>
                                           if (BoundedString_eq_dec Ridx Ridx') then
                                             None
                                           else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetUnConstrRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end));
                   match schConstr, schConstr', qsConstr, qsConstr' with
                         | true, true, true, true =>
                           ret (UpdateUnConstrRelation qs Ridx
                                                   (EnsembleInsert
                                                      {| elementIndex := idx;
                                                         indexedElement := tup |}
                                                      (GetUnConstrRelation qs Ridx)), true)
                         | _, _, _, _ => ret (qs, false)
                       end)
              | None, None =>
                idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx} ;
                  (qsConstr <- (@Iterate_Decide_Comp_opt' _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt' _ _ []
                                        (fun Ridx' =>
                                           if (BoundedString_eq_dec Ridx Ridx') then
                                             None
                                           else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetUnConstrRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end));
                   match qsConstr, qsConstr' with
                         | true, true =>
                           ret (UpdateUnConstrRelation qs Ridx
                                                   (EnsembleInsert
                                                      {| elementIndex := idx;
                                                         indexedElement := tup |}
                                                      (GetUnConstrRelation qs Ridx)), true)
                         | _, _ => ret (qs, false)
                       end)
        end.
    unfold QSInsert.
    intros; rewrite QSInsertSpec_UnConstr_refine;
    eauto using
          refine_SatisfiesAttributeConstraints_self,
    refine_SatisfiesTupleConstraints,
    refine_SatisfiesTupleConstraints',
    refine_SatisfiesCrossConstraints;
    [
    | intros; eapply refine_SatisfiesCrossConstraints'].
    destruct (attrConstraints (QSGetNRelSchema qsSchema Ridx));
      destruct (tupleConstraints (QSGetNRelSchema qsSchema Ridx)).
    - reflexivity.
    - f_equiv; unfold pointwise_relation; intros.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; f_equiv.
    - f_equiv; unfold pointwise_relation; intros.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; f_equiv.
    - f_equiv; unfold pointwise_relation; intros.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; f_equiv.
  Qed.

End InsertRefinements.

(* We should put all these simplification hints into a distinct file
   so we're not unfolding things all willy-nilly. *)
Arguments Iterate_Decide_Comp _ _ / _.
Arguments Iterate_Decide_Comp' _ _ _ _ / _.
Arguments SatisfiesCrossRelationConstraints  _ _ _ _ _ / .
Arguments BuildQueryStructureConstraints  _ _ _ / .
Arguments BuildQueryStructureConstraints'  _ _ _ _ / .
Arguments BuildQueryStructureConstraints_cons / .
Arguments GetNRelSchemaHeading  _ _ / .
Arguments Ensemble_BoundedIndex_app_comm_cons  _ _ _ _ _ _ / .
Arguments id  _ _ / .

Create HintDb refine_keyconstraints discriminated.
(*Hint Rewrite refine_Any_DecideableSB_True : refine_keyconstraints.*)

Arguments ith_Bounded _ _ _ _ _ _ _ / .
Arguments SatisfiesTupleConstraints _ _ _ _ / .
Arguments GetUnConstrRelation : simpl never.
Arguments UpdateUnConstrRelation : simpl never.
Arguments replace_BoundedIndex : simpl never.
