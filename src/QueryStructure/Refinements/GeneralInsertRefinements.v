Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryStructure
        QuerySpecs.QueryQSSpecs QuerySpecs.InsertQSSpecs EnsembleListEquivalence
        ConstraintChecksRefinements.

(* Facts about implements insert operations. *)

Section InsertRefinements.

  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesSchemaConstraints.

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
                   SatisfiesSchemaConstraints Ridx tup tup')
    (schConstr' : forall tup',
                   GetRelation qs Ridx tup' ->
                   SatisfiesSchemaConstraints Ridx tup' tup)
    (schConstr_self :
       @SatisfiesSchemaConstraints qsSchema Ridx tup tup)
    (qsConstr : forall Ridx',
                  SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))
    (qsConstr' : forall Ridx',
                   Ridx' <> Ridx ->
                   forall tup',
                     GetRelation qs Ridx' tup'
                     -> SatisfiesCrossRelationConstraints
                     Ridx' Ridx tup'
                     (EnsembleInsert tup (GetRelation qs Ridx)))
  : QueryStructure qsSchema :=
    {| rels :=
         UpdateRelation _ (rels qs) Ridx {| rel := EnsembleInsert tup (GetRelation qs Ridx)|}
    |}.
  Next Obligation.
    unfold GetRelation.
    unfold SatisfiesSchemaConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ith_Bounded _ (rels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (schemaConstraints
                (relSchema (nth_Bounded relName (qschemaSchemas qsSchema) Ridx))); eauto.
    unfold EnsembleInsert in *; simpl in *; intuition; subst; eauto.
  Defined.
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
                         (SatisfiesSchemaConstraints Ridx tup tup)};
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup tup')};
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup' tup)};
            qsConstr <- {b | decides b
              (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))};
            qsConstr' <- {b | decides
                                b
                                (forall Ridx',
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     (GetRelation qs Ridx') tup'
                                     -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
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
    intros qsSchema qs Ridx tup default v Comp_v.
    do 5 (apply_in_hyp computes_to_inv; destruct_ex; split_and);
      destruct x;
      [ destruct x0;
        [ destruct x1;
          [ destruct x2;
            [ destruct x3;
              [ repeat (apply_in_hyp computes_to_inv; destruct_ex; split_and); simpl in *;
                econstructor; unfold QSInsertSpec; eauto |
              ]
            | ]
          | ]
        |  ]
      |  ];
      cbv delta [decides] beta in *; simpl in *;
      repeat (apply_in_hyp computes_to_inv; destruct_ex); eauto;
      econstructor; unfold QSInsertSpec; intros;
      solve [elimtype False; intuition].
  Qed.

  Lemma QSInsertSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr_self <- {b | decides b
                                           (SatisfiesSchemaConstraints Ridx tup tup)};
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup tup')};
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup' tup)};
            qsConstr <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   SatisfiesCrossRelationConstraints
                                     Ridx Ridx' tup
                                     (GetRelation qsHint Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetRelation qsHint Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
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
        (schConstr_self <- {b | decides b (SatisfiesSchemaConstraints Ridx tup tup)};
         schConstr <-
                   {b | decides b
                      (forall tup',
                         GetUnConstrRelation qs Ridx tup'
                         -> SatisfiesSchemaConstraints Ridx tup tup')};
         schConstr' <-
                    {b |
                     decides
                       b
                       (forall tup',
                          GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx tup' tup)};
         qsConstr <- (@Iterate_Decide_Comp _
                                           (fun Ridx' =>
                                              SatisfiesCrossRelationConstraints
                                     Ridx Ridx' tup
                                     (GetUnConstrRelation qs Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetUnConstrRelation qs Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (EnsembleInsert tup (GetUnConstrRelation qs Ridx))));
            ret match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                (UpdateUnConstrRelation qs Ridx (EnsembleInsert tup (GetUnConstrRelation qs Ridx)), true)
              | _, _, _, _, _ => (qs, false)
            end).
  Proof.
    intros.
    setoid_rewrite refineEquiv_pick_eq'.
    unfold DropQSConstraints_AbsR in *; intros; subst.
    rewrite QSInsertSpec_refine with (default := ret or).
    unfold refine; intros; subst.
      do 5 (apply_in_hyp computes_to_inv; destruct_ex; split_and).
      repeat rewrite GetRelDropConstraints in *.
      (* These assert are gross. Need to eliminate them. *)
      assert ((fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          SatisfiesCrossRelationConstraints Ridx Ridx' tup
            (GetUnConstrRelation (DropQSConstraints or) Ridx')) =
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                 SatisfiesCrossRelationConstraints Ridx Ridx' tup
                                                   (GetRelation or Ridx'))) as rewriteSat
        by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
            reflexivity); rewrite rewriteSat in H3; clear rewriteSat.
      assert ((fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          Ridx' <> Ridx ->
          forall
            tup' : @IndexedTuple
                     (schemaHeading
                        (relSchema
                           (nth_Bounded relName (qschemaSchemas qsSchema)
                              Ridx'))),
          GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
          SatisfiesCrossRelationConstraints Ridx' Ridx tup'
            (EnsembleInsert tup (GetRelation or Ridx))) =
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
      Ridx' <> Ridx ->
      forall
        tup' : @IndexedTuple
                 (schemaHeading
                    (relSchema
                       (nth_Bounded relName (qschemaSchemas qsSchema) Ridx'))),
      GetRelation or Ridx' tup' ->
      SatisfiesCrossRelationConstraints Ridx' Ridx tup'
                                        (EnsembleInsert tup (GetRelation or Ridx))))
          as rewriteSat
            by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
                reflexivity); rewrite rewriteSat in H4; clear rewriteSat.
      (* Resume not-terribleness *)
      generalize (Iterate_Decide_Comp_BoundedIndex _ _ _ H3) as H3';
      generalize (Iterate_Decide_Comp_BoundedIndex _ _ _ H4) as H4'; intros.
      revert H3 H4.
      repeat apply_in_hyp computes_to_inv.
      econstructor 2 with
      (comp_a_value := match x as x', x0 as x0', x1 as x1', x2 as x2', x3 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => (@Insert_Valid _ or Ridx tup H0 H1 H H2 H3, true)
                          | _, _, _, _, _ => fun _ _ _ _ _ => (or, false)
                        end H0 H1 H2 H3' H4').
      econstructor 2 with (comp_a_value :=  match x as x', x0 as x0', x1 as x1', x2 as x2', x3 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => @Insert_Valid _ or Ridx tup H0 H1 H H2 H3
                          | _, _, _, _, _ => fun _ _ _ _ _ => or
                        end H0 H1 H2 H3' H4').
      repeat (econstructor; eauto).
      repeat find_if_inside; try econstructor; simpl in *.
      unfold GetRelation, Insert_Valid, UpdateUnConstrRelation,
      UpdateRelation, EnsembleInsert ; simpl; split; intros; eauto.
      rewrite ith_replace_BoundIndex_neq; eauto using string_dec; simpl.
      rewrite ith_replace_BoundIndex_eq; unfold EnsembleInsert, GetRelation;
      simpl; intuition.
      econstructor.
      econstructor 3 with (v :=  match x as x', x0 as x0', x1 as x1', x2 as x2', x3 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => true
                          | _, _, _, _, _ => fun _ _ _ _ _ => false
                        end H0 H1 H2 H3' H4').
      repeat find_if_inside; simpl;
      try (solve [unfold not; let H := fresh in intros H; eapply NIntup; eapply H;
      unfold EnsembleInsert; eauto]).
      intros; rewrite <- GetRelDropConstraints.
      unfold Insert_Valid, GetUnConstrRelation, DropQSConstraints,
      UpdateRelation; simpl.
      rewrite <- ith_Bounded_imap, ith_replace_BoundIndex_eq; simpl;
      tauto.

      repeat find_if_inside; subst; repeat econstructor.

      simpl.
      repeat find_if_inside; subst; repeat econstructor.
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl.
      unfold GetRelation, Insert_Valid, UpdateUnConstrRelation,
      UpdateRelation; rewrite imap_replace_BoundedIndex; simpl; eauto using string_dec.
  Qed.

  Lemma freshIdx2UnConstr {qsSchema} qs Ridx
  : refine {bound | forall tup : IndexedTuple,
                      @GetUnConstrRelation qsSchema qs Ridx tup ->
                      tupleIndex tup <> bound}
           {bound | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) bound}.
  Proof.
    unfold UnConstrFreshIdx; intros v Comp_v; econstructor.
    inversion_by computes_to_inv; intros.
    apply Comp_v in H; omega.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema )
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx)))
           (or : QueryStructure qsSchema)
           refined_schConstr_self refined_schConstr refined_schConstr'
           refined_qsConstr refined_qsConstr',
      refine {b | decides b (SatisfiesSchemaConstraints Ridx tup tup)}
             refined_schConstr_self
      -> refine {b | decides b
                             (forall tup',
                                GetUnConstrRelation qs Ridx tup'
                                -> SatisfiesSchemaConstraints Ridx tup tup')}
                refined_schConstr
      -> refine
           {b |
            decides
              b
              (forall tup',
                 GetUnConstrRelation qs Ridx tup'
                 -> SatisfiesSchemaConstraints Ridx tup' tup)}
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
                                                 Ridx' Ridx tup'
                                                 (EnsembleInsert
                                                    {| tupleIndex := idx;
                                                       indexedTuple := tup |}
                                                    (GetUnConstrRelation qs Ridx))))
              (refined_qsConstr' idx))
      -> DropQSConstraints_AbsR or qs ->
      refine
        (or' <- (idx <- Pick (freshIdx {| qsHint := or |} Ridx);
                 qs' <- Pick (QSInsertSpec {| qsHint := or |} Ridx
                                          {| tupleIndex := idx;
                                             indexedTuple := tup |});
                 b <- Pick (SuccessfulInsertSpec {| qsHint := or |} Ridx qs'
                                                 {| tupleIndex := idx;
                                                    indexedTuple := tup |});
                 ret (qs', b));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        (idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx};
         (schConstr_self <- refined_schConstr_self;
          schConstr <- refined_schConstr;
          schConstr' <- refined_schConstr';
          qsConstr <- refined_qsConstr ;
          qsConstr' <- (refined_qsConstr' idx);
          ret match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
                | true, true, true, true, true =>
                  (UpdateUnConstrRelation qs Ridx
                                          (EnsembleInsert
                                             {| tupleIndex := idx;
                                                indexedTuple := tup |}
                                                   (GetUnConstrRelation qs Ridx)), true)
                | _, _, _, _, _ => (qs, false)
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
    setoid_rewrite <- (QSInsertSpec_UnConstr_refine' _ {| tupleIndex := a; indexedTuple := tup |}).
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
                          Ridx' Ridx tup'
                          (EnsembleInsert
                             {| tupleIndex := idx;
                                indexedTuple := tup |}
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
                                                       -> CrossConstr (indexedTuple tup') (
                                                                        (EnsembleInsert
                                                                           {| tupleIndex := idx;
                                                                              indexedTuple := tup |}
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
                                          {| tupleIndex := idx;
                                             indexedTuple := tup |});
                 b <- Pick (SuccessfulInsertSpec {| qsHint := or |} Ridx qs'
                                                 {| tupleIndex := idx;
                                                    indexedTuple := tup |});
                 ret (qs', b));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        match (schemaConstraints (QSGetNRelSchema qsSchema Ridx)) with
            Some Constr =>
            idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx} ;
            (schConstr_self <- {b | decides b (Constr tup tup) };
                   schConstr <- {b | decides b
                                             (forall tup',
                                                GetUnConstrRelation qs Ridx tup'
                                                -> Constr tup tup')};
                   schConstr' <- {b | decides b
                                              (forall tup',
                                                   GetUnConstrRelation qs Ridx tup'
                                                   -> Constr tup' tup)};
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
                                                       -> CrossConstr (indexedTuple tup') (
                                                                        (EnsembleInsert
                                                                           {| tupleIndex := idx;
                                                                              indexedTuple := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end));
                   ret match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
                         | true, true, true, true, true =>
                           (UpdateUnConstrRelation qs Ridx
                                                   (EnsembleInsert
                                                      {| tupleIndex := idx;
                                                         indexedTuple := tup |}
                                                      (GetUnConstrRelation qs Ridx)), true)
                         | _, _, _, _, _ => (qs, false)
                       end)
          | None =>
            idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) idx};
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
                                                       -> CrossConstr (indexedTuple tup') (
                                                                        (EnsembleInsert
                                                                           {| tupleIndex := idx;
                                                                              indexedTuple := tup |}
                                                                           (GetUnConstrRelation qs Ridx))))
                                               | None => None
                                      end));
                   ret match qsConstr, qsConstr' with
                         | true, true =>
                           (UpdateUnConstrRelation qs Ridx
                                                     (EnsembleInsert
                                                        {| tupleIndex := idx;
                                                           indexedTuple := tup |}
                                                        (GetUnConstrRelation qs Ridx)), true)
                           | _, _ => (qs, false)
                         end)
        end.
    unfold QSInsert.
    intros; rewrite QSInsertSpec_UnConstr_refine;
    eauto using
          refine_SatisfiesSchemaConstraints_self,
    refine_SatisfiesSchemaConstraints,
    refine_SatisfiesSchemaConstraints',
    refine_SatisfiesCrossConstraints;
    [
    | intros; eapply refine_SatisfiesCrossConstraints'].
    destruct (schemaConstraints (QSGetNRelSchema qsSchema Ridx)).
    reflexivity.
    f_equiv; unfold pointwise_relation; intros.
    repeat setoid_rewrite refineEquiv_bind_bind.
    repeat setoid_rewrite refineEquiv_bind_unit; f_equiv.
  Qed.

End InsertRefinements.

  (* When we insert a tuple into a relation which has another relation has
     a foreign key into, we need to show that we haven't messed up any
     references (which is, of course, trivial. We should bake this into
     our the [QSInsertSpec_refine'] refinement itself by filtering out the
     irrelevant constraints somehow, but for now we can use the following
     tactic to rewrite them away. *)

  Ltac remove_trivial_insertion_constraints :=
          repeat match goal with
          |- context[EnsembleInsert _ (GetUnConstrRelation _ _) ] =>
          match goal with
              AbsR : DropQSConstraints_AbsR ?or ?nr
              |- context [
                     Pick
                       (fun b =>
                          decides b
                                  (forall tup' ,
                           GetUnConstrRelation ?r ?Ridx tup' ->
                           exists tup2,
                             EnsembleInsert ?tup (GetUnConstrRelation ?r ?Ridx') tup2 /\
                             (indexedTuple tup') ?attr = (indexedTuple tup2) ?attr'))] =>
              let neq := fresh in
              assert (Ridx <> Ridx') by (subst_strings; discriminate);
              let refine_trivial := fresh in
              assert
                (refine {b' |
                         decides b'
                                 (forall tup',
                                    (GetUnConstrRelation r Ridx) tup' ->
                                    exists
                                      tup2,
                                      EnsembleInsert tup (GetUnConstrRelation r Ridx') tup2 /\
                                      (indexedTuple tup') attr = (indexedTuple tup2) attr')} (ret true))
                as refine_trivial;
                [ let v := fresh in
                  let Comp_v := fresh in
                  intros v Comp_v;
                    apply computes_to_inv in Comp_v;
                    rewrite <- AbsR; subst;
                    repeat rewrite GetRelDropConstraints;
                    let tup' := fresh in
                    let In_tup' := fresh in
                    econstructor; simpl map; simpl; intros tup' In_tup';
                    unfold EnsembleInsert;
                    let H' := fresh in
                    pose proof (@crossConstr _ or Ridx Ridx' tup' neq In_tup') as H';
                      simpl map in *; simpl in *;
                      destruct H' as [? [? ?]]; eauto |
                  subst_strings; setoid_rewrite refine_trivial;
                  clear refine_trivial;
                  pose_string_ids; simplify with monad laws
                ] end end .

Tactic Notation "remove" "trivial" "insertion" "checks" :=
  (* Move all the binds we can outside the exists / computes
   used for abstraction, stopping when we've rewritten
         the bind in [QSInsertSpec]. *)
  repeat rewrite refineEquiv_bind_bind;
  etransitivity;
  [ repeat (apply refine_bind;
            [reflexivity
            | match goal with
                | |- context [Bind (Insert _ into _)%QuerySpec _] =>
                  unfold pointwise_relation; intros
                    end
                 ] );
    (* Pull out the relation we're inserting into and then
     rewrite [QSInsertSpec] *)
    match goal with
        H : DropQSConstraints_AbsR _ ?r_n
        |- context [(Insert ?n into ?R)%QuerySpec] =>
        let H' := fresh in
          (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                   after we've drilled under a bind, this tactic will fail because
                   typeclass resolution breaks down. Generalizing and applying gets
                   around this problem for reasons unknown. *)
        let H' := fresh in
        pose proof (@QSInsertSpec_UnConstr_refine_opt
                      _ r_n {| bindex := R |} n _ H) as H';
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

Tactic Notation "Split" "Constraint" "Checks" :=
  repeat (let b := match goal with
                     | [ |- context[if ?X then _ else _] ] => constr:(X)
                     | [ H : context[if ?X then _ else _] |- _ ]=> constr:(X)
                   end in
          let b_eq := fresh in
          eapply (@refine_if _ _ b); intros b_eq;
          simpl in *; repeat rewrite b_eq; simpl).

Tactic Notation "implement" "failed" "insert" :=
  repeat (rewrite refine_pick_val, refineEquiv_bind_unit; eauto);
  reflexivity.


Tactic Notation "drop" "constraints" "from" "insert" constr(methname) :=
  hone method methname;
  [ remove trivial insertion checks;
    (* The trivial insertion checks involve the fresh id,
       so we need to drill under the binder before
       attempting to remove them. *)
    rewrite refine_bind;
    [ | reflexivity |
      unfold pointwise_relation; intros;
      repeat remove_trivial_insertion_constraints;
      higher_order_1_reflexivity ];
    finish honing
  | ].
