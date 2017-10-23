Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List
        Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Computation
        Fiat.Computation.Refinements.Iterate_Decide_Comp
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.IterateBoundedIndex
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Insert
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements.

(* Facts about implements insert operations. *)

Section InsertRefinements.

  Hint Resolve crossConstr.
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
    (tup : _ )
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
    {| rawRels :=
         UpdateRelation (rawRels qs) Ridx {| rawRel := EnsembleInsert tup (GetRelation qs Ridx)|}
    |}.
  Next Obligation.
    unfold GetRelation.
    unfold SatisfiesAttributeConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ilist2.ith2 (rawRels qs) Ridx)) as X in *; destruct X; simpl in *.
    destruct (attrConstraints
                (Vector.nth (Vector.map schemaRaw (QSschemaSchemas qsSchema)) Ridx));
      eauto;
    unfold EnsembleInsert in *; simpl in *; intuition; subst; eauto.
  Defined.
  Next Obligation.
    unfold GetRelation.
    unfold SatisfiesTupleConstraints, QSGetNRelSchema, GetNRelSchema,
    GetRelation in *.
    set ((ilist2.ith2 (rawRels qs) Ridx )) as X in *; destruct X; simpl in *.
    destruct (tupleConstraints
       (Vector.nth (Vector.map schemaRaw (QSschemaSchemas qsSchema)) Ridx));
      eauto.
    unfold EnsembleInsert in *; simpl in *; intuition; subst; eauto.
    congruence.
  Qed.
  Next Obligation.
    caseEq (BuildQueryStructureConstraints qsSchema idx idx'); eauto.
    unfold SatisfiesCrossRelationConstraints, UpdateRelation in *;
    destruct (fin_eq_dec Ridx idx'); subst.

    - rewrite ilist2.ith_replace2_Index_eq; simpl.
      rewrite ilist2.ith_replace2_Index_neq in H1; eauto using string_dec.
      generalize (qsConstr' idx H0 _ H1); rewrite H; eauto.
    - rewrite ilist2.ith_replace2_Index_neq; eauto using string_dec.
      destruct (fin_eq_dec Ridx idx); subst.
      + rewrite ilist2.ith_replace2_Index_eq in H1; simpl in *; eauto.
        unfold EnsembleInsert in H1; destruct H1; subst; eauto.
        * generalize (qsConstr idx'); rewrite H; eauto.
        * pose proof (crossConstr qs idx idx') as X; rewrite H in X; eauto.
      + rewrite ilist2.ith_replace2_Index_neq in H1; eauto using string_dec.
        pose proof (crossConstr qs idx idx') as X; rewrite H in X; eauto.
  Qed.

  Lemma QSInsertSpec_refine' :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec qs Ridx tup))
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
                    GetRelation qs Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (EnsembleInsert tup (GetRelation qs Ridx) t)
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
           (Pick (QSInsertSpec qs Ridx tup))
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
                                     (GetRelation qs Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetRelation qs Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx (indexedElement tup')
                                       (EnsembleInsert tup (GetRelation qs Ridx))));
            match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (EnsembleInsert tup (GetRelation qs Ridx) t)
             }

              | _, _, _, _, _ => default
            end).
  Proof.
    intros.
    rewrite QSInsertSpec_refine'; f_equiv.
    unfold pointwise_relation; intros.
    repeat (f_equiv; unfold pointwise_relation; intros).
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv; eauto.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv; eauto.
  Qed.

    Lemma freshIdx_UnConstrFreshIdx_Equiv
    : forall qsSchema (qs : QueryStructure qsSchema) Ridx,
      refine {x : nat | freshIdx qs Ridx x}
             {idx : nat | UnConstrFreshIdx (GetRelation qs Ridx) idx}.
  Proof.
    unfold freshIdx, UnConstrFreshIdx, refine; intros.
    computes_to_inv.
    computes_to_econstructor; intros.
    apply H in H0.
    unfold RawTupleIndex; intro; subst.
    destruct tup; omega.
  Qed.

  Lemma refine_SuccessfulInsert :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup b,
      computes_to {idx | UnConstrFreshIdx (GetRelation qs Ridx) idx} b
      -> refine
           (b <- {result : bool |
                  decides result
                          (forall t : IndexedElement,
                              GetRelation qs Ridx t <->
                              EnsembleInsert {| elementIndex := b; indexedElement := tup |}
                                             (GetRelation qs Ridx) t)};
            ret (qs, b)) (ret (qs, false)).
  Proof.
    intros; computes_to_inv.
    unfold UnConstrFreshIdx in *.
    refine pick val false; simpl.
    - simplify with monad laws; reflexivity.
    - intro.
      unfold EnsembleInsert in H0.
      assert (GetRelation qs Ridx {| elementIndex := b; indexedElement := tup |}).
      eapply H0; intuition.
      apply H in H1; simpl in *; intuition.
  Qed.

  Corollary refine_SuccessfulInsert_Bind ResultT:
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup b (k : _ -> Comp ResultT),
      computes_to {idx | UnConstrFreshIdx (GetRelation qs Ridx) idx} b
      ->
       refine
     (x2 <- {x : bool |
            SuccessfulInsertSpec qs Ridx qs
              {| elementIndex := b; indexedElement := tup |} x};
      k (qs, x2)) (k (qs, false)).
  Proof.
    unfold SuccessfulInsertSpec; intros.
    rewrite <- refineEquiv_bind_unit with (f := k).
    rewrite <- refine_SuccessfulInsert by eauto.
    rewrite refineEquiv_bind_bind.
    setoid_rewrite refineEquiv_bind_unit; f_equiv.
  Qed.

  Lemma QSInsertSpec_refine_opt :
  forall qsSchema (qs : QueryStructure qsSchema) Ridx tup,
      refine
        (QSInsert qs Ridx tup)
        match (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)),
              (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)) with
            Some aConstr, Some tConstr =>
            idx <- {idx | UnConstrFreshIdx (GetRelation qs Ridx) idx} ;
            (schConstr_self <- {b | decides b (aConstr tup) };
                   schConstr <- {b | decides b
                                             (forall tup',
                                                GetRelation qs Ridx tup'
                                                -> tConstr tup (indexedElement tup'))};
                   schConstr' <- {b | decides b
                                              (forall tup',
                                                   GetRelation qs Ridx tup'
                                                   -> tConstr (indexedElement tup') tup)};
                   qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           If (fin_eq_dec Ridx Ridx') Then
                                             None
                                           Else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetRelation qs Ridx))))
                                               | None => None
                                      end));
                   match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
                   | true, true, true, true, true =>
                     qs' <- {qs' |
                      (forall Ridx',
                          Ridx <> Ridx' ->
                          GetRelation qs Ridx' =
                          GetRelation qs' Ridx')
                      /\ forall t,
                          GetRelation qs' Ridx t <->
                          (EnsembleInsert {| elementIndex := idx;
                                             indexedElement := tup |} (GetRelation qs Ridx) t)};
                         ret (qs', true)
                     | _, _, _, _, _ => ret (qs, false)
                       end)
              | Some aConstr, None =>
                idx <- {idx | UnConstrFreshIdx (GetRelation qs Ridx) idx} ;
                  (schConstr_self <- {b | decides b (aConstr tup) };
                   qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           If (fin_eq_dec Ridx Ridx') Then
                                             None
                                           Else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetRelation qs Ridx))))
                                               | None => None
                                      end));
                   match schConstr_self, qsConstr, qsConstr' with
                   | true, true, true =>
                     qs' <- {qs' |
                      (forall Ridx',
                          Ridx <> Ridx' ->
                          GetRelation qs Ridx' =
                          GetRelation qs' Ridx')
                      /\ forall t,
                          GetRelation qs' Ridx t <->
                          (EnsembleInsert {| elementIndex := idx;
                                             indexedElement := tup |} (GetRelation qs Ridx) t)};
                         ret (qs', true)
                     | _, _, _ => ret (qs, false)
                       end)
              | None, Some tConstr =>
                idx <- {idx | UnConstrFreshIdx (GetRelation qs Ridx) idx} ;
                  (schConstr <- {b | decides b
                                             (forall tup',
                                                GetRelation qs Ridx tup'
                                                -> tConstr tup (indexedElement tup'))};
                   schConstr' <- {b | decides b
                                              (forall tup',
                                                   GetRelation qs Ridx tup'
                                                   -> tConstr (indexedElement tup') tup)};
                   qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           If (fin_eq_dec Ridx Ridx') Then
                                             None
                                           Else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetRelation qs Ridx))))
                                               | None => None
                                      end));
                   match schConstr, schConstr', qsConstr, qsConstr' with
                   | true, true, true, true =>
                     qs' <- {qs' |
                      (forall Ridx',
                          Ridx <> Ridx' ->
                          GetRelation qs Ridx' =
                          GetRelation qs' Ridx')
                      /\ forall t,
                          GetRelation qs' Ridx t <->
                          (EnsembleInsert {| elementIndex := idx;
                                             indexedElement := tup |} (GetRelation qs Ridx) t)};
                         ret (qs', true)
                         | _, _, _, _ => ret (qs, false)
                       end)
              | None, None =>
                idx <- {idx | UnConstrFreshIdx (GetRelation qs Ridx) idx} ;
                  (qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           If (fin_eq_dec Ridx Ridx') Then
                                             None
                                           Else
                                             match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                               | Some CrossConstr =>
                                                 Some (
                                                     forall tup',
                                                       (GetRelation qs Ridx') tup'
                                                       -> CrossConstr (indexedElement tup') (
                                                                        (EnsembleInsert
                                                                           {| elementIndex := idx;
                                                                              indexedElement := tup |}
                                                                           (GetRelation qs Ridx))))
                                               | None => None
                                      end));
                   match qsConstr, qsConstr' with
                   | true, true =>
                                                               qs' <- {qs' |
                      (forall Ridx',
                          Ridx <> Ridx' ->
                          GetRelation qs Ridx' =
                          GetRelation qs' Ridx')
                      /\ forall t,
                          GetRelation qs' Ridx t <->
                          (EnsembleInsert {| elementIndex := idx;
                                             indexedElement := tup |} (GetRelation qs Ridx) t)};
                         ret (qs', true)
                         | _, _ => ret (qs, false)
                       end)
        end.
  Proof.
    unfold QSInsert.
    intros; simpl.
    unfold If_Then_Else.
    setoid_rewrite QSInsertSpec_refine with (default := ret qs).
    simplify with monad laws.
    setoid_rewrite refine_SatisfiesAttributeConstraints_self; simpl.
    match goal with
      |- context [attrConstraints ?R] => destruct (attrConstraints R)
    end.
    setoid_rewrite refine_SatisfiesTupleConstraints_Constr; simpl.
    setoid_rewrite refine_SatisfiesTupleConstraints_Constr'; simpl.
    match goal with
      |- context [tupleConstraints ?R] => destruct (tupleConstraints R)
    end.
    setoid_rewrite refine_SatisfiesCrossConstraints_Constr; simpl.
    rewrite freshIdx_UnConstrFreshIdx_Equiv.
    repeat (eapply refine_under_bind; intros).
    eapply refine_under_bind_both.
    unfold SatisfiesCrossRelationConstraints; simpl.
    setoid_rewrite refine_Iterate_Decide_Comp_equiv.
    eapply refine_Iterate_Decide_Comp.
    - simpl; intros; simpl in *.
      destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
      + congruence.
      + destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
    - simpl; intros.
      intro; apply H4.
      simpl in *; destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
      + destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
    - intros.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      unfold If_Then_Else.
      repeat find_if_inside; unfold SuccessfulInsertSpec;
      try (simplify with monad laws; eapply refine_SuccessfulInsert; eauto).
      + apply refine_under_bind; intros.
        refine pick val true; simpl.
        simplify with monad laws; reflexivity.
        intros; computes_to_inv; intuition;
        eapply H7; eauto.
    - simpl; simplify with monad laws.
      setoid_rewrite refine_SatisfiesCrossConstraints_Constr; simpl.
      rewrite freshIdx_UnConstrFreshIdx_Equiv.
      repeat (eapply refine_under_bind; intros).
      eapply refine_under_bind_both.
      unfold SatisfiesCrossRelationConstraints; simpl.
      setoid_rewrite refine_Iterate_Decide_Comp_equiv.
      eapply refine_Iterate_Decide_Comp.
      + simpl; intros; simpl in *.
        destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
        * congruence.
        * destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
      + simpl; intros.
        intro; apply H2.
        simpl in *; destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
        * destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
      + intros.
        repeat setoid_rewrite refine_If_Then_Else_Bind.
        unfold If_Then_Else.
        repeat find_if_inside; unfold SuccessfulInsertSpec;
        try (simplify with monad laws; eapply refine_SuccessfulInsert; eauto).
        * apply refine_under_bind; intros.
          refine pick val true; simpl.
          simplify with monad laws; reflexivity.
          intros; computes_to_inv; intuition;
          eapply H5; eauto.
    - simplify with monad laws.
      setoid_rewrite refine_SatisfiesTupleConstraints_Constr; simpl.
      setoid_rewrite refine_SatisfiesTupleConstraints_Constr'; simpl.
      match goal with
        |- context [tupleConstraints ?R] => destruct (tupleConstraints R)
      end.
      setoid_rewrite refine_SatisfiesCrossConstraints_Constr; simpl.
      rewrite freshIdx_UnConstrFreshIdx_Equiv.
      repeat (eapply refine_under_bind; intros).
      eapply refine_under_bind_both.
      unfold SatisfiesCrossRelationConstraints; simpl.
      setoid_rewrite refine_Iterate_Decide_Comp_equiv.
      eapply refine_Iterate_Decide_Comp.
      + simpl; intros; simpl in *.
        destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
      * congruence.
      * destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
      + simpl; intros.
        intro; apply H3.
         simpl in *; destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
        * destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
      + intros.
        repeat setoid_rewrite refine_If_Then_Else_Bind.
        unfold If_Then_Else.
        repeat find_if_inside; unfold SuccessfulInsertSpec;
        try (simplify with monad laws; eapply refine_SuccessfulInsert; eauto).
        * apply refine_under_bind; intros.
          refine pick val true; simpl.
          simplify with monad laws; reflexivity.
          intros; computes_to_inv; intuition;
          eapply H6; eauto.
      + simpl; simplify with monad laws.
        setoid_rewrite refine_SatisfiesCrossConstraints_Constr; simpl.
        rewrite freshIdx_UnConstrFreshIdx_Equiv.
        repeat (eapply refine_under_bind; intros).
        eapply refine_under_bind_both.
        unfold SatisfiesCrossRelationConstraints; simpl.
        setoid_rewrite refine_Iterate_Decide_Comp_equiv.
        eapply refine_Iterate_Decide_Comp.
      * simpl; intros; simpl in *.
        destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
        congruence.
        destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
      * simpl; intros.
        intro; apply H1.
        simpl in *; destruct (fin_eq_dec Ridx idx); simpl in *; substs; eauto.
        destruct (BuildQueryStructureConstraints qsSchema idx Ridx); eauto.
      * intros.
        repeat setoid_rewrite refine_If_Then_Else_Bind.
        unfold If_Then_Else.
        repeat find_if_inside; unfold SuccessfulInsertSpec;
        try (simplify with monad laws; eapply refine_SuccessfulInsert; eauto).
        apply refine_under_bind; intros.
        refine pick val true; simpl.
        simplify with monad laws; reflexivity.
        intros; computes_to_inv; intuition;
        eapply H4; eauto.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine' :
    forall qsSchema
           (qs : _ )
           (Ridx : _)
           (tup : _ )
           (or : _ )
           (NIntup : ~ GetUnConstrRelation qs Ridx tup),
      @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        (or' <- (qs' <- Pick (QSInsertSpec or Ridx tup);
                 b <- Pick (SuccessfulInsertSpec or Ridx qs' tup);
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
      assert ((fun Ridx' =>
          SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup)
            (GetUnConstrRelation (DropQSConstraints or) Ridx')) =
              (fun Ridx'  =>
                 SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup)
                                                   (GetRelation or Ridx'))) as rewriteSat
        by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
            reflexivity); rewrite rewriteSat in H'''; clear rewriteSat.
      assert ((fun Ridx'  =>
          Ridx' <> Ridx ->
          forall tup',
          GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
          SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
            (EnsembleInsert tup (GetRelation or Ridx))) =
              (fun Ridx' =>
      Ridx' <> Ridx ->
      forall tup',
        GetRelation or Ridx' tup' ->
        SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
                                          (EnsembleInsert tup (GetRelation or Ridx))))
          as rewriteSat
            by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
                reflexivity).
      rewrite GetRelDropConstraints in H', H'',  H''''.
      setoid_rewrite rewriteSat in H''''; clear rewriteSat.
      (* Resume not-terribleness *)
      generalize (Iterate_Decide_Comp_BoundedIndex _ _ H''') as H3';
      generalize (Iterate_Decide_Comp_BoundedIndex _ _ H'''') as H4'; intros.
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
      rewrite ilist2.ith_replace2_Index_neq; eauto using string_dec; simpl.
      rewrite ilist2.ith_replace2_Index_eq; unfold EnsembleInsert, GetRelation;
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
      rewrite <- ilist2.ith_imap2, ilist2.ith_replace2_Index_eq; simpl; tauto.
      simpl in *.
      unfold not; intros; apply NIntup.
      rewrite GetRelDropConstraints; eapply H0;
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl; eauto.
      unfold not; intros; apply NIntup;
      rewrite GetRelDropConstraints; eapply H0;
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl; eauto.
      unfold not; intros; apply NIntup;
      rewrite GetRelDropConstraints; eapply H0;
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl; eauto.
      unfold not; intros; apply NIntup;
      rewrite GetRelDropConstraints; eapply H0;
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl; eauto.
      unfold not; intros; apply NIntup;
      rewrite GetRelDropConstraints; eapply H0;
      unfold DropQSConstraints, Insert_Valid, EnsembleInsert; simpl; eauto.
      simpl in *.
      repeat find_if_inside; simpl; eauto.
      repeat find_if_inside; simpl; eauto.
      repeat computes_to_econstructor.
      unfold Insert_Valid, GetUnConstrRelation, DropQSConstraints,
      UpdateRelation; simpl;  eauto.
      computes_to_inv; subst.
      unfold Insert_Valid, GetUnConstrRelation, DropQSConstraints,
      UpdateUnConstrRelation; simpl;  eauto.
      rewrite ilist2.imap_replace2_Index, <- ilist2.ith_imap2.
      simpl; computes_to_econstructor.
  Qed.

  Lemma freshIdx2UnConstr {qsSchema} qs Ridx
  : refine {bound | forall tup,
                      @GetUnConstrRelation (QueryStructureSchemaRaw qsSchema) qs Ridx tup ->
                      RawTupleIndex tup <> bound}
           {bound | UnConstrFreshIdx (GetUnConstrRelation qs Ridx) bound}.
  Proof.
    unfold UnConstrFreshIdx; intros v Comp_v; computes_to_econstructor.
    computes_to_inv; intros.
    unfold RawTupleIndex in *; apply Comp_v in H; omega.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine :
    forall qsSchema qs Ridx tup or
           refined_schConstr_self refined_schConstr refined_schConstr'
           refined_qsConstr refined_qsConstr',
      refine {b | decides b (SatisfiesAttributeConstraints Ridx tup)}
             refined_schConstr_self
      -> refine {b | decides b
                             (forall tup' : @IndexedElement
                                              (@RawTuple
                                                 (@GetNRelSchemaHeading
                                                    (numRawQSschemaSchemas
                                                       (QueryStructureSchemaRaw
                                                          qsSchema))
                                               (qschemaSchemas
                                                  (QueryStructureSchemaRaw
                                                     qsSchema))
                                               _)),
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
      -> @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        (or' <- (idx <- Pick (freshIdx or Ridx);
                 qs' <- Pick (QSInsertSpec or Ridx
                                          {| elementIndex := idx;
                                             indexedElement := tup |});
                 b <- Pick (SuccessfulInsertSpec or Ridx qs'
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

  Local Transparent QSInsert.

  Definition UpdateUnConstrRelationInsertC {qsSchema} (qs : UnConstrQueryStructure qsSchema) Ridx tup :=
    ret (UpdateUnConstrRelation qs Ridx
                                (EnsembleInsert tup (GetUnConstrRelation qs Ridx))).

  Lemma QSInsertSpec_refine_subgoals ResultT :
    forall qsSchema (qs : QueryStructure qsSchema) qs' Ridx
           tup default success refined_schConstr_self
           refined_schConstr refined_schConstr'
           refined_qsConstr refined_qsConstr'
           (k : _ -> Comp ResultT),
      DropQSConstraints_AbsR qs qs'
      -> refine {b | decides b
                             (SatisfiesAttributeConstraints Ridx tup)}
                refined_schConstr_self
      -> refine {b |
                 decides
                   b
                   (forall tup',
                       GetUnConstrRelation qs' Ridx tup'
                       -> SatisfiesTupleConstraints Ridx tup (indexedElement tup'))}
                refined_schConstr
      -> (forall b',
             decides b'
                     (forall tup',
                         GetUnConstrRelation qs' Ridx tup'
                         -> SatisfiesTupleConstraints Ridx tup (indexedElement tup'))
             -> refine
                  {b |
                   decides
                     b
                     (forall tup',
                         GetUnConstrRelation qs' Ridx tup'
                         -> SatisfiesTupleConstraints Ridx (indexedElement tup') tup)}
                  (refined_schConstr' b'))
      -> refine
           (@Iterate_Decide_Comp_opt _
                                     (fun Ridx' =>
                                        match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs' Ridx'))
                                        | None => None
                                        end))
           refined_qsConstr
      -> (forall idx,
             UnConstrFreshIdx (GetUnConstrRelation qs' Ridx) idx
             -> refine
                  (@Iterate_Decide_Comp_opt _
                                            (fun Ridx' =>
                                               if (fin_eq_dec Ridx Ridx') then
                                                 None
                                               else
                                                 match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                                 | Some CrossConstr =>
                                                   Some (
                                                       forall tup',
                                                         (GetUnConstrRelation qs' Ridx') tup'
                                                         -> CrossConstr (indexedElement tup') (
                                                                          (EnsembleInsert
                                                                             {| elementIndex := idx;
                                                                                indexedElement := tup |}
                                                                             (GetUnConstrRelation qs' Ridx))))
                                                 | None => None
                                                 end))
                  (refined_qsConstr' idx))
      -> (forall idx qs' qs'',
             DropQSConstraints_AbsR qs' qs''
             -> UnConstrFreshIdx (GetRelation qs Ridx) idx
             -> (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs' Ridx')
             -> (forall t,
                    GetRelation qs' Ridx t <->
                    (EnsembleInsert
                       {| elementIndex := idx;
                          indexedElement := tup |}
                       (GetRelation qs Ridx) t))
             -> refine (k (qs', true))
                       (success qs''))
      -> refine (k (qs, false)) default
      -> refine
           (qs' <- QSInsert qs Ridx tup; k qs')
           (idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs' Ridx) idx} ;
              schConstr_self <- refined_schConstr_self;
              schConstr <- refined_schConstr;
              schConstr' <- refined_schConstr' schConstr;
              qsConstr <- refined_qsConstr;
              qsConstr' <- refined_qsConstr' idx;
              match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                qs'' <- UpdateUnConstrRelationInsertC qs' Ridx {| elementIndex := idx;
                                                                  indexedElement := tup |};
                  success qs''
              | _, _, _, _, _ => default
              end).
  Proof.
    intros.
    unfold QSInsert.
    simplify with monad laws.
    setoid_rewrite QSInsertSpec_refine with (default := ret qs).
    rewrite freshIdx_UnConstrFreshIdx_Equiv.
    simplify with monad laws.
    rewrite <- H, (GetRelDropConstraints qs).
    apply refine_under_bind_both; [reflexivity | intros].
    rewrite <- !GetRelDropConstraints; rewrite !H.
    repeat (apply refine_under_bind_both;
            [repeat rewrite <- (GetRelDropConstraints qs); eauto
            | intros]).
    computes_to_inv; eauto.
    rewrite refine_SatisfiesCrossConstraints_Constr; etransitivity; try eassumption.
    simpl; f_equiv; apply functional_extensionality; intros;
      rewrite <- H, GetRelDropConstraints; reflexivity.
    rewrite <- H, GetRelDropConstraints, refine_SatisfiesCrossConstraints'_Constr.
    etransitivity; try eapply H4.
    simpl; f_equiv; apply functional_extensionality; intros.
    rewrite <- H; rewrite !(GetRelDropConstraints qs); eauto.
    rewrite <- H, GetRelDropConstraints; computes_to_inv; eauto.
    repeat find_if_inside; try simplify with monad laws;
      try solve [rewrite refine_SuccessfulInsert_Bind; eauto].
    apply Iterate_Decide_Comp_BoundedIndex in H11.
    apply Iterate_Decide_Comp_BoundedIndex in H12.
    computes_to_inv; simpl in *.
    assert (forall tup' : IndexedElement,
               GetRelation qs Ridx tup' ->
               SatisfiesTupleConstraints (qsSchema := qsSchema) Ridx
                                         (indexedElement {| elementIndex := a; indexedElement := tup |})
                                         (indexedElement tup')) as H9'
        by (intros; apply H9; rewrite <- H, GetRelDropConstraints; eassumption).
    assert (forall Ridx' : Fin.t (numRawQSschemaSchemas qsSchema),
               Ridx' <> Ridx ->
               forall tup' : IndexedElement,
                 GetRelation qs Ridx' tup' ->
                 SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
                                                   (EnsembleInsert {| elementIndex := a; indexedElement := tup |}
                                                                   (GetRelation qs Ridx)))
      as H12' by (intros; rewrite <- GetRelDropConstraints, H; eauto).
    assert (forall tup' : IndexedElement,
               GetRelation qs Ridx tup' ->
               SatisfiesTupleConstraints (qsSchema := qsSchema) Ridx (indexedElement tup')
                                         (indexedElement {| elementIndex := a; indexedElement := tup |})) as H10'
        by (intros; apply H10; rewrite <- H, GetRelDropConstraints; eassumption).
    refine pick val (Insert_Valid qs {| elementIndex := a;
                                        indexedElement := tup |} H9' H10' H8 H11 H12').
    simplify with monad laws.
    refine pick val true.
    unfold UpdateUnConstrRelationInsertC.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_unit.
    eapply H5.
    rewrite <- H.
    rewrite GetRelDropConstraints.
    unfold DropQSConstraints_AbsR, DropQSConstraints, Insert_Valid; simpl.
    unfold UpdateRelation.
    rewrite ilist2.imap_replace2_Index; reflexivity.
    eauto.
    intros; unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_neq; simpl; eauto.
    intros; unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
    unfold SuccessfulInsertSpec; simpl.
    unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
    split; intros.
    unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_neq; simpl; eauto.
    rewrite <- H; rewrite GetRelDropConstraints.
    unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
  Qed.

  Lemma QSInsertSpec_refine_short_circuit' :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec qs Ridx tup))
           (schConstr_self <-
                           {b |
                            decides b
                                    (SatisfiesAttributeConstraints Ridx (indexedElement tup))};
              If schConstr_self Then
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))};
               If schConstr Then
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))};
               If schConstr' Then
            qsConstr <- {b | decides b
                                     (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup) (GetRelation qs Ridx'))};
               If qsConstr Then
            qsConstr' <- {b | decides
                                b
                                (forall Ridx',
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     (GetRelation qs Ridx') tup'
                                     -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx (indexedElement tup')
                                       (EnsembleInsert tup (GetRelation qs Ridx)))};
               If qsConstr' Then
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (EnsembleInsert tup (GetRelation qs Ridx) t)
                }
                Else default
                Else default
                Else default
                Else default
                Else default).
  Proof.
    intros qsSchema qs Ridx tup default v Comp_v;
    computes_to_inv.
      destruct v0;
      [ simpl in *; computes_to_inv; destruct v0;
        [ simpl in *; computes_to_inv;  destruct v0;
          [simpl in *; computes_to_inv;  destruct v0;
            [ simpl in *; computes_to_inv;  destruct v0;
              [ repeat (computes_to_inv; destruct_ex; split_and); simpl in *;
                computes_to_econstructor; unfold QSInsertSpec; eauto |
              ]
            | ]
          | ]
        |  ]
      |  ];
      cbv delta [decides] beta in *; simpl in *;
      repeat (computes_to_inv; destruct_ex); eauto.
      intuition.
      unfold QSInsertSpec; intros; intuition.
      unfold QSInsertSpec; intros; intuition.
      unfold QSInsertSpec; intros; intuition.
      unfold QSInsertSpec; intros; intuition.
      unfold QSInsertSpec; intros; intuition.
      computes_to_econstructor; unfold QSInsertSpec; intros;
        intros.
      solve [elimtype False; intuition].
  Qed.

  Lemma QSInsertSpec_refine_short_circuit :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec qs Ridx tup))
           (schConstr_self <- {b | decides b
                                           (SatisfiesAttributeConstraints Ridx (indexedElement tup))};
              If schConstr_self Then
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))};
              If schConstr Then
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))};
              If schConstr' Then
            qsConstr <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   SatisfiesCrossRelationConstraints
                                     Ridx Ridx' (indexedElement tup)
                                     (GetRelation qs Ridx')));
              If qsConstr Then
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetRelation qs Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx (indexedElement tup')
                                       (EnsembleInsert tup (GetRelation qs Ridx))));
              If qsConstr' Then
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (EnsembleInsert tup (GetRelation qs Ridx) t)
                } Else default
                Else default
                Else default
                Else default
                Else default).
  Proof.
    intros.
    rewrite QSInsertSpec_refine_short_circuit'; f_equiv.
    unfold pointwise_relation; intros.
    apply refine_If_Then_Else; f_equiv; unfold pointwise_relation; intros.
    apply refine_If_Then_Else; f_equiv; unfold pointwise_relation; intros.
    apply refine_If_Then_Else; f_equiv; unfold pointwise_relation; intros.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv; eauto.
    apply refine_If_Then_Else; f_equiv; unfold pointwise_relation; intros.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv; eauto.
  Qed.

  Lemma QSInsertSpec_refine_subgoals_short_circuit ResultT :
    forall qsSchema (qs : QueryStructure qsSchema) qs' Ridx
           tup default success refined_schConstr_self
           refined_schConstr refined_schConstr'
           refined_qsConstr refined_qsConstr'
           (k : _ -> Comp ResultT),
      DropQSConstraints_AbsR qs qs'
      -> refine {b | decides b
                             (SatisfiesAttributeConstraints Ridx tup)}
                refined_schConstr_self
      -> refine {b |
                 decides
                   b
                   (forall tup',
                       GetUnConstrRelation qs' Ridx tup'
                       -> SatisfiesTupleConstraints Ridx tup (indexedElement tup'))}
                refined_schConstr
      -> (forall b',
             decides b'
                     (forall tup',
                         GetUnConstrRelation qs' Ridx tup'
                         -> SatisfiesTupleConstraints Ridx tup (indexedElement tup'))
             -> refine
                  {b |
                   decides
                     b
                     (forall tup',
                         GetUnConstrRelation qs' Ridx tup'
                         -> SatisfiesTupleConstraints Ridx (indexedElement tup') tup)}
                  (refined_schConstr' b'))
      -> refine
           (@Iterate_Decide_Comp.Iterate_Decide_Comp_opt _
                                                         (fun Ridx' =>
                                                            match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                                            | Some CrossConstr =>
                                                              Some (CrossConstr tup (GetUnConstrRelation qs' Ridx'))
                                                            | None => None
                                                            end))
           refined_qsConstr
      -> (forall idx,
             UnConstrFreshIdx (GetUnConstrRelation qs' Ridx) idx
             -> refine
                  (@Iterate_Decide_Comp.Iterate_Decide_Comp_opt _
                                                                (fun Ridx' =>
                                                                   if (fin_eq_dec Ridx Ridx') then
                                                                     None
                                                                   else
                                                                     match (BuildQueryStructureConstraints qsSchema Ridx' Ridx) with
                                                                     | Some CrossConstr =>
                                                                       Some (
                                                                           forall tup',
                                                                             (GetUnConstrRelation qs' Ridx') tup'
                                                                             -> CrossConstr (indexedElement tup') (
                                                                                              (EnsembleInsert
                                                                                                 {| elementIndex := idx;
                                                                                                    indexedElement := tup |}
                                                                                                 (GetUnConstrRelation qs' Ridx))))
                                                                     | None => None
                                                                     end))
                  (refined_qsConstr' idx))
      -> (forall idx qs' qs'',
             DropQSConstraints_AbsR qs' qs''
             -> UnConstrFreshIdx (GetRelation qs Ridx) idx
             -> (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs' Ridx')
             -> (forall t,
                    GetRelation qs' Ridx t <->
                    (EnsembleInsert
                       {| elementIndex := idx;
                          indexedElement := tup |}
                       (GetRelation qs Ridx) t))
             -> refine (k (qs', true))
                       (success qs''))
      -> refine (k (qs, false)) default
      -> refine
           (qs' <- QSInsert qs Ridx tup; k qs')
           (idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation qs' Ridx) idx} ;
              schConstr_self <- refined_schConstr_self;
              If schConstr_self Then
                 schConstr <- refined_schConstr;
              If schConstr Then
                 schConstr' <- refined_schConstr' schConstr;
              If schConstr' Then
                 qsConstr <- refined_qsConstr;
              If qsConstr Then
                 qsConstr' <- refined_qsConstr' idx;
              If qsConstr' Then
                 qs'' <- UpdateUnConstrRelationInsertC qs' Ridx {| elementIndex := idx;
                                                                   indexedElement := tup |};
              success qs''
                      Else default
                      Else default
                      Else default
                      Else default
                      Else default
           ).
  Proof.
    intros; unfold QSInsert.
    simplify with monad laws.
    setoid_rewrite QSInsertSpec_refine_short_circuit with (default := ret qs).
    rewrite freshIdx_UnConstrFreshIdx_Equiv.
    simplify with monad laws.
    rewrite <- !H, (GetRelDropConstraints qs).
    apply refine_under_bind_both; [reflexivity | intros].
    apply refine_under_bind_both; [eassumption | intros].
    rewrite refine_If_Then_Else_Bind.
    eapply refine_if; intros; subst; simpl; try simplify with monad laws.
    apply refine_under_bind_both; [eauto | intros].
    rewrite <- H1; simpl.
    rewrite <- (GetRelDropConstraints qs), H; reflexivity.
    rewrite refine_If_Then_Else_Bind.
    eapply refine_if; intros; subst; simpl; try simplify with monad laws.
    apply refine_under_bind_both; [eauto | intros].
    rewrite <- H2; simpl.
    rewrite <- (GetRelDropConstraints qs), H; reflexivity.
    computes_to_inv; simpl in *; eauto.
    rewrite <- !GetRelDropConstraints in H9; rewrite !H in H9.
    eauto.
    rewrite refine_If_Then_Else_Bind.
    eapply refine_if; intros; subst; simpl; try simplify with monad laws.
    apply refine_under_bind_both; [eauto | intros].
    rewrite <- H3; simpl.
    etransitivity.
    apply refine_SatisfiesCrossConstraints_Constr.
    f_equiv.
    apply functional_extensionality; intro.
    destruct (BuildQueryStructureConstraints qsSchema Ridx x).
    rewrite <- (GetRelDropConstraints qs), H; reflexivity.
    reflexivity.
    rewrite refine_If_Then_Else_Bind.
    eapply refine_if; intros; subst; simpl; try simplify with monad laws.
    apply refine_under_bind_both; [eauto | intros].
    rewrite <- H4; simpl.
    etransitivity.
    apply refine_SatisfiesCrossConstraints'_Constr.
    f_equiv.
    apply functional_extensionality; intro.
    simpl.
    find_if_inside; eauto.
    destruct (BuildQueryStructureConstraints qsSchema x Ridx).
    rewrite <- (GetRelDropConstraints qs), H.
    rewrite <- (GetRelDropConstraints qs), H.
    reflexivity.
    reflexivity.
    computes_to_inv; simpl in *; subst.
    rewrite <- H, (GetRelDropConstraints qs); eauto.
    rewrite refine_If_Then_Else_Bind.
    eapply refine_if.
    simpl in *; intros; subst; simpl; computes_to_inv; simpl in *.
    assert (forall tup' : IndexedElement,
               GetRelation qs Ridx tup' ->
               SatisfiesTupleConstraints (qsSchema := qsSchema) Ridx
                                         (indexedElement {| elementIndex := a; indexedElement := tup |})
                                         (indexedElement tup')) as H9'
        by (intros; apply H9; try rewrite <- H, GetRelDropConstraints; eassumption).
    assert (forall Ridx' : Fin.t (numRawQSschemaSchemas qsSchema),
               Ridx' <> Ridx ->
               forall tup' : IndexedElement,
                 GetRelation qs Ridx' tup' ->
                 SatisfiesCrossRelationConstraints Ridx' Ridx (indexedElement tup')
                                                   (EnsembleInsert {| elementIndex := a; indexedElement := tup |}
                                                                   (GetRelation qs Ridx)))
      as H12' by 
          (apply Iterate_Decide_Comp_BoundedIndex in H12;
           computes_to_inv; subst; simpl in *; apply H12).
    assert (forall tup' : IndexedElement,
               GetRelation qs Ridx tup' ->
               SatisfiesTupleConstraints (qsSchema := qsSchema) Ridx (indexedElement tup')
                                         (indexedElement {| elementIndex := a; indexedElement := tup |})) as H10'
        by (intros; apply H10; try rewrite <- H, GetRelDropConstraints; eassumption).
    assert (forall Ridx' : Fin.t (numRawQSschemaSchemas qsSchema),
               SatisfiesCrossRelationConstraints (qsSchema := qsSchema) Ridx Ridx' (indexedElement {| elementIndex := a; indexedElement := tup |})
                                                 (GetRelation qs Ridx'))
      as H11'.
    (apply Iterate_Decide_Comp_BoundedIndex in H11;
           computes_to_inv; subst; simpl in *; apply H11).
    refine pick val (Insert_Valid qs {| elementIndex := a;
                                        indexedElement := tup |} H9' H10' H8 H11' H12').
    simplify with monad laws.
    refine pick val true.
    unfold UpdateUnConstrRelationInsertC.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_unit.
    eapply H5.
    rewrite H.
    unfold DropQSConstraints_AbsR, DropQSConstraints, Insert_Valid; simpl.
    unfold UpdateRelation.
    rewrite ilist2.imap_replace2_Index; try reflexivity.
    simpl.
    unfold UpdateUnConstrRelation; simpl.
    rewrite <- H.
    rewrite GetRelDropConstraints; reflexivity.
    apply H7.
    intros.
    intros; unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    simpl.
    rewrite ilist2.ith_replace2_Index_neq; simpl; eauto.
    intros; unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
    unfold SuccessfulInsertSpec; simpl.
    unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
    split; intros.
    unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    rewrite ilist2.ith_replace2_Index_neq; simpl; eauto.
    rewrite <- GetRelDropConstraints.
    unfold Insert_Valid, GetRelation, UpdateRelation; simpl.
    unfold DropQSConstraints, GetUnConstrRelation; simpl.
    rewrite ilist2.imap_replace2_Index; simpl.
    rewrite ilist2.ith_replace2_Index_eq; simpl; reflexivity.
    intros; subst; computes_to_inv; simpl.
    simplify with monad laws.
    refine pick val _; try simplify with monad laws; eauto.
    unfold SuccessfulInsertSpec.
    computes_to_inv; simpl in *; subst.
    intro.
    pose proof (proj2 (H13 _) (or_introl (eq_refl _))).
    apply H7 in H14; simpl in H14; omega.
    refine pick val _; try simplify with monad laws; eauto.
    unfold SuccessfulInsertSpec.
    computes_to_inv; simpl in *; subst.
    intro.
    pose proof (proj2 (H12 _) (or_introl (eq_refl _))).
    apply H7 in H13; simpl in H13; omega.
    refine pick val _; try simplify with monad laws; eauto.
    unfold SuccessfulInsertSpec.
    computes_to_inv; simpl in *; subst.
    intro.
    pose proof (proj2 (H11 _) (or_introl (eq_refl _))).
    apply H7 in H12; simpl in H12; omega.
    refine pick val _; try simplify with monad laws; eauto.
    unfold SuccessfulInsertSpec.
    computes_to_inv; simpl in *; subst.
    intro.
    pose proof (proj2 (H10 _) (or_introl (eq_refl _))).
    apply H7 in H11; simpl in H11; omega.
    refine pick val _; try simplify with monad laws; eauto.
    unfold SuccessfulInsertSpec.
    computes_to_inv; simpl in *; subst.
    intro.
    pose proof (proj2 (H9 _) (or_introl (eq_refl _))).
    apply H7 in H10; simpl in H10; omega.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine_opt :
    forall qsSchema
           qs
           or
           (Ridx : Fin.t _) tup,
      @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        (or' <- (idx <- Pick (freshIdx or Ridx);
                 qs' <- Pick (QSInsertSpec or Ridx
                                          {| elementIndex := idx;
                                             indexedElement := tup |});
                 b <- Pick (SuccessfulInsertSpec or Ridx qs'
                                                 {| elementIndex := idx;
                                                    indexedElement := tup |});
                 ret (qs', b));
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        match (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)),
              (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)) with
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
                   qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           if (fin_eq_dec Ridx Ridx') then
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
                   qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           if (fin_eq_dec Ridx Ridx') then
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
                   qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           if (fin_eq_dec Ridx Ridx') then
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
                  (qsConstr <- (@Iterate_Decide_Comp_opt _
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end));
                   qsConstr' <- (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           if (fin_eq_dec Ridx Ridx') then
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
    destruct (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx));
      destruct (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)).
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
Arguments SatisfiesCrossRelationConstraints  _ _ _ _ _ / .
Arguments BuildQueryStructureConstraints  _ _ _ / .
Arguments BuildQueryStructureConstraints_cons / .
Arguments GetNRelSchemaHeading _  _ _ / .
Arguments id  _ _ / .

Create HintDb refine_keyconstraints discriminated.
(*Hint Rewrite refine_Any_DecideableSB_True : refine_keyconstraints.*)

Arguments ith_Bounded _ _ _ _ _ _ / .
Arguments SatisfiesTupleConstraints _ _ _ _ / .
Arguments GetUnConstrRelation : simpl never.
Arguments UpdateUnConstrRelation : simpl never.
Arguments replace_BoundedIndex : simpl never.

Opaque UpdateUnConstrRelationInsertC.
