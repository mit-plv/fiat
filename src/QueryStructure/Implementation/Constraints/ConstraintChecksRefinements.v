Require Export
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List
        Coq.Arith.Compare_dec
        Coq.Bool.Bool
        Coq.Strings.String
        Fiat.Common.BoolFacts
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.List.ListFacts
        Fiat.Common.LogicFacts
        Fiat.Common.DecideableEnsembles
        Fiat.Computation.Refinements.Iterate_Decide_Comp
        Fiat.Computation.Refinements.General
        Fiat.QueryStructure.Specification.Constraints.tupleAgree
        Fiat.QueryStructure.Specification.Operations.Mutate.

Import Lists.List.ListNotations.

Unset Implicit Arguments.

Local Transparent Count Query_For.

Section ConstraintCheckRefinements.
  Hint Resolve crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesAttributeConstraints
       SatisfiesTupleConstraints.

  Fixpoint List_Query_eqT
           (attrlist : list Type)
    : Type
    := match attrlist with
       | [ ] => unit
       | attr :: attrlist' =>
         prod (Query_eq attr) (List_Query_eqT attrlist')
       end.

  Fixpoint Tuple_Agree_eq'
           {h : RawHeading}
           {attrlist : list (Attributes h)}
           (attr_eq_dec : List_Query_eqT (map (Domain h) attrlist))
           (tup tup' : @RawTuple h)
    : bool :=
    match attrlist return List_Query_eqT (map (Domain h) attrlist) ->
                          bool with
    | [ ] => fun _ => true
    |  attr :: attrlist' =>
       fun attr_eq_dec' =>
         if @A_eq_dec _ (fst attr_eq_dec') (GetAttributeRaw tup attr) (GetAttributeRaw tup' attr)
         then Tuple_Agree_eq' (snd attr_eq_dec') tup tup'
         else false
    end attr_eq_dec.

  Class List_Query_eq (As : list Type) :=
    { As_Query_eq : List_Query_eqT As}.

  Definition Tuple_Agree_eq {h} (attrlist : list (Attributes h))
          (attr_eq_dec : List_Query_eq (map (Domain h) attrlist)) tup tup' :=
    @Tuple_Agree_eq' h attrlist (@As_Query_eq _ attr_eq_dec) tup tup'.

  Lemma Tuple_Agree_eq_dec h attrlist attr_eq_dec (tup tup' : @RawTuple h) :
    tupleAgree tup tup' attrlist <->
    Tuple_Agree_eq attrlist attr_eq_dec tup tup' = true.
  Proof.
    destruct attr_eq_dec.
    induction attrlist; unfold tupleAgree in *; simpl in *; simpl;
    intuition;
    unfold Tuple_Agree_eq in *; simpl in *; find_if_inside; simpl; subst; eauto;
    try (eapply IHattrlist; eauto; fail);
    discriminate.
  Qed.

  Lemma Tuple_Agree_eq_dec' h attrlist attr_eq_dec (tup tup' : @RawTuple h) :
    ~ tupleAgree tup tup' attrlist <->
    Tuple_Agree_eq attrlist attr_eq_dec tup tup' = false.
  Proof.
    destruct attr_eq_dec.
    induction attrlist; unfold tupleAgree in *; simpl in *; simpl;
    intuition;
    unfold Tuple_Agree_eq in *; simpl in *; intuition;
    find_if_inside; simpl; subst; eauto.
    try (eapply IHattrlist; intros; eapply H).
    intros; intuition; subst; auto.
    eapply IHattrlist; intros; eauto.
  Qed.

  Definition Tuple_Agree_dec h attrlist
             (attr_eq_dec : List_Query_eq (map (Domain h) attrlist)) (tup tup' : @RawTuple h)
    : {tupleAgree tup tup' attrlist} + {~ tupleAgree tup tup' attrlist}.
  Proof.
    case_eq (Tuple_Agree_eq attrlist attr_eq_dec tup tup').
    left; eapply Tuple_Agree_eq_dec; eauto.
    right; eapply Tuple_Agree_eq_dec'; eauto.
  Defined.


  Lemma tupleAgree_sym :
    forall (heading: Heading) tup1 tup2 attrs,
      @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
  Proof.
    intros; unfold tupleAgree;
    split; intros; rewrite H; eauto.
  Qed.

  (* Consequences of ith_replace_BoundIndex_neq and ith_replace_BoundIndex_eq on updates *)

  Lemma refine_SatisfiesAttributeConstraints_self
    : forall (qsSchema : RawQueryStructureSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine {b | decides b (SatisfiesAttributeConstraints Ridx tup )}
             match (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) _)) with
               Some Constr => {b | decides b (Constr tup) }
             | None => ret true
             end.
  Proof.
    unfold SatisfiesAttributeConstraints.
    intros; match goal with
              |- context [attrConstraints ?A] => destruct (attrConstraints A)
            end;
    eauto using decides_True.
    reflexivity.
  Qed.

  Lemma refine_SatisfiesTupleConstraints_self
    : forall (qsSchema : RawQueryStructureSchema)
             (Ridx : Fin.t _)
             (tup tup' : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine {b | decides b (SatisfiesTupleConstraints Ridx tup tup')}
             match (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) _)) with
               Some Constr => {b | decides b (Constr tup tup') }
             | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; match goal with
              |- context [tupleConstraints ?A] => destruct (tupleConstraints A)
            end;
    eauto using decides_True.
    reflexivity.
  Qed.

  Lemma refine_SatisfiesTupleConstraints_Constr
    : forall (qsSchema : QueryStructureSchema)
             (qs : QueryStructure qsSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine {b | decides
                    b
                    (forall tup',
                        GetRelation qs Ridx tup'
                        -> SatisfiesTupleConstraints
                             Ridx
                             tup
                             (indexedElement tup'))}
             match (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) _)) with
               Some Constr =>
               {b | decides b (forall tup',
                                  GetRelation qs Ridx tup'
                                  -> Constr tup (indexedElement tup'))}
             | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; match goal with
              |- context [tupleConstraints ?A] => destruct (tupleConstraints A)
            end;
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesTupleConstraints_Constr'
    : forall (qsSchema : QueryStructureSchema)
             (qs : QueryStructure qsSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine {b | decides b
                          (forall tup',
                              GetRelation qs Ridx tup'
                              -> SatisfiesTupleConstraints Ridx (indexedElement tup') tup)}
             match tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) _) with
               Some Constr =>
               {b | decides b (forall tup',
                                  GetRelation qs Ridx tup'
                                  -> Constr (indexedElement tup') tup)}
             | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; match goal with
              |- context [tupleConstraints ?A] => destruct (tupleConstraints A)
            end;
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesCrossConstraints_Constr
    : forall (qsSchema : QueryStructureSchema)
             (qs : QueryStructure qsSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine
        (@Iterate_Decide_Comp _
                              (fun Ridx' =>
                                 SatisfiesCrossRelationConstraints
                                   Ridx Ridx' tup
                                   (GetRelation qs Ridx')))
        (@Iterate_Decide_Comp_opt _ (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                      | Some CrossConstr =>
                                        Some (CrossConstr tup (GetRelation qs Ridx'))
                                      | None => None
                                      end)) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.

  Lemma refine_SatisfiesTupleConstraints
    : forall (qsSchema : RawQueryStructureSchema)
             (qs : UnConstrQueryStructure qsSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine {b | decides
                    b
                    (forall tup',
                        GetUnConstrRelation qs Ridx tup'
                        -> SatisfiesTupleConstraints
                             Ridx
                             tup
                             (indexedElement tup'))}
             match (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) _)) with
               Some Constr =>
               {b | decides b (forall tup',
                                  GetUnConstrRelation qs Ridx tup'
                                  -> Constr tup (indexedElement tup'))}
             | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; match goal with
              |- context [tupleConstraints ?A] => destruct (tupleConstraints A)
            end;
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesTupleConstraints'
    : forall (qsSchema : RawQueryStructureSchema)
             (qs : UnConstrQueryStructure qsSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine {b | decides b
                          (forall tup',
                              GetUnConstrRelation qs Ridx tup'
                              -> SatisfiesTupleConstraints Ridx (indexedElement tup') tup)}
             match tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) _) with
               Some Constr =>
               {b | decides b (forall tup',
                                  GetUnConstrRelation qs Ridx tup'
                                  -> Constr (indexedElement tup') tup)}
             | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; match goal with
              |- context [tupleConstraints ?A] => destruct (tupleConstraints A)
            end;
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesCrossConstraints
    : forall (qsSchema : RawQueryStructureSchema)
             (qs : UnConstrQueryStructure qsSchema)
             (Ridx : Fin.t _)
             (tup : @RawTuple (rawSchemaHeading (GetNRelSchema (qschemaSchemas qsSchema) Ridx))),
      refine
        (@Iterate_Decide_Comp _
                              (fun Ridx' =>
                                 SatisfiesCrossRelationConstraints
                                   Ridx Ridx' tup
                                   (GetUnConstrRelation qs Ridx')))
        (@Iterate_Decide_Comp_opt _ (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                      | Some CrossConstr =>
                                        Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                      | None => None
                                      end)) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.

  Lemma refine_SatisfiesCrossConstraints'_Constr
    : forall (qsSchema : QueryStructureSchema)
             (qs : QueryStructure qsSchema)
             (Ridx : Fin.t _)
             tup idx,
      refine
        (@Iterate_Decide_Comp _
                              (fun Ridx' =>
                Ridx' <> Ridx
                -> forall tup',
                     (GetRelation qs Ridx') tup'
                     -> SatisfiesCrossRelationConstraints
                          Ridx' Ridx (indexedElement tup')
                          (EnsembleInsert
                             {| elementIndex := idx;
                                indexedElement := tup |}
                             (GetRelation qs Ridx))))
             (@Iterate_Decide_Comp_opt _
                                        (fun Ridx' =>
                                           if (fin_eq_dec Ridx Ridx') then
                                             None
                                           else
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
                                      end)).
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints.
    apply refine_Iterate_Decide_Comp_equiv; simpl; intros.
    simpl in *; destruct (fin_eq_dec Ridx idx0); subst.
    congruence.
    destruct (BuildQueryStructureConstraints qsSchema idx0 Ridx); eauto.
    simpl in *; destruct (fin_eq_dec Ridx idx0); subst; eauto.
    destruct (BuildQueryStructureConstraints qsSchema idx0 Ridx); eauto.
  Qed.

  Lemma refine_SatisfiesCrossConstraints'
  : forall qsSchema qs Ridx tup,
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
             (@Iterate_Decide_Comp_opt _
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
                                      end)).
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints.
    apply refine_Iterate_Decide_Comp_equiv; simpl; intros.
    destruct (fin_eq_dec Ridx idx0); subst.
    congruence.
    destruct (BuildQueryStructureConstraints qsSchema idx0 Ridx); eauto.
    intro; eapply H.
    destruct (fin_eq_dec Ridx idx0); subst; eauto.
    destruct (BuildQueryStructureConstraints qsSchema idx0 Ridx); eauto.
  Qed.

  Lemma tupleAgree_refl :
    forall (h : RawHeading)
           (tup : @RawTuple h)
           (attrlist : list (Attributes h)),
      tupleAgree tup tup attrlist.
  Proof.
    unfold tupleAgree; auto.
  Qed.

  Lemma refine_tupleAgree_refl_True :
    forall (h : RawHeading)
           (tup : @RawTuple h)
           (attrlist attrlist' : list (Attributes h)),
      refine {b |
              decides b (tupleAgree tup tup attrlist'
                         -> tupleAgree tup tup attrlist)}
             (ret true).
  Proof.
    unfold refine; intros;  computes_to_inv.
    subst; computes_to_econstructor; simpl; auto using tupleAgree_refl.
  Qed.

  Lemma refine_SatisfiesCrossConstraints_Pre (Q : Prop)
    : forall (qsSchema : RawQueryStructureSchema) qs
             (Ridx :Fin.t _)
             (tup : @RawTuple _),
      refine
        (@Iterate_Decide_Comp_Pre _
                                  (fun Ridx' =>
                                     SatisfiesCrossRelationConstraints
                                       Ridx Ridx' tup
                                       (GetUnConstrRelation qs Ridx')) Q)
        (@Iterate_Decide_Comp_opt_Pre _
                                       (fun Ridx' =>
                                          match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                          | Some CrossConstr =>
                                            Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                          | None => None
                                          end) Q) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp_Pre.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.

  Lemma DeletePrimaryKeysOK {qsSchema}
    : forall (qs : UnConstrQueryStructure qsSchema)
             (Ridx :Fin.t _)
             DeletedTuples
             attrlist1 attrlist2,
      refine {b | (forall tup tup',
                      elementIndex tup <> elementIndex tup'
                      -> GetUnConstrRelation qs Ridx tup
                      -> GetUnConstrRelation qs Ridx tup'
                      -> (FunctionalDependency_P attrlist1 attrlist2 (indexedElement tup) (indexedElement tup')))
                  -> decides b (Mutate.MutationPreservesTupleConstraints
                                  (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)
                                  (FunctionalDependency_P attrlist1 attrlist2)
             )}
             (ret true).
  Proof.
    unfold Mutate.MutationPreservesTupleConstraints, FunctionalDependency_P;
    intros * v Comp_v;  computes_to_inv; subst.
    computes_to_constructor; simpl.
    intros.
    unfold EnsembleDelete in *; destruct H1; destruct H2; eauto.
  Qed.

  Local Transparent Count.

  Lemma In_UnConstrQuery_In {qsSchema} {A}
    : forall (qs : UnConstrQueryStructure qsSchema) Ridx bod results,
      UnConstrQuery_In qs Ridx bod ↝ results
      -> forall (a : A), List.In a results ->
                         exists (tup' : IndexedRawTuple) results',
                           Ensembles.In _ (GetUnConstrRelation qs Ridx) tup'
                           /\ bod (indexedElement tup') ↝ results'
                           /\ List.In a results'.
  Proof.
    unfold UnConstrQuery_In, QueryResultComp; intros;
    computes_to_inv.
    unfold UnIndexedEnsembleListEquivalence in *; destruct_ex; intuition; subst.
    rewrite map_map in H'.
    remember (GetUnConstrRelation qs Ridx); clear Heqi;
    revert i a results H0 H' H H3;
    induction x; simpl in *; intros;
    computes_to_inv; subst.
    - simpl in H0; intuition.
    - apply in_app_or in H0; intuition.
      exists a; exists v; intuition; try eapply H; eauto.
      inversion H3; subst.
      destruct (IHx (fun tup => tup <> a /\ i tup) _ _ H1 H''); eauto.
      unfold Ensembles.In; intros; intuition; subst; eauto.
      eapply H in H6; intuition.
      apply H4; apply in_map; auto.
      apply H; intuition.
      destruct_ex; intuition.
      eexists x0, x1; intuition.
      apply H2.
  Qed.

  Lemma In_UnConstrQuery_In' {qsSchema} {A}
    : forall (qs : UnConstrQueryStructure qsSchema) Ridx
             (bod : RawTuple -> Comp (list A))
             results
             (a : A) (tup' : IndexedRawTuple),
      Ensembles.In _ (GetUnConstrRelation qs Ridx) tup'
      -> (forall results', bod (indexedElement tup') ↝ results'
                           -> List.In a results')
      -> UnConstrQuery_In qs Ridx bod ↝ results
      -> List.In a results.
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, Ensembles.In; intros.
    computes_to_inv.
    unfold UnIndexedEnsembleListEquivalence in *; destruct_ex; intuition; subst.
    rewrite map_map in H1'.
    remember (GetUnConstrRelation qs Ridx); clear Heqi;
    revert i a results H H0 H1 H1' H4;
    induction x; simpl in *; intros;
    computes_to_inv; subst.
    - simpl in *; intuition; eapply H1; eauto.
    - apply H1 in H; intuition; subst; apply in_or_app; eauto.
      right; inversion H4; subst.
      eapply (IHx (fun tup => tup <> a /\ i tup)); eauto.
      intuition; subst; eauto.
      apply H5; eauto using in_map.
      apply H1; eauto.
      unfold Ensembles.In; intuition; intros; eauto.
      rewrite H1 in H7; intuition.
      subst; eauto using in_map.
      apply H1; eauto.
  Qed.

  Lemma DeleteForeignKeysCheck {qsSchema}
    : forall (qs : UnConstrQueryStructure qsSchema)
             (Ridx Ridx' :Fin.t _)
             (DeletedTuples : Ensemble (RawTuple ))
             (Delete_dec : DecideableEnsemble DeletedTuples)
             (attr : Attributes _)
             (attr' : Attributes _)
             (tupmap : Domain _ attr
                       -> Domain _ attr')
             (AgreeDelete : forall tup tup',
                 tupleAgree tup tup' [attr] ->
                 DeletedTuples tup ->
                 DeletedTuples tup')
             (attr_eq_dec : Query_eq (Domain _ attr))
             (P : Prop)
             (ForeignKey_P_P :
                P -> (forall tup' : IndexedRawTuple,
                         GetUnConstrRelation qs Ridx' tup' ->
                         ForeignKey_P attr' attr tupmap (indexedElement tup')
                                      (GetUnConstrRelation qs Ridx)))
             (tup_map_inj : forall a a', tupmap a = tupmap a' -> a = a'),
      refine {b' |
              P ->
              decides b'
                      (MutationPreservesCrossConstraints
                         (GetUnConstrRelation qs Ridx')
                         (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)
                         (ForeignKey_P attr' attr tupmap))}
             (x <- Count (For (UnConstrQuery_In
                                 qs Ridx'
                                 (fun tup' =>
                                    UnConstrQuery_In
                                      qs Ridx
                                      (fun tup =>
                                         Where (DeletedTuples tup)
                                               Where (tupmap (GetAttributeRaw tup attr) = GetAttributeRaw tup' attr')
                                               Return ()))));
              ret (match x with
                     0  => true
                   | S _ => false
                   end)).
  Proof.
    simpl; unfold ForeignKey_P; intros.
    intros v Comp_v.
    computes_to_inv; destruct_ex; split_and.
    unfold Count in *;  computes_to_inv.
    destruct v0; simpl in *; subst;  computes_to_inv; subst;
    computes_to_constructor; simpl; unfold not;
    unfold MutationPreservesCrossConstraints; intros.
    - destruct (ForeignKey_P_P H _ H0) as [tup2 [In_tup2 Agree_tup2] ].
      eexists; intuition eauto.
      unfold EnsembleDelete; constructor; unfold In; intros; eauto.
      unfold Complement, Ensembles.In, not; intros.
      unfold Query_For in *;  computes_to_inv.
      rewrite Permutation_nil in Comp_v; symmetry in Comp_v'0; eauto.
      apply (fun x => In_UnConstrQuery_In' _ _ _ _ () _ H0 x Comp_v).
      intros results' H3;
        apply (fun x => In_UnConstrQuery_In' _ _ _ _ () _ In_tup2 x H3).
      intros results'0 H5.
      unfold Query_Where in H5; computes_to_inv;
      simpl in *; intuition.
      computes_to_inv; split_and.
      simpl in H4.
      unfold QSGetNRelSchema, GetNRelSchema in Agree_tup2; simpl in *.
      rewrite Agree_tup2 in H4; pose proof (H4 (refl_equal _)) as H';
      computes_to_inv; simpl in *; subst; simpl; eauto.
      apply Return_inv in H'; subst; simpl; intuition.
      rewrite Comp_v'; destruct v1; try discriminate; reflexivity.
    - unfold Query_For in *;  computes_to_inv.
      eapply In_UnConstrQuery_In with (a := tt) in Comp_v; destruct_ex;
      intuition.
      pose proof (H3 _ H2); pose proof (H0 _ H2); destruct_ex;
      intuition.
      eapply In_UnConstrQuery_In with (a := tt) in H1; destruct_ex;
      intuition.
      unfold EnsembleDelete in *; inversion H5; subst;
      unfold Ensembles.In, Complement, In in *.
      unfold Query_Where in H1; computes_to_inv;  intuition.
      case_eq (@dec _ _ Delete_dec (indexedElement x3)); intros.
      + apply Delete_dec in H1; pose proof (H13 H1) as H'.
        computes_to_inv; split_and.
        unfold indexedTuple in *.
        destruct (A_eq_dec (GetAttributeRaw (indexedElement x3) attr)
                           (GetAttributeRaw (indexedElement x1) attr)).
        * rewrite e in *; setoid_rewrite <- H9 in H15; subst;
          pose proof (H15 (refl_equal _)) as e'; computes_to_inv; simpl in *; subst.
          apply H12; eapply AgreeDelete; eauto.
          unfold tupleAgree; simpl; intros attr'' In_attr''; destruct In_attr'';
          [rewrite H17 in *; eauto | intuition ].
        * rewrite H16 in H11; simpl in *; eauto.
          intros;
            unfold QSGetNRelSchema, GetNRelSchema in *; simpl in *;
            setoid_rewrite <- H17 in H9; eauto.
      + rewrite H14 in H11; simpl in *; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
      + eapply Permutation_in; symmetry in Comp_v'; simpl; eauto.
        destruct v1; simpl in *;
        [ discriminate | destruct u; eauto].
  Qed.

  Lemma InsertForeignKeysCheck {qsSchema}
    : forall
      (qs : UnConstrQueryStructure qsSchema)
      (Ridx Ridx' :Fin.t _)
      (attr : Attributes _)
      (attr' : Attributes _)
      (tupmap : Domain _ attr' -> Domain _ attr)
      tup
      (ForeignKey_P_P :
         (forall tup' : IndexedRawTuple,
             GetUnConstrRelation qs Ridx tup' ->
             ForeignKey_P attr attr' tupmap (indexedElement tup')
                          (GetUnConstrRelation qs Ridx'))),
      Ridx <> Ridx'
      -> refine {b' |
                 decides b'
                         (forall tup',
                             (GetUnConstrRelation qs Ridx) tup' ->
                             ForeignKey_P attr attr' tupmap
                                          (indexedElement tup')
                                          (EnsembleInsert tup (GetUnConstrRelation qs Ridx')))}
                (ret true).
  Proof.
    intros; apply refine_pick_val; simpl; intros.
    unfold ForeignKey_P in *.
    destruct (ForeignKey_P_P _ H0) as [tup'' [In_tup'' ?] ];
      exists tup''; unfold EnsembleInsert; intuition.
  Qed.

End ConstraintCheckRefinements.

Lemma In_flatten_CompList {A} :
  forall (P : Ensemble A)
         (P_dec : forall a, P a \/ ~ P a)
         (il : list (@IndexedElement A))
         (l : list A)
         (a : A),
    In a l
    -> flatten_CompList
         (map
            (fun x1 : IndexedElement =>
               Where (P (indexedElement x1))
                     Return (indexedElement x1) ) il) ↝ l
    -> exists a', In a' il /\ indexedElement a' = a.
Proof.
  induction il; simpl; intros;  computes_to_inv; subst; simpl in *; intuition.
  apply in_app_or in H; intuition.
  unfold Query_Where in H0; computes_to_inv; intuition.
  destruct (P_dec (indexedElement a)).
  apply H in H0; unfold Query_Return in *; computes_to_inv; subst;
  simpl in H; exists a; simpl in H1; intuition; eauto.
  apply H2 in H0; subst; simpl in *; contradiction.
  destruct (IHil _ _ H1 H0') as [a' [In_a' a'_eq] ]; exists a'; split; eauto.
Qed.

Lemma For_computes_to_In :
  forall {heading} P,
    (forall a, P a \/ ~ P a) ->
    forall seq ens,
      computes_to (For (QueryResultComp (heading := heading) ens
                                        (fun tup => Where (P tup) Return tup))) seq ->
      forall x,
        List.In x seq -> (P x /\ (exists x0, ens x0 /\ indexedRawTuple x0 = x)).
Proof.
  unfold refine, decides;
  unfold Query_For, QueryResultComp; intros * excl;
  induction seq as [ | head seq' IH ]; intros.

  exfalso; intuition.

  computes_to_inv.

  pose proof (permutation_cons_in H') as in_x0.
  apply in_split in in_x0.
  destruct in_x0 as [ x0_before [ x0_after ? ] ]; subst.
  symmetry in H'. apply Permutation_cons_app_inv in H'.

  unfold UnIndexedEnsembleListEquivalence in H; destruct_ex; intuition; subst.

  rewrite map_map in H'0.
  destruct (flatten_CompList_app_cons_inv _ excl _ _ _ _ H'0) as [ x1_before [ x1_middle [ head' [ x1_after (_eq & in_orig & before & middle & after) ] ] ] ]; subst.

  unfold boxed_option in middle; simpl in middle.
  eapply Bind_inv in middle.
  destruct middle as [head'' (middle1 & middle2)].
  apply Pick_inv in middle1.
  apply Bind_inv in middle2.
  destruct middle1 as ( spec1 & spec2 ).
  destruct middle2 as [ nil' (ret_nil & ret_cons) ].
  apply Return_inv in ret_nil; subst.
  rewrite app_nil_r in *; subst.
  apply Return_inv in ret_cons; subst.



  rewrite singleton_neq_nil in spec2.
  destruct (excl (indexedRawTuple head')) as [ H'' | H'' ]; try solve [exfalso; intuition].
  specialize (spec1 H'').

  apply Return_inv in spec1.
  injection spec1; intros; subst.

  destruct H0.

  - subst x; eauto.
  - pose proof (flatten_CompList_app _ _ _ _ before after) as flatten_app.
    eapply IH; try assumption.
    computes_to_econstructor; [ | computes_to_constructor; symmetry; eassumption ].
    computes_to_econstructor.
    pose proof (EnsembleListEquivalence_slice x1_before x1_middle x1_after).
    instantiate (2 := (fun x0 : IndexedRawTuple => ens x0 /\ ~ In x0 x1_middle)).
    eapply PickComputes with (a := map indexedElement (x1_before ++ x1_after)).
    econstructor; split; eauto; intuition.
    destruct (H1 ens).
    unfold EnsembleListEquivalence; split; eauto using NoDup_IndexedElement.
    eapply H5; eauto.
    unfold Ensembles.In; split.
    eapply H; apply in_app_or in H2; intuition.
    intros; apply NoDup_IndexedElement in H3; eapply NoDup_app_inv'; eauto using in_app_or.
    repeat rewrite map_app in *; eauto using NoDup_slice.
    unfold boxed_option in *.
    rewrite !map_app, !map_map.
    apply flatten_app.

  - rewrite map_map in H'0.
    destruct (In_flatten_CompList P excl x0 (x0_before ++ head :: x0_after) x) as [x1 [In_x1 x1_eq] ];
      eauto.
    eapply Permutation_in with (l := head :: (x0_before ++ x0_after)).
    eapply Permutation_middle.
    simpl in *; intuition; right; eauto using Permutation_in.
    exists x1; split; eauto.
    apply H; eauto.
Qed.

Lemma UnIndexedEnsembleListEquivalence_eqv {A}
  : forall ens l,
    @UnIndexedEnsembleListEquivalence A ens l ->
    exists l',
      EnsembleListEquivalence ens l' /\ l = map indexedElement l'.
Proof.
  unfold UnIndexedEnsembleListEquivalence, EnsembleListEquivalence; intros.
  destruct_ex; intuition.
  exists x; intuition; eauto using NoDup_IndexedElement.
Qed.

Lemma For_computes_to_nil :
  forall {heading} P,
  forall ens,
    computes_to (For (QueryResultComp (heading := heading) ens
                                      (fun tup => Where (P tup) Return tup))) [] ->
    forall x,
      ens x -> ~ (P (indexedRawTuple x)).
Proof.
  unfold refine, decides, Count, Query_For, QueryResultComp; intros **.
  computes_to_inv.
  symmetry in H'; apply Permutation_nil in H'; subst.
  apply UnIndexedEnsembleListEquivalence_eqv in H; destruct_ex; intuition; subst.

  apply H2 in H0.
  apply in_split in H0.
  destruct H0 as [ x1_before [ x1_after _eq ] ]; subst.
  rewrite map_map in H'0.
  eapply (@FlattenCompList.flatten_CompList_nil _ P); unfold boxed_option; eauto; intuition.
Qed.

Lemma decidable_excl :
  forall {A : Type} (P : Ensemble A) (P_dec : DecideableEnsemble P),
    (forall (a: A), P a \/ ~ P a).
Proof.
  intros ??? a.
  destruct (dec a) eqn:eqdec;
    [ rewrite dec_decides_P in eqdec | rewrite Decides_false in eqdec ]; intuition.
Qed.

Lemma refine_constraint_check_into_QueryResultComp :
  forall heading R P' P
         (P_dec : DecideableEnsemble P),
    Same_set _ (fun tup => P (indexedElement tup)) P'
    -> refine
         (Pick (fun (b : bool) =>
                  decides b
                          (exists tup2: @IndexedRawTuple heading,
                              (R tup2 /\ P' tup2))))
         (Bind
            (Count (For (QueryResultComp R (fun tup => Where (P tup) Return tup))))
            (fun count => ret (negb (beq_nat count 0)))).
Proof.
  Local Transparent Count.
  unfold refine, Count, UnConstrQuery_In;
    intros * excl * P_iff_P' pick_comp ** .
  computes_to_inv; subst.

  computes_to_constructor.

  destruct (Datatypes.length v0) eqn:eq_length;
    destruct v0 as [ | head tail ]; simpl in *; try discriminate; simpl.

  pose proof (For_computes_to_nil _ R H).
  rewrite not_exists_forall; intro a; rewrite not_and_implication; intros.
  unfold not; intros; eapply H0; eauto; apply P_iff_P'; eauto.

  apply For_computes_to_In with (x := head) in H; try solve [intuition].
  destruct H as ( p & [ x0 ( in_ens & _eq ) ] ); subst.
  eexists; split; eauto; apply P_iff_P'; eauto.

  apply decidable_excl; assumption.
Qed.

Lemma refine_constraint_check_into_query' :
  forall {schm tbl} (c : UnConstrQueryStructure schm) P' P
         (P_dec : DecideableEnsemble P),
    Same_set _ (fun tup => P (indexedElement tup)) P'
    -> refine
         (Pick (fun (b : bool) =>
                  decides b
                          (exists tup2: @IndexedRawTuple _,
                              (GetUnConstrRelation c tbl tup2 /\ P' tup2))))
         (Bind
            (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return tup))))
            (fun count => ret (negb (beq_nat count 0)))).
Proof.
  intros; rewrite refine_constraint_check_into_QueryResultComp; eauto.
  reflexivity.
Qed.

Corollary refine_constraint_check_into_query :
  forall {schm tbl} P (c : UnConstrQueryStructure schm)
         (P_dec : DecideableEnsemble P),
    refine
      (Pick (fun (b : bool) =>
               decides b
                       (exists tup2: @IndexedRawTuple _,
                           (GetUnConstrRelation c tbl tup2 /\ P (indexedRawTuple tup2)))))
      (Bind
         (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return tup))))
         (fun count => ret (negb (beq_nat count 0)))).
Proof.
  intros.
  setoid_rewrite refine_constraint_check_into_query'; eauto.
  reflexivity.
  unfold Same_set, Included; intuition.
Qed.

Lemma refine_constraint_check_into_query'' :
  forall heading R P' P
         (P_dec : DecideableEnsemble P),
    Same_set _ (fun tup => P (indexedElement tup)) P'
    -> refine
         (Pick (fun (b : bool) =>
                  decides b
                          (exists tup2: @IndexedRawTuple heading,
                              (R tup2 /\ P' tup2))))
         (Bind
            (Count (For (QueryResultComp R (fun tup => Where (P tup) Return tup))))
            (fun count => ret (negb (beq_nat count 0)))).
Proof.
  Local Transparent Count.
  unfold refine, Count, UnConstrQuery_In;
    intros * excl * P_iff_P' pick_comp ** .
  computes_to_inv; subst.

  computes_to_constructor.

  destruct (Datatypes.length v0) eqn:eq_length;
    destruct v0 as [ | head tail ]; simpl in *; try discriminate; simpl.

  pose proof (For_computes_to_nil _ R H).
  rewrite not_exists_forall; intro a; rewrite not_and_implication; intros.
  unfold not; intros; eapply H0; eauto; apply P_iff_P'; eauto.

  apply For_computes_to_In with (x := head) in H; try solve [intuition].
  destruct H as ( p & [ x0 ( in_ens & _eq ) ] ); subst.
  eexists; split; eauto; apply P_iff_P'; eauto.

  apply decidable_excl; assumption.
Qed.

Definition refine_foreign_key_check_into_query {schm tbl} :=
  @refine_constraint_check_into_query schm tbl.

Lemma refine_functional_dependency_check_into_query :
  forall {schm : RawQueryStructureSchema}
         {tbl}
         (ref : @RawTuple (@GetNRelSchemaHeading _ (qschemaSchemas schm) tbl))
         args1
         args2
         (c : UnConstrQueryStructure schm),
    DecideableEnsemble (fun x : RawTuple => tupleAgree_computational ref x args1 /\
                                            ~ tupleAgree_computational ref x args2) ->
    ((forall tup' : IndexedRawTuple,
         GetUnConstrRelation c tbl tup'
         -> FunctionalDependency_P args2 args1 ref (indexedElement tup'))
     <-> (forall tup',
             ~ (GetUnConstrRelation c tbl tup'
                /\ tupleAgree ref (indexedElement tup') args1
                /\ ~ tupleAgree ref (indexedElement tup') args2))) ->
    refine
      (Pick (fun (b : bool) =>
               decides b
                       (forall tup',
                           GetUnConstrRelation c tbl tup' ->
                           FunctionalDependency_P args2 args1 ref (indexedElement tup'))))
      (Bind (Count
               For (UnConstrQuery_In c tbl
                                     (fun tup =>
                                        Where (tupleAgree_computational ref tup args1 /\
                                               ~ tupleAgree_computational ref tup args2)
                                              Return tup)))
            (fun count => ret (beq_nat count 0))).
Proof.
  intros * is_dec ** .

  setoid_replace (forall tup', GetUnConstrRelation c tbl tup' ->
                               tupleAgree ref (indexedElement tup') args1
                               -> tupleAgree ref (indexedElement tup') args2)
  with           (forall tup', ~ (GetUnConstrRelation c tbl tup' /\
                                  tupleAgree ref (indexedElement tup') args1 /\
                                  ~ tupleAgree ref (indexedElement tup') args2)); eauto.

  setoid_rewrite refine_decide_negation.
  setoid_rewrite (tupleAgree_equivalence ref).

  setoid_rewrite (@refine_constraint_check_into_query _ _
                                                      (fun x => tupleAgree_computational ref x args1 /\
                                                                          ~ tupleAgree_computational ref x args2)); try assumption.

  Opaque Query_For Count.
  simplify with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.

Lemma refine_functional_dependency_check_into_query' :
  forall {schm : RawQueryStructureSchema}
         {tbl}
         ref
         args1
         args2
         (c : UnConstrQueryStructure schm),
    DecideableEnsemble (fun x => tupleAgree_computational x ref args1 /\
                                         ~ tupleAgree_computational x ref args2) ->
    ((forall tup' ,
         GetUnConstrRelation c tbl tup'
         -> FunctionalDependency_P args2 args1 (indexedElement tup') ref)
     <-> (forall tup',
             ~ (GetUnConstrRelation c tbl tup'
                /\ tupleAgree (indexedElement tup') ref args1
                /\ ~ tupleAgree (indexedElement tup') ref args2))) ->
    refine
      (Pick (fun (b : bool) =>
               decides b
                       (forall tup',
                           GetUnConstrRelation c tbl tup' ->
                           FunctionalDependency_P args2 args1 (indexedElement tup') ref)))
      (Bind (Count
               For (UnConstrQuery_In c tbl
                                     (fun tup =>
                                        Where (tupleAgree_computational tup ref args1 /\
                                               ~ tupleAgree_computational tup ref args2)
                                              Return tup)))
            (fun count => ret (beq_nat count 0))).
Proof.
  intros * is_dec ** .

  setoid_replace (forall tup', GetUnConstrRelation c tbl tup' ->
                               tupleAgree (indexedElement tup') ref args1
                               -> tupleAgree (indexedElement tup') ref args2)
  with           (forall tup', ~ (GetUnConstrRelation c tbl tup' /\
                                  tupleAgree (indexedElement tup') ref args1 /\
                                  ~ tupleAgree (indexedElement tup') ref args2)); eauto.

  setoid_rewrite refine_decide_negation.
  setoid_rewrite tupleAgree_equivalence.
  setoid_rewrite (@refine_constraint_check_into_query _ _
                                                      (fun x => tupleAgree_computational x ref args1 /\
                                                                          ~ tupleAgree_computational x ref args2)); try assumption.

  Opaque Query_For Count.
  simplify with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.

 Theorem FunctionalDependency_symmetry
  : forall A H (f : _ -> _ -> Comp A) (P : _ -> Prop) attrlist1 attrlist2 n,
    refine (x1 <- {b | decides b
                               (forall tup' : @IndexedRawTuple H,
                                   P tup'
                                   -> FunctionalDependency_P attrlist1 attrlist2 n (indexedElement tup'))};
            x2 <- {b | decides b (forall tup' : @IndexedRawTuple H,
                                     P tup'
                                     -> FunctionalDependency_P attrlist1 attrlist2 (indexedElement tup') n)};
            f x1 x2)
           (x1 <- {b | decides b (forall tup' : @IndexedRawTuple H,
                                     P tup'
                                     -> FunctionalDependency_P attrlist1 attrlist2 n (indexedElement tup'))};
            f x1 x1).
Proof.
  unfold refine, FunctionalDependency_P; intros.
  computes_to_inv; firstorder.
  computes_to_inv; firstorder.
  repeat (computes_to_econstructor; eauto).
  destruct v0; simpl in *; unfold tupleAgree in *; intros; eauto.
  erewrite H0; eauto; intros; rewrite H2; eauto.
  unfold not; intros; eapply H0; intros.
  rewrite H1; eauto; intros; rewrite H3; eauto.
Qed.


Theorem FunctionalDependency_symmetry'
  : forall H P attrlist1 attrlist2 n b',
    decides b'
            (forall tup' : @IndexedRawTuple H,
                P tup'
                -> FunctionalDependency_P attrlist1 attrlist2 n (indexedElement tup'))
    -> refine {b | decides b (forall tup' : @IndexedRawTuple H,
                                 P tup'
                                 -> FunctionalDependency_P attrlist1 attrlist2 (indexedElement tup') n)}
                  (ret b').
Proof.
  unfold FunctionalDependency_P; intros.
  refine pick val b'.
  reflexivity.
  destruct b'; simpl in *; unfold tupleAgree in *; intros; eauto.
  erewrite H0; eauto; intros; rewrite H1; eauto.
  unfold not; intros; eapply H0; intros.
  rewrite H1; eauto; intros; rewrite H2; eauto.
Qed.


Lemma if_duplicate_cond_eq {A}
  : forall (i : bool) (t e : A),
    (if i then (if i then t else e) else e) = if i then t else e.
Proof.
  destruct i; reflexivity.
Qed.

Global Instance nil_List_Query_eq :
  List_Query_eq [] :=
  { As_Query_eq := tt  }.

Global Instance cons_List_Query_eq
       {A : Type}
       {As : list Type}
       {A_Query_eq : Query_eq A}
       {As_Query_eq' : List_Query_eq As}
  :
    List_Query_eq (A :: As) :=
  { As_Query_eq := (A_Query_eq, As_Query_eq) }.

Theorem UniqueAttribute_symmetry
  : forall A (f : _ -> _ -> Comp A) H (P : _ -> Prop) attr n,
    refine (b1 <- {b | decides b
                               (forall tup' : @IndexedRawTuple H,
                                   P tup'
                                   -> UniqueAttribute' attr n (indexedElement tup'))};
           b2 <- {b | decides b (forall tup' : @IndexedRawTuple H,
                                     P tup'
                                     -> UniqueAttribute' attr (indexedElement tup') n)}; f b1 b2)
           (b1 <- {b | decides b
                               (forall tup' : @IndexedRawTuple H,
                                   P tup'
                                   -> UniqueAttribute' attr n (indexedElement tup'))}; f b1 b1).
Proof.
  unfold refine, UniqueAttribute'; intros.
  computes_to_inv; firstorder.
  repeat (computes_to_econstructor; eauto).
  destruct v0; simpl in *; unfold not in *; intros; eauto.
Qed.

Lemma refine_uniqueness_check_into_query' :
  forall {schm : RawQueryStructureSchema}
         idx
         tup
         attr
         (c : UnConstrQueryStructure schm),
    Query_eq (Domain (GetNRelSchemaHeading (qschemaSchemas schm) idx) attr)
    -> refine
      {b | decides b
                   (forall tup' : @IndexedRawTuple _,
                       GetUnConstrRelation c idx tup'
                       -> UniqueAttribute' attr tup (indexedElement tup'))}
      (c <- (Count
               For (UnConstrQuery_In c idx
                                     (fun tup' =>
                                        Where (GetAttributeRaw tup attr
                                               = GetAttributeRaw tup' attr)
                                              Return tup')));
            (ret (beq_nat c 0))).
Proof.
  intros.
  setoid_replace (forall tup', GetUnConstrRelation c idx tup' ->
                               UniqueAttribute' attr tup (indexedElement tup'))
with           (forall tup', ~ (GetUnConstrRelation c idx tup' /\
                                GetAttributeRaw tup attr = GetAttributeRaw  (indexedElement tup') attr)) by
      (unfold UniqueAttribute'; intuition eauto).
  setoid_rewrite refine_decide_negation.
  rewrite (@refine_constraint_check_into_query _ _
                                                      (fun tup' => GetAttributeRaw tup attr = GetAttributeRaw tup' attr)) by eauto with typeclass_instances.
  simplify with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.
