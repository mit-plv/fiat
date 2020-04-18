Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.List.ListFacts
        Fiat.Computation
        Fiat.Computation.Refinements.Iterate_Decide_Comp
        Fiat.ADT
        Fiat.ADTRefinement Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Delete
        Fiat.QueryStructure.Specification.Operations.Mutate
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.MutateRefinements
        Fiat.Common.Ensembles.EnsembleListEquivalence.

(* Facts about implements delete operations. *)

Section DeleteRefinements.

  Hint Resolve crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesAttributeConstraints
       SatisfiesTupleConstraints.

  Arguments GetUnConstrRelation : simpl never.
  Arguments UpdateUnConstrRelation : simpl never.
  Arguments replace_BoundedIndex : simpl never.
  Arguments BuildQueryStructureConstraints : simpl never.
  Arguments BuildQueryStructureConstraints' : simpl never.

  Local Transparent QSDelete.

  Definition QSDeletedTuples
             {qsSchema}
             (qs : UnConstrQueryStructure qsSchema) Ridx
             (DeletedTuples : Ensemble RawTuple) :=
    (UnIndexedEnsembleListEquivalence
       (Intersection _
                     (GetUnConstrRelation qs Ridx)
                     (Complement _ (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)))).

  Lemma QSDeleteSpec_UnConstr_refine_AttributeConstraints :
    forall qsSchema qs  Ridx
           (DeletedTuples : Ensemble RawTuple)
           or,
      @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        {b : bool |
         (forall tup,
            GetUnConstrRelation qs Ridx tup ->
            SatisfiesAttributeConstraints Ridx (indexedElement tup)) ->
         decides b
                 (MutationPreservesAttributeConstraints
                    (EnsembleDelete (GetRelation or Ridx) DeletedTuples)
                    (SatisfiesAttributeConstraints Ridx))}
        (ret true).
  Proof.
    unfold MutationPreservesAttributeConstraints; intros * AbsR_or_qs v Comp_v.
    computes_to_econstructor; intros; computes_to_inv; subst; simpl; intros.
    unfold DropQSConstraints_AbsR in *; eapply H; inversion H0; subst;
    rewrite GetRelDropConstraints; eauto.
  Qed.

  Lemma QSDeleteSpec_UnConstr_refine_CrossConstraints' :
    forall qsSchema qs  Ridx
           (DeletedTuples : Ensemble RawTuple)
           or,
      @DropQSConstraints_AbsR qsSchema or qs ->
  refine
   {b : bool |
   (forall Ridx',
    Ridx' <> Ridx ->
    forall tup',
    GetUnConstrRelation qs Ridx tup' ->
    SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup')
      (GetUnConstrRelation qs Ridx')) ->
   decides b
     (forall Ridx',
      Ridx' <> Ridx ->
      MutationPreservesCrossConstraints
        (EnsembleDelete (GetRelation or Ridx) DeletedTuples)
        (GetUnConstrRelation qs Ridx')
        (SatisfiesCrossRelationConstraints Ridx Ridx'))}
   (ret true).
  Proof.
    unfold MutationPreservesCrossConstraints; intros * AbsR_or_qs v Comp_v.
    computes_to_econstructor; intros;  computes_to_inv; subst; simpl; intros.
    unfold DropQSConstraints_AbsR in *; eapply H; inversion H1; subst; eauto.
    rewrite GetRelDropConstraints; eauto.
  Qed.

  Lemma QSDeleteSpec_UnConstr_refine_opt :
    forall qsSchema qs Ridx DeletedTuples or,
      @DropQSConstraints_AbsR qsSchema or qs ->
      refine
        (or' <- (QSDelete or Ridx DeletedTuples);
         nr' <- {nr' | DropQSConstraints_AbsR (fst or') nr'};
         ret (nr', snd or'))
        match (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)) with
          | Some tConstr =>
            tupleConstr <- {b | (forall tup tup',
                                   elementIndex tup <> elementIndex tup'
                                   -> GetUnConstrRelation qs Ridx tup
                                     -> GetUnConstrRelation qs Ridx tup'
                                     -> tConstr (indexedElement tup) (indexedElement tup'))
                                  -> decides b (MutationPreservesTupleConstraints
                                                  (EnsembleDelete (GetRelation or Ridx) DeletedTuples)
                                                  tConstr) };
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
                                                  (EnsembleDelete (GetRelation or Ridx) DeletedTuples)
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
                             ));
              match tupleConstr, crossConstr with
                | true, true =>
                  deleted  <- Pick (QSDeletedTuples qs Ridx DeletedTuples);
                    ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
                | _, _  => ret (qs, [])
              end
          | None =>
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
                                                  (EnsembleDelete (GetRelation or Ridx) DeletedTuples)
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
              match crossConstr with
                | true  =>
                  deleted   <- Pick (QSDeletedTuples qs Ridx DeletedTuples);
                    ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples), deleted)
                | _ => ret (qs, [])
            end
        end.
  Proof.
    unfold QSDelete.
    intros; rewrite QSMutateSpec_UnConstr_refine;
    eauto using
          QSDeleteSpec_UnConstr_refine_AttributeConstraints,
    refine_SatisfiesTupleConstraintsMutate,
    refine_SatisfiesCrossConstraintsMutate,
    QSDeleteSpec_UnConstr_refine_CrossConstraints'.
    simplify with monad laws.
    unfold SatisfiesTupleConstraints.
    case_eq (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)); intros;
    [eapply refine_under_bind; intros
    | simplify with monad laws].
    simpl; unfold DropQSConstraints_AbsR, QSDeletedTuples in *; subst.
    f_equiv; unfold pointwise_relation; intros;
    repeat find_if_inside; try simplify with monad laws; try reflexivity.
    rewrite GetRelDropConstraints, get_update_unconstr_eq; f_equiv.
    f_equiv; unfold pointwise_relation; intros; eauto.
    simpl; unfold DropQSConstraints_AbsR, QSDeletedTuples in *; subst.
    repeat find_if_inside; try simplify with monad laws; try reflexivity.
    rewrite GetRelDropConstraints, get_update_unconstr_eq; f_equiv.
  Qed.

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
    - case_eq (DecideableEnsembles.dec (indexedElement x)); intros.
      + eapply dec_decides_P; eauto.
      + exfalso; apply H0; constructor; unfold In; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
    - intros H'; destruct H'; unfold In in *; eauto.
  Qed.

  Lemma DeletedTuplesIntersection {qsSchema}
  : forall qs Ridx (P : Ensemble RawTuple),
      DecideableEnsemble P
      -> refine {x | @QSDeletedTuples qsSchema qs Ridx P x}
                {x | UnIndexedEnsembleListEquivalence
                       (Intersection _ (GetUnConstrRelation qs Ridx)
                                     (fun itup => P (indexedElement itup))) x}.
  Proof.
    intros qs Ridx P P_dec v Comp_v;  computes_to_inv.
    computes_to_constructor.
    unfold QSDeletedTuples, UnIndexedEnsembleListEquivalence in *; destruct_ex;
    intuition; subst.
    eexists; intuition.
    unfold EnsembleListEquivalence in *; intuition; eauto with typeclass_instances.
    + eapply H; eapply EnsembleComplementIntersection; eauto with typeclass_instances.
    + eapply EnsembleComplementIntersection; eauto with typeclass_instances.
      eapply H; eauto.
  Qed.

  Definition UpdateUnConstrRelationDeleteC {qsSchema} (qs : UnConstrQueryStructure qsSchema) Ridx DeletedTuples :=
    ret (UpdateUnConstrRelation qs Ridx (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)).

  Lemma QSDeleteSpec_refine_subgoals ResultT :
    forall qsSchema (qs : QueryStructure qsSchema) qs' Ridx
           default success
           refined_schConstr refined_qsConstr
           (DeletedTuples : Ensemble RawTuple)
           (k : _ -> Comp ResultT),
      DropQSConstraints_AbsR qs qs'
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
                                     (EnsembleDelete (GetUnConstrRelation qs' Ridx) DeletedTuples)
                                     Constr) }
                | None => ret true
                end
                refined_schConstr
      -> refine (Iterate_Decide_Comp_opt_Pre _
                                  (fun Ridx' =>
                                      if fin_eq_dec Ridx Ridx'
                                      then None
                                      else
                                        match BuildQueryStructureConstraints qsSchema Ridx' Ridx with
                                        | Some CrossConstr =>
                                          Some
                                            (MutationPreservesCrossConstraints (GetUnConstrRelation qs' Ridx')
                                                                               (EnsembleDelete (GetUnConstrRelation qs' Ridx) DeletedTuples)
                                                                               CrossConstr)
                                        | None => None
                                        end)
                                  (@Iterate_Ensemble_BoundedIndex_filter
                                     _
                                     (fun Ridx' =>
                                        forall tup',
                                          GetUnConstrRelation qs' Ridx' tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx (indexedElement tup') (GetUnConstrRelation qs' Ridx))
                                     (fun idx =>
                                        if (fin_eq_dec Ridx idx)
                                        then false else true)
                )) refined_qsConstr
      -> (forall qs'' qs''' mutated,
             DropQSConstraints_AbsR qs'' qs'''
             -> (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qs Ridx' =
                    GetRelation qs'' Ridx')
             -> (forall t,
                    GetRelation qs'' Ridx t <-> EnsembleDelete (GetRelation qs Ridx) DeletedTuples t)
             -> QSDeletedTuples qs' Ridx DeletedTuples mutated
             -> refine (k (qs'', mutated))
                       (success qs''' mutated))
      -> refine (k (qs, [ ])) default
      -> refine
           (qs' <- QSDelete qs Ridx DeletedTuples; k qs')
           ( schConstr <- refined_schConstr;
             qsConstr <- refined_qsConstr;
             match schConstr, qsConstr with
             | true, true =>
               mutated  <- Pick (QSDeletedTuples qs' Ridx DeletedTuples);
                 qs'' <- UpdateUnConstrRelationDeleteC qs' Ridx DeletedTuples;
                 success qs'' mutated
             | _, _ => default
             end).
  Proof.
    intros.
    unfold QSDelete.
    rewrite QSMutateSpec_refine_subgoals' with (refined_schConstr_self := ret true)
                                                (refined_qsConstr' := ret true);
      try first [eassumption | reflexivity ].
    simplify with monad laws.
    repeat (f_equiv; unfold pointwise_relation; intros).
    rewrite <- H0, <- (GetRelDropConstraints qs Ridx), <- H.
    rewrite refine_SatisfiesTupleConstraintsMutate; eauto.
    destruct (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx));
    f_equiv.
    rewrite refine_SatisfiesCrossConstraintsMutate; eauto.
    rewrite <- (GetRelDropConstraints qs Ridx).
    rewrite <- H1, H; f_equiv.
    repeat find_if_inside.
    unfold QSDeletedTuples.
    f_equiv.
    rewrite <- (GetRelDropConstraints qs Ridx).
    unfold GetUnConstrRelation, UpdateUnConstrRelation.
    rewrite ilist2.ith_replace2_Index_eq, <- H; reflexivity.
    unfold UpdateUnConstrRelationDeleteC, UpdateUnConstrRelationMutateC;
    rewrite <- H, GetRelDropConstraints; reflexivity.
    reflexivity.
    reflexivity.
    eauto using QSDeleteSpec_UnConstr_refine_AttributeConstraints.
    eauto using QSDeleteSpec_UnConstr_refine_CrossConstraints'.
    intros; eapply H2; eauto.
    unfold QSDeletedTuples.
    unfold GetUnConstrRelation, UpdateUnConstrRelation in H7.
    rewrite ilist2.ith_replace2_Index_eq in H7.
    rewrite <- GetRelDropConstraints, H in H7; eauto.
  Qed.

  Local Transparent Query_For.

  Lemma DeletedTuplesFor {qsSchema}
  : forall qs Ridx P,
      DecideableEnsemble P
      -> refine {x | @QSDeletedTuples qsSchema qs Ridx P x}
                (For (UnConstrQuery_In qs Ridx
                                       (fun tup => Where (P tup) Return tup))).
  Proof.
    intros qs Ridx P P_dec v Comp_v; rewrite DeletedTuplesIntersection by auto.
    computes_to_constructor.
    unfold UnIndexedEnsembleListEquivalence.
    unfold Query_For in *.
    computes_to_inv.
    destruct Comp_v as [l [Perm_l_v Comp_v] ].
    unfold UnConstrQuery_In, QueryResultComp in *;  computes_to_inv.
    remember (GetUnConstrRelation qs Ridx); clear Heqi.
    revert P_dec i v v0 Perm_l_v Comp_v Comp_v'; clear; induction l; simpl; intros.
    - apply Return_inv in Comp_v; subst.
      eexists nil; simpl; split; eauto.
      rewrite Permutation_nil by eauto; reflexivity.
      + unfold EnsembleListEquivalence in *; intuition.
        * destruct H; intuition.
          apply Pick_inv in Perm_l_v; inversion Perm_l_v.
          unfold In in *; intuition; subst.
          apply H1 in H.
          eapply (@FlattenCompList.flatten_CompList_nil _ P x0); eauto.
          destruct x0; simpl in *; try discriminate; computes_to_econstructor.
        * constructor.
    - apply Pick_inv in Perm_l_v.
       unfold UnConstrRelation in i.
       destruct Perm_l_v as [ [ | [a' x'] ] [x_eq [equiv_u_x' NoDup_x'] ] ].
       destruct l; simpl in *; try discriminate.
       unfold In in Comp_v; pose (Bind_inv Comp_v); destruct_ex; intuition; subst; computes_to_inv; subst.
       simpl in x_eq; injections.
      case_eq (@DecideableEnsembles.dec _ P P_dec a); intros.
      + apply Pick_inv in H0; intuition.
        apply dec_decides_P in H2. apply H3 in H2.
        apply Return_inv in H2; simpl in *; subst; simpl in *.
        pose proof (PermutationConsSplit _ _ _ Comp_v'); destruct_ex; subst.
        unfold UnIndexedEnsembleListEquivalence in *.
        destruct (H (fun x => i x /\ x <> {|indexedElement := a; elementIndex := a' |}) (app x x0) v1); intuition eauto.
        apply PickComputes.
        computes_to_inv; injections.
        eexists _; intuition eauto.
        unfold In in *; intuition.
        rewrite equiv_u_x' in H2; destruct H2; subst; eauto; congruence.
        unfold In; intuition.
        apply equiv_u_x'; simpl; intuition.
        inversion NoDup_x'; subst; eauto.
        apply H7; apply in_map_iff; eexists; split; eauto; simpl; eauto.
        inversion NoDup_x'; subst; eauto.
        eapply Permutation_cons_inv; rewrite Permutation_middle; eassumption.
        * symmetry in H2; pose proof (app_map_inv _ _ _ _ H2); destruct_ex;
          intuition; subst.
          eexists (app x2 ({|indexedElement := a; elementIndex := a' |} :: x3));
            simpl; rewrite map_app.
          { simpl; intuition; computes_to_inv; injections.
            - destruct H5; unfold In in *; apply equiv_u_x' in H5; simpl in *; intuition.
              apply in_or_app; simpl; eauto.
              assert (i x) as u_x by (apply equiv_u_x'; eauto).
              assert (List.In x (x2 ++ x3)) as In_x by
                    (apply H0; constructor; unfold In; intuition; subst;
                inversion NoDup_x'; subst; eapply H10; apply in_map_iff; eexists;
                split; cbv beta; simpl; eauto; reflexivity).
              apply in_or_app; simpl; apply in_app_or in In_x; intuition.
            - unfold In.
              assert (List.In x (x2 ++ x3) \/ x = {|indexedElement := a; elementIndex := a' |})
                as In_x0
                  by (apply in_app_or in H5; simpl in H5; intuition).
              intuition.
              + apply H0 in H7; destruct H7; unfold In in *; intuition.
                constructor; eauto.
              + subst; constructor; eauto.
                apply equiv_u_x'; simpl; eauto.
                case_eq (@DecideableEnsembles.dec _ P P_dec a); intros.
                apply dec_decides_P; eauto.
                assert (~ P a) as H''
                    by (unfold not; intros H'; apply dec_decides_P in H'; congruence);
                apply H4 in H''; discriminate.
            - rewrite map_app; apply NoDup_app_swap; simpl; constructor; eauto.
              inversion NoDup_x'; subst; unfold not; intros; apply H8.
              rewrite <- map_app in H5; apply in_map_iff in H5; destruct_ex; intuition.
              assert (List.In x (x2 ++ x3)) as In_a by
                    (apply in_or_app; apply in_app_or in H10; intuition).
              apply H0 in In_a; destruct In_a; unfold In in *; intuition.
              apply equiv_u_x' in H12; simpl in *; intuition.
              destruct x; simpl in *; subst.
              apply in_map_iff; eexists; split; eauto; simpl; eauto.
              apply NoDup_app_swap; rewrite <- map_app; eauto.
          }
      + unfold Query_Where, Query_Return in H0;
        computes_to_inv; intuition.
        assert (~ P a) as H''
            by (unfold not; intros H'; apply dec_decides_P in H'; congruence
        ).
        apply H4 in H''; subst; simpl in *; subst.
        destruct (H (fun x => i x /\ x <> {|indexedElement := a; elementIndex := a' |}) v v1); intuition eauto.
        * computes_to_econstructor.
          eexists; intuition; eauto.
          unfold In in *; intuition.
          apply equiv_u_x' in H5; destruct H5; subst; eauto.
          congruence.
          unfold In; intuition.
          unfold In; intuition.
          subst.
          apply equiv_u_x'; simpl; intuition.
          inversion NoDup_x'; subst; eauto.
          apply H8; apply in_map_iff; eexists; split; eauto; simpl; eauto.
          inversion NoDup_x'; subst; eauto.
        * unfold In.
          eexists; split; eauto.
          unfold UnIndexedEnsembleListEquivalence in *; intuition.
          destruct H6; intuition.
          eapply H0; constructor; unfold In in *; subst; intuition.
          subst; apply_in_hyp dec_decides_P; simpl in *; congruence.
          constructor;
            apply H0 in H6; destruct H6; unfold In in *; intuition.
  Qed.

End DeleteRefinements.
