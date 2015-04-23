Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        Fiat.Computation Fiat.ADT Fiat.ADTRefinement Fiat.ADTNotation Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Operations.Query Fiat.QueryStructure.Specification.Operations.Insert Fiat.QueryStructure.Specification.Operations.Empty Fiat.QueryStructure.Specification.Operations.Delete Fiat.QueryStructure.Specification.Operations.Update
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements Fiat.QueryStructure.Implementation.Operations.General.InsertRefinements Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements. (* Add Update *)

Lemma Constructor_DropQSConstraints {MySchema} {Dom}
: forall oldConstructor (d : Dom),
    refine
      (or' <- oldConstructor d;
       {nr' |
          DropQSConstraints_AbsR (qsSchema := MySchema) or' nr'})
        (or' <- oldConstructor d;
         ret (DropQSConstraints or')).
Proof.
  unfold refine; intros; computes_to_inv.
  repeat computes_to_econstructor; eauto.
Qed.

(* Queries over an empty relation return empty lists. *)
Lemma refine_For_In_Empty  :
  forall ResultT MySchema R bod,
    refine (Query_For (@UnConstrQuery_In ResultT MySchema
                                   (DropQSConstraints (QSEmptySpec MySchema))
                                   R bod))
           (ret []).
Proof.
  intros; rewrite refine_For.
  simplify with monad laws.
  unfold In, DropQSConstraints, GetUnConstrRelation in *.
  rewrite <- ith_Bounded_imap.
  unfold QSEmptySpec; simpl rels.
  rewrite Build_EmptyRelation_IsEmpty; simpl.
  rewrite refine_pick_val with
  (A := list Tuple) (a := []).
  - simplify with monad laws.
    rewrite refine_pick_val with
    (A := list ResultT) (a := []); reflexivity.
  - eexists []; simpl; intuition econstructor.
Qed.

Lemma Ensemble_List_Equivalence_Insert {A}
: forall (a : @IndexedElement A) (Ens : @IndexedEnsemble A),
    ~ In _ (fun idx => exists a', In _ Ens a' /\ elementIndex a' = elementIndex a) a ->
    refine {l |
            UnIndexedEnsembleListEquivalence (EnsembleInsert a Ens) l}
           (l <- { l |
                   UnIndexedEnsembleListEquivalence Ens l};
            ret ((indexedElement a) :: l) ).
Proof.
  unfold UnIndexedEnsembleListEquivalence, refine, In,
  EnsembleInsert; intros.
   computes_to_inv; subst; computes_to_econstructor.
   destruct_ex; simpl; intuition.
  exists (a :: x).
  intuition; subst; simpl; eauto.
  right; eapply H0; eauto.
  simpl in *; intuition.
  right; eapply H0; eauto.
  econstructor; eauto.
  unfold not; intros.
  rewrite in_map_iff in H1; destruct_ex; intuition.
  apply H0 in H4.
  eapply H; eexists; eauto.
Qed.

Lemma refine_For_In_Insert
: forall ResultT MySchema R or a tup bod,
    (forall tup, GetUnConstrRelation or R tup -> tupleIndex tup <> a)
    -> refine (Query_For
                 (@UnConstrQuery_In
                    ResultT MySchema
                    (UpdateUnConstrRelation
                       or R
                       (EnsembleInsert {| elementIndex := a;
                                          indexedElement := tup |}
                                       (GetUnConstrRelation or R)))
                    R bod))
              (newResults <- bod tup;
               origResults <- (Query_For
                                 (@UnConstrQuery_In
                                    ResultT MySchema or R bod));
               {l | Permutation.Permutation (newResults ++ origResults) l}).
Proof.
  intros; rewrite refine_For.
  unfold UnConstrQuery_In,
  GetUnConstrRelation at 1, UpdateUnConstrRelation.
  rewrite ith_replace_BoundIndex_eq.
  unfold QueryResultComp; simplify with monad laws.
  rewrite Ensemble_List_Equivalence_Insert.
  - setoid_rewrite refineEquiv_bind_bind.
    setoid_rewrite refineEquiv_bind_unit; simpl.
    simplify with monad laws.
    Transparent Query_For.
    unfold Query_For.
    repeat setoid_rewrite refineEquiv_bind_bind; simpl.
    unfold refine; intros;  computes_to_inv.
    repeat computes_to_econstructor; eauto.
    rewrite Permutation.Permutation_app_head; eauto.
  - simpl; unfold In, not; intros; destruct_ex; intuition.
    eapply H; eauto.
Qed.

  Lemma get_update_unconstr_iff {db_schema qs table new_contents} :
    forall x,
      Ensembles.In _ (GetUnConstrRelation (@UpdateUnConstrRelation db_schema qs table new_contents) table) x <->
      Ensembles.In _ new_contents x.
  Proof.
    unfold GetUnConstrRelation, UpdateUnConstrRelation, EnsembleInsert.
    intros. rewrite ith_replace_BoundIndex_eq;
            reflexivity.
  Qed.
