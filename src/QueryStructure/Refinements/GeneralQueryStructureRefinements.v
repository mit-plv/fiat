Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        ADTSynthesis.Computation ADTSynthesis.ADT ADTSynthesis.ADTRefinement ADTSynthesis.ADTNotation ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.QueryStructureSchema ADTSynthesis.QueryStructure.QueryStructure
        ADTSynthesis.QueryStructure.IndexedEnsembles
        ADTSynthesis.QueryStructure.QuerySpecs.QueryQSSpecs ADTSynthesis.QueryStructure.QuerySpecs.InsertQSSpecs ADTSynthesis.QueryStructure.QuerySpecs.EmptyQSSpecs ADTSynthesis.QueryStructure.QuerySpecs.DeleteQSSpecs
        ADTSynthesis.QueryStructure.QueryStructureNotations
        ADTSynthesis.QueryStructure.Refinements.GeneralQueryRefinements ADTSynthesis.QueryStructure.Refinements.GeneralInsertRefinements ADTSynthesis.QueryStructure.Refinements.GeneralDeleteRefinements.

Ltac subst_strings :=
  repeat match goal with
           | [ H : string |- _ ] => subst H
         end.

Ltac pose_string_ids :=
  subst_strings;
  repeat match goal with
           | |- context [String ?R ?R'] =>
             let str := fresh "StringId" in
             set (String R R') as str in *
         end.

Lemma Constructor_DropQSConstraints {MySchema} {Dom}
: forall oldConstructor (d : Dom),
    refine
      (or' <- oldConstructor d;
       {nr' |
          DropQSConstraints_AbsR (qsSchema := MySchema) or' nr'})
        (or' <- oldConstructor d;
         ret (DropQSConstraints or')).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  repeat econstructor; eauto.
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
  (A := list (IndexedTuple)) (a := [])
    by (repeat econstructor; eauto).
  simplify with monad laws.
  rewrite refine_pick_val with
  (A := list ResultT) (a := []); reflexivity.
Qed.

Lemma Ensemble_List_Equivalence_Insert {A}
: forall (a : A) (Ens : Ensemble A),
    ~ In _ Ens a ->
    refine {l |
            EnsembleListEquivalence (EnsembleInsert a Ens) l}
           (l <- { l |
                   EnsembleListEquivalence Ens l};
            ret (a :: l) ).
Proof.
  unfold EnsembleListEquivalence, refine, In,
  EnsembleInsert; intros.
  inversion_by computes_to_inv; subst; econstructor.
  simpl; intuition.
  econstructor; eauto.
  intuition; eapply H; eapply H3; eauto.
  right; eapply H3; eauto.
  right; eapply H3; eauto.
Qed.

Lemma refine_For_In_Insert
: forall ResultT MySchema R or a tup bod,
    ~ In _ (GetUnConstrRelation or R)
      {| elementIndex := a;
         indexedElement := tup |}
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
  rewrite Ensemble_List_Equivalence_Insert by eauto.
  setoid_rewrite refineEquiv_bind_bind.
  setoid_rewrite refineEquiv_bind_unit; simpl.
  simplify with monad laws.
  Transparent Query_For.
  unfold Query_For.
  repeat setoid_rewrite refineEquiv_bind_bind; simpl.
  unfold refine; intros; inversion_by computes_to_inv.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor.
  rewrite Permutation.Permutation_app_head; eauto.
Qed.

Ltac start_honing_QueryStructure :=
  pose_string_ids;
  match goal with
      |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
      hone representation using (@DropQSConstraints_AbsR Rep);
        match goal with
            |- context [Build_consDef (@Build_consSig ?Id _)
                                      (@absConstructor _ _ _ _ _)] =>
            hone constructor Id;
              [ etransitivity;
                [apply Constructor_DropQSConstraints |
                 simplify with monad laws; finish honing]
              | ]
        end; pose_string_ids;
        repeat (match goal with
                  | |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (absMethod _ (fun _ _ => Insert _ into _))] =>
                    drop constraints from insert Id
                  | |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (absMethod _ (fun _ _ => Delete _ from _ where _))] =>
                    drop constraints from delete Id
                  | |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (@absMethod _ _ _ _ _ _)] =>
                    drop constraints from query Id
                end; pose_string_ids)
  end.

Lemma refine_trivial_if_then_else :
  forall x,
    refine
      (If_Then_Else x (ret true) (ret false))
      (ret x).
Proof.
  destruct x; reflexivity.
Qed.

Tactic Notation "start" "honing" "QueryStructure" := start_honing_QueryStructure.
