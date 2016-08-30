Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Insert
        Fiat.QueryStructure.Specification.Operations.Empty
        Fiat.QueryStructure.Specification.Operations.Delete
        Fiat.QueryStructure.Specification.Operations.Update
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.InsertRefinements
        Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements
        Fiat.QueryStructure.Implementation.Operations.General.QueryStructureRefinements
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.General.QueryAutomation
        Fiat.QueryStructure.Automation.General.InsertAutomation
        Fiat.QueryStructure.Automation.General.DeleteAutomation.

Ltac start_honing_QueryStructure' :=
    eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl;
                              match goal with
                                | |- context [QSInsert _ _ _] => drop_constraints_from_insert
                                | |- context [QSDelete _ _ _] => drop_constraints_from_delete
                                | |- context [Query_For _] => drop_constraints_from_query
                                | |- _ => idtac
                              end | ]
                          ])]
    end | ].

Ltac start_honing_QueryStructure :=
  match goal with
      |- ?R ?QSSpec =>
      cbv delta [QSSpec
                   QSGetNRelSchemaHeading GetNRelSchema
                   GetNRelSchemaHeading Domain Specif.value
                   ] beta; simpl;
      (*pose_string_hyps; pose_heading_hyps;*)
      match R with
        | ?MostlySharpened =>
          eapply MostlySharpened_Start; start_honing_QueryStructure'
        | ?FullySharpened =>
          eapply FullySharpened_Start; [start_honing_QueryStructure' | ]
      end
  end; pose_string_hyps; pose_heading_hyps.

Tactic Notation "start" "honing" "QueryStructure" := start_honing_QueryStructure.

Ltac implement_DropQSConstraints_AbsR :=
  simpl; intros;
  try simplify with monad laws; cbv beta; simpl;
  simpl; refine pick val _; [ | eassumption].

Ltac drop_constraints_from_query' :=
  match goal with
    [ H : DropQSConstraints_AbsR ?r_o ?r_n
      |- context [Query_In ?r_o _ _] ] =>
    setoid_rewrite (DropQSConstraintsQuery_In r_o);
      rewrite !H
  end.

Ltac drop_constraints :=
  first
    [ simplify with monad laws
    | drop_constraints_from_query'
    | setoid_rewrite refine_If_Then_Else_Bind; simpl
    | setoid_rewrite refine_If_Opt_Then_Else_Bind; simpl
    | setoid_rewrite refine_if_Then_Else_Duplicate
    | implement_DropQSConstraints_AbsR].

Ltac drop_constraints_drill :=
  subst_refine_evar;
  first
    [ try set_refine_evar; implement_QSInsertSpec
    | try set_refine_evar; implement_QSDeleteSpec
    | eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else;
      [intro; set_refine_evar | set_refine_evar ] ].


Ltac start_honing_QueryStructure'' :=
    eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl;
                              doAny ltac:(drop_constraints)
                                           drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing)
                            | ]
          ])]
    end | ].

Ltac subst_FiniteTables_AbsR :=
  match goal with
  | [ H : FiniteTables_AbsR ?r_o ?r_n
      |- context [?r_o] ]=> rewrite (proj1 H)
  | [ H : FiniteTables_AbsR ?r_o ?r_n
    |- context [GetUnConstrRelation ?r_o ?Ridx] ]=>
  rewrite (@GetRel_FiniteTableAbsR _ r_o r_n Ridx H)
end.

Ltac Finite_FiniteTables_AbsR :=
  match goal with
  | [ H : FiniteTables_AbsR ?r_o ?r_n
      |- context [FiniteEnsemble (GetUnConstrRelation ?r_o ?Ridx)] ]=>
    eapply (@FiniteTable_FiniteTableAbsR _ r_o r_n Ridx H)
  | [ H : FiniteTables_AbsR ?r_o ?r_n
      |- context [FiniteEnsemble (GetUnConstrRelation ?r_n ?Ridx)] ]=>
    eapply (@FiniteTable_FiniteTableAbsR' _ r_o r_n Ridx H)
  | _ => eapply FiniteEnsemble_Intersection; eauto with typeclass_instances
  end.

Lemma FiniteTables_AbsR_Insert'
      {qs_schema : RawQueryStructureSchema}
  : forall (r_o r_n r_n' : UnConstrQueryStructure qs_schema)
           (idx : Fin.t (numRawQSschemaSchemas qs_schema))
           (tup : IndexedElement),
    computes_to (UpdateUnConstrRelationInsertC r_n idx tup) r_n'
    -> UnConstrFreshIdx (GetUnConstrRelation r_n idx) (elementIndex tup)
    -> FiniteTables_AbsR r_o r_n
    -> FiniteTables_AbsR r_n' r_n'.
Proof.
  unfold UpdateUnConstrRelationInsertC; intros; computes_to_inv; subst.
  unfold FiniteTables_AbsR; intuition.
  destruct (fin_eq_dec idx idx0); subst.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation.
    rewrite ilist2.ith_replace2_Index_eq.
    unfold FiniteTables_AbsR in H1; intuition subst.
    destruct (H2 idx0) as [l ?]; eexists (cons (indexedElement tup) l).
    eauto using UnIndexedEnsembleListEquivalence_Insert.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation.
    rewrite ilist2.ith_replace2_Index_neq; eauto.
    unfold FiniteTables_AbsR in H1; intuition subst.
    eapply H2.
Qed.

Lemma FiniteTables_AbsR_Delete'
      {qs_schema : RawQueryStructureSchema}
  : forall (r_o r_n r_n' : UnConstrQueryStructure qs_schema)
           (idx : Fin.t (numRawQSschemaSchemas qs_schema))
           (P : Ensemble RawTuple)
           (P_dec : DecideableEnsemble P),
    computes_to (UpdateUnConstrRelationDeleteC r_n idx P) r_n'
    -> FiniteTables_AbsR r_o r_n
    -> FiniteTables_AbsR r_n' r_n'.
Proof.
  unfold UpdateUnConstrRelationDeleteC; intros; computes_to_inv; subst.
  unfold FiniteTables_AbsR; intuition.
  destruct (fin_eq_dec idx idx0); subst.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation.
    rewrite ilist2.ith_replace2_Index_eq.
    unfold FiniteTables_AbsR in H0; intuition subst.
    destruct (H1 idx0) as [l ?]; eexists _.
    eapply UnIndexedEnsembleListEquivalence_Delete; eauto.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation.
    rewrite ilist2.ith_replace2_Index_neq.
    unfold FiniteTables_AbsR in H0; intuition subst.
    destruct (H1 idx0) as [l ?]; eexists _; eauto.
    congruence.
Qed.

Ltac implement_FiniteTables_AbsR :=
  simpl; intros;
  try simplify with monad laws; cbv beta; simpl;
  simpl; refine pick val _;
  [
  | solve
      [ repeat first
               [solve [eauto using FiniteTables_AbsR_symmetry]
               | match goal with
                   H : computes_to (UpdateUnConstrRelationInsertC ?r_n ?idx ?tup) ?r_n'
                   |- FiniteTables_AbsR ?r_n' _ =>
                   eapply (FiniteTables_AbsR_Insert' H); try eassumption
                 end
               | match goal with
                   H : computes_to (UpdateUnConstrRelationDeleteC ?r_n ?idx ?P) ?r_n'
                   |- FiniteTables_AbsR ?r_n' _ =>
                   eapply (FiniteTables_AbsR_Delete' _ H); try eassumption
                 end
  ] ] ].


Ltac doAny' srewrite_fn drills_fn finish_fn :=
  let repeat_srewrite_fn := repeat srewrite_fn in
  try repeat_srewrite_fn;
    try apply_under_subgoal drills_fn ltac:(repeat_srewrite_fn);
    finish_fn.

Ltac simplify_queries :=
  first [
      simplify with monad laws
    | progress unfold UnConstrQuery_In
    | setoid_rewrite refine_If_Then_Else_Bind; simpl
    | setoid_rewrite refine_If_Opt_Then_Else_Bind; simpl
    | rewrite refine_QueryResultComp_Intersection_Intersection
    | rewrite refine_IndexedEnsemble_Intersection_Intersection
    | rewrite (@refine_Where_Intersection' _ _ _); repeat decide equality
    | rewrite (@refine_Where_Intersection _ _ _ _ _ _)
    | Finite_FiniteTables_AbsR
    | subst_FiniteTables_AbsR
    | implement_FiniteTables_AbsR
    ].
