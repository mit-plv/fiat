Require Export Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List
        Coq.Arith.Compare_dec
        Coq.Bool.Bool
        Coq.Strings.String
        Coq.Strings.Ascii
        Fiat.Common.BoolFacts
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.List.ListFacts
        Fiat.Common.LogicFacts
        Fiat.Common.DecideableEnsembles
        Fiat.QueryStructure.Specification.Constraints.tupleAgree
        Fiat.QueryStructure.Specification.Operations.Mutate
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.QueryStructure.Automation.Common.

Ltac dec_tauto :=
  clear; intuition eauto;
  eapply Tuple_Agree_eq_dec;
  match goal with
  | [ |- ?E = true ] => case_eq E; intuition idtac; [ exfalso ]
  end;
  match goal with
  | [ H : _ |- _ ] => apply Tuple_Agree_eq_dec' in H; solve [ eauto ]
  end.

Lemma query_eq_true_iff {A}
      (q_eq : Query_eq A)
  : forall (a a' : A), ?[ A_eq_dec a a'] = true <-> a = a'.
Proof.
  intros; destruct (A_eq_dec a a'); split; intros; try congruence.
Qed.

Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  (*repeat setoid_rewrite <- (@query_eq_true_iff _ _); *)
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- eq_N_dec_bool_true_iff;
  try setoid_rewrite <- eq_Z_dec_bool_true_iff;
  try setoid_rewrite <- string_dec_bool_true_iff;
  try setoid_rewrite <- ascii_dec_bool_true_iff;
  setoid_rewrite and_True;
  repeat progress (
           try setoid_rewrite <- andb_true_iff;
           try setoid_rewrite not_true_iff_false;
           try setoid_rewrite <- negb_true_iff);
  rewrite bool_equiv_true;
  reflexivity.

Hint Extern 100 (DecideableEnsemble _) => prove_decidability_for_functional_dependencies : typeclass_instances.

Tactic Notation "refine" "existence" "check" "into" "query" :=
  match goal with
    |- context[{b | decides b
                            (exists tup : @IndexedTuple ?heading,
                                (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
    =>
    let H1 := fresh in
    let H2 := fresh in
    makeEvar (Ensemble (@Tuple heading))
             ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                   [unfold Same_set, Included, Ensembles.In;
                     split; [intros x H; pattern (indexedElement x);
                             match goal with
                               |- ?P'' (indexedElement x) => unify P' P'';
                                 simpl; eauto
                             end
                            | eauto]
                   |
                   assert (DecideableEnsemble P') as H2;
                     [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                     | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.

Ltac funDepToQuery :=
  match goal with
  | |-
    context [{b : _ |
              decides b
                      (forall tup' : @IndexedElement ?T,
                          GetUnConstrRelation (QSSchema := ?qsSchema) ?or ?Ridx _ ->
                          @FunctionalDependency_P ?heading ?attrlist1 ?attrlist2 ?n _)}] =>
    let H' := fresh in
    let H'' := fresh in
    let refine_fundep := fresh in
    assert
      ((forall (tup' : @IndexedElement T),
           GetUnConstrRelation or Ridx tup' ->
           @FunctionalDependency_P heading attrlist1 attrlist2 n (indexedElement tup')) <->
       (forall tup' : @IndexedElement T,
           ~
             (GetUnConstrRelation or Ridx tup' /\
              @tupleAgree heading n (indexedElement tup') attrlist2 /\
              ~ @tupleAgree heading n (indexedElement tup') attrlist1)))
      as H' by (unfold FunctionalDependency_P; dec_tauto);
      assert
        (DecideableEnsemble
           (fun x : T =>
              @tupleAgree_computational heading n x attrlist2 /\
              ~ @tupleAgree_computational heading n x attrlist1))
      as H''
        by (subst_all;
            FunctionalDependencyAutomation.prove_decidability_for_functional_dependencies);
      (let refine_fundep :=
           eval simpl in
       ( (@refine_functional_dependency_check_into_query qsSchema Ridx n attrlist2
                                                         attrlist1 or H'' H')) in
           setoid_rewrite refine_fundep; clear H'' H')
  end.

Ltac fundepToQuery :=
  match goal with
  | [ |- context[Pick
                   (fun b => decides
                               b
                               (forall tup' : @IndexedRawTuple ?sch,
                                   GetUnConstrRelation (QSSchema := ?qs_schema) ?or ?Ridx _
                                   -> @FunctionalDependency_P ?heading ?attrlist1 ?attrlist2 ?n _))] ] =>
    let H' := fresh in
    let H'' := fresh in
    let refine_fundep := fresh in
    assert ((forall tup' : IndexedRawTuple,
                GetUnConstrRelation or Ridx tup'
                -> @FunctionalDependency_P heading attrlist1 attrlist2 n (indexedElement tup'))
            <-> (forall tup' : IndexedRawTuple,
                    ~ (GetUnConstrRelation or Ridx tup'
                       /\ @tupleAgree sch n (indexedElement tup') attrlist2
                       /\ ~ @tupleAgree sch n (indexedElement tup') attrlist1))) as H'
        by (unfold FunctionalDependency_P; dec_tauto);
      assert (DecideableEnsemble (fun x : RawTuple =>
                                    @tupleAgree_computational sch n x attrlist2 /\
                                    ~ @tupleAgree_computational sch n x attrlist1)) as H''
        by (subst_all;
            prove_decidability_for_functional_dependencies);
      let refine_fundep := eval simpl in (@refine_functional_dependency_check_into_query qs_schema Ridx n attrlist2 attrlist1 or H'' H') in
          (* as refine_fundep; simpl in refine_fundep;
        fold_heading_hyps_in refine_fundep; fold_string_hyps_in refine_fundep; *)
          setoid_rewrite refine_fundep; clear H'' H'
  | [ |- context[Pick
                   (fun b => decides
                               b
                               (forall tup' : @IndexedRawTuple ?sch,
                                   GetUnConstrRelation ?or ?Ridx _
                                   -> @FunctionalDependency_P ?heading ?attrlist1 ?attrlist2 _ ?n ))] ] =>
    let H' := fresh in
    let H'' := fresh in
    let refine_fundep := fresh in
    assert ((forall tup' : IndexedTuple,
                GetUnConstrRelation or Ridx tup'
                -> @FunctionalDependency_P heading attrlist1 attrlist2 (indexedElement tup') n)
            <-> (forall tup' : IndexedTuple,
                    ~ (GetUnConstrRelation or Ridx tup'
                       /\ @tupleAgree sch (indexedElement tup') n attrlist2
                       /\ ~ @tupleAgree sch (indexedElement tup') n attrlist1))) as H'
        by (unfold FunctionalDependency_P; dec_tauto);
      assert (DecideableEnsemble (fun x : Tuple =>
                                    @tupleAgree_computational sch x n attrlist2 /\
                                    ~ @tupleAgree_computational sch x n attrlist1)) as H''
        by prove_decidability_for_functional_dependencies;
      let refine_fundep := eval simpl in
      (@refine_functional_dependency_check_into_query' _ _ n attrlist2 attrlist1 or H'' H') in
          (*simpl in refine_fundep; setoid_rewrite refine_fundep; *) clear H'' H'
  end; try simplify with monad laws; pose_string_hyps; pose_heading_hyps.
