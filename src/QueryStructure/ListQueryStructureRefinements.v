Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        QueryStructure GeneralInsertRefinements
        GeneralQueryRefinements SetEq AdditionalLemmas
        ListInsertRefinements ListQueryRefinements.

Instance EnsembleListEquivalence_SiR {A}:
  @UnConstrRelationSiRClass A (list A) :=
  {| UnConstrRelationSiR := @EnsembleListEquivalence A |}.

  Lemma EnsembleListEquivalence_Empty :
    forall qsSchema Ridx,
      EnsembleListEquivalence
        (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qsSchema))
                             Ridx) [].
  Proof.
    intros; rewrite GetRelDropConstraints; simpl; split; simpl; intros;
    unfold GetRelation, In in *;
    rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; auto.
  Qed.

Ltac implement_empty_list constrName RepSiR :=
  hone constructor constrName;
  [ unfold RepSiR, DropQSConstraints_SiR;
    repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
    repeat setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws;
    repeat rewrite refineEquiv_pick_pair;
    repeat (rewrite refine_pick_val;
            [simplify with monad laws
            | apply EnsembleListEquivalence_Empty]);
        subst_body; higher_order_1_reflexivity
  | ].

Tactic Notation "implement" "using" "lists" "under" constr(Rep_SiR) :=
    let SiR_Hyp := fresh in
    pose Rep_SiR as SiR_Hyp;
      unfold Rep_SiR in SiR_Hyp;
      hone representation using SiR_Hyp;
      repeat match goal with
                 |- context[
                        (const ?R ( _ : _ ) : rep :=
                           { _ | exists _, _ })%consDef] =>
                 implement_empty_list R SiR_Hyp
             end;
      repeat
        match goal with
            |- context [ (meth ?R ( _ : rep , _ : _ ) : _ :=
                            {nr' | forall or , _ } )%methDef] =>
            first [ implement insert in R with lists under SiR_Hyp
                  | implement query in R with lists under SiR_Hyp ]
        end.
