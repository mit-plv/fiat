Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        QueryStructure GeneralInsertRefinements
        GeneralQueryRefinements SetEq AdditionalLemmas.

Definition EnsembleIndexedListEquivalence {heading}
           (R : Ensemble (@IndexedTuple heading))
           (l : list (@Tuple heading)) :=
  (forall tup, In _ R tup ->
               lt (tupleIndex tup)  (length l))
  /\ UnIndexedEnsembleListEquivalence R l.

Instance EnsembleListEquivalence_AbsR {heading}:
  @UnConstrRelationAbsRClass (@IndexedTuple heading)
                             (list (@Tuple heading)) :=
  {| UnConstrRelationAbsR := @EnsembleIndexedListEquivalence heading|}.


Lemma EnsembleIndexedListEquivalence_lift_property {heading} {P: @Tuple heading -> Prop} :
  forall (sequence: list (@Tuple heading)) (ensemble: @IndexedTuple heading -> Prop),
    EnsembleIndexedListEquivalence ensemble sequence ->
    ((forall item,
        List.In item sequence -> P item) <->
     (forall item,
        Ensembles.In _ ensemble item -> P (indexedTuple item))).
Proof.
  intros * equiv;
  destruct equiv as [_ [ l' (is_map & _ & equiv) ] ];
  subst.
  setoid_rewrite equiv.
  setoid_rewrite in_map_iff.
  split; intros; firstorder; subst; intuition. 
Qed.

  Lemma EnsembleListEquivalence_Empty :
    forall qsSchema Ridx,
      EnsembleListEquivalence
        (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qsSchema))
                             Ridx) [].
  Proof.
    intros; rewrite GetRelDropConstraints; simpl; split; simpl; intros;
    unfold GetRelation, In in *.
    + econstructor.
    + rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
  Qed.

  Lemma EnsembleIndexedListEquivalence_Empty :
    forall qsSchema Ridx,
      EnsembleIndexedListEquivalence
        (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qsSchema))
                             Ridx) [].
  Proof.
    intros; rewrite GetRelDropConstraints; simpl; split; simpl; intros;
    unfold GetRelation, In in *.
    + rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
    + eexists []; intuition; econstructor.
      - econstructor.
      - unfold In; split; intros.
        * rewrite Build_EmptyRelation_IsEmpty in *; simpl in *; intuition.
        * intuition.
  Qed.

Ltac implement_empty_list constrName RepAbsR :=
  hone constructor constrName;
  [ unfold RepAbsR, DropQSConstraints_AbsR;
    repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
    repeat setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws;
    repeat rewrite refineEquiv_pick_pair;
    repeat (rewrite refine_pick_val;
            [simplify with monad laws
            | apply EnsembleIndexedListEquivalence_Empty]);
        subst_body; higher_order_1_reflexivity
  | ].

(*Tactic Notation "implement" "using" "lists" "under" constr(Rep_AbsR) :=
    let AbsR_Hyp := fresh in
    pose Rep_AbsR as AbsR_Hyp;
      unfold Rep_AbsR in AbsR_Hyp;
      hone representation using AbsR_Hyp;
      repeat match goal with
                 |- context[
                        (const ?R ( _ : _ ) : rep :=
                           { _ | exists _, _ })%consDef] =>
                 implement_empty_list R AbsR_Hyp
             end;
      repeat
        match goal with
            |- context [ (meth ?R ( _ : rep , _ : _ ) : _ :=
                            {nr' | forall or , _ } )%methDef] =>
            first [ implement insert in R with lists under AbsR_Hyp
                  | implement query in R with lists under AbsR_Hyp ]
        end.
*)
