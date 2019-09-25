Require Import
        Coq.Lists.List
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.ilist2
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.List.ListFacts
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
Import ListNotations.

        
Lemma change_refine_form {X1 X2 Y Z} :
  forall (cx: Comp (X1 * X2)) (cy: X1 * X2 -> Comp Y) (f: Y -> Comp Z),
    refine
      (x <- cx;
       y <- cy x;
       f y)
      (x0 <- (x <- cx;
              y <- cy x;
              ret (y, snd x));
       f (fst x0)).
Proof.
  intros.
  unfold refine; intros.
  computes_to_inv; subst.
  eauto.
Qed.


Definition UnIndexedEnsembleListEquivalence'
           (ElementType : Type)
           (ensemble : IndexedEnsemble)
           (l : list ElementType) :=
  sig (fun (l': list IndexedElement) =>
         map indexedElement l' = l /\
         (forall x : IndexedElement,
            In IndexedElement ensemble x <-> List.In x l') /\
         NoDup (map elementIndex l')).

Definition AllFinite {qs_schema} (r: UnConstrQueryStructure qs_schema) :=
  forall idx, {l: list RawTuple & UnIndexedEnsembleListEquivalence' (GetUnConstrRelation r idx) l}.

Definition FiniteTables_AbsR'
    {qs_schema}
    (r_o : UnConstrQueryStructure qs_schema)
    (r_n : { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n }) :=
  r_o = projT1 r_n.

Lemma QSEmptyIsFinite {qs_schema}: AllFinite (DropQSConstraints (QSEmptySpec qs_schema)).
Proof.
  unfold AllFinite. intros. exists []. exists [].
  split.
  - reflexivity.
  - split.
    * split; intros.
      + cbn in H. red in H. red in H.
        change (Vector.map schemaRaw (QSschemaSchemas qs_schema))
          with (qschemaSchemas qs_schema) in H. rewrite <- ith_imap2 in H.
        remember (ith2 _ _) in *.
        change (numQSschemaSchemas qs_schema)
          with (numRawQSschemaSchemas (QueryStructureSchemaRaw qs_schema)) in Heqy.
        change (fun x => ?f x) with f in Heqy.

        rewrite (Build_EmptyRelation_IsEmpty qs_schema idx) in Heqy.
        subst y. cbn in H. inversion H.
      + inversion H.
    * constructor.
Qed.

Lemma FiniteTables_AbsR'_QSEmptySpec
      {qs_schema}
  :  FiniteTables_AbsR'
       (DropQSConstraints (QSEmptySpec qs_schema))
       (existT AllFinite (DropQSConstraints (QSEmptySpec qs_schema)) QSEmptyIsFinite).
Proof. reflexivity. Qed.

Definition IncrMaxFreshIdx {qs_schema idx} (r: sigT (@AllFinite qs_schema)) :=
  S (fold_right (fun elem acc => max (elementIndex elem) acc) 0 (proj1_sig (projT2 ((projT2 r) idx)))).

Lemma IncrMaxFreshIdx_Prop:
  forall {qs_schema idx} (r: sigT (@AllFinite qs_schema)),
    UnConstrFreshIdx (GetUnConstrRelation (projT1 r) idx)
                     (@IncrMaxFreshIdx _ idx r).
Proof.
  intros qsc idx r. pose (proj2_sig (projT2 ((projT2 r) idx))) as Hl.
  destruct Hl as [Hmap [Heqv Hdup]]. intro elem; intros Helem.
  apply Heqv in Helem. unfold lt.
  apply le_n_S; apply fold_right_max_is_max; apply Helem.
Qed.

Lemma IncrMaxFreshIdx_Refine:
  forall {qs_schema} {qidx: Fin.t (numRawQSschemaSchemas qs_schema)} (r: sigT (@AllFinite qs_schema)),
    refine
      {idx: nat | UnConstrFreshIdx (GetUnConstrRelation (projT1 r) qidx) idx}
      (ret (@IncrMaxFreshIdx _ qidx r)).
Proof.
  intros qsc qidx r. apply refine_pick. intros.
  apply Return_inv in H. subst. apply IncrMaxFreshIdx_Prop.
Qed.

Lemma insert_finite_helper:
  forall (qs_schema : RawQueryStructureSchema)
         (r_n: { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n })
         qidx tup,
    UnConstrFreshIdx (GetUnConstrRelation (projT1 r_n) qidx) (elementIndex tup) ->
    AllFinite (UpdateUnConstrRelation (projT1 r_n) qidx
                 (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) qidx))).
Proof.
  red; intros qsc r_n idx tup Hfresh idx'. destruct (Fin.eqb idx idx') eqn:idxeq.
  - apply Fin.eqb_eq in idxeq. subst idx'.
    destruct r_n as [r Hfin]. destruct (Hfin idx) as [l1 Hl1].
    destruct Hl1 as [l2 [Hmap [Hin Hdup]]].
    exists ((indexedElement tup) :: l1). cbn.
    rewrite get_update_unconstr_eq. red. exists (tup :: l2).
    
    split. simpl. rewrite <- Hmap. reflexivity. split.
    split; intros H; unfold EnsembleInsert, In in *;
      destruct H; simpl;
        [ left; symmetry; assumption
        | right; apply (Hin x); apply H
        | left; symmetry; assumption
        | right; apply (Hin x); apply H].
    
    simpl. apply NoDup_cons. red in Hfresh. simpl in Hfresh.
    assert (Hlist: forall (x: nat) l,
               (forall x', List.In x' l -> lt x' x) ->
               ~List.In x l).
    {
      intros x l Hx'. intro Hx. apply (Hx' x) in Hx.
      apply lt_irrefl in Hx. inversion Hx.
    }
    apply Hlist. apply forall_In_map. intros elem Helem.
    apply Hfresh. apply (Hin elem).
    assumption. assumption.
    
  - assert (Hidxeq: idx <> idx').
    { intro. apply Fin.eqb_eq in H. congruence. }
    destruct r_n as [r Hfin]. destruct (Hfin idx') as [l1 Hl1].
    exists l1. cbn. rewrite get_update_unconstr_neq.
    assumption. assumption.
Qed.

Lemma FiniteTables_AbsR'_Insert :
  forall (qs_schema : RawQueryStructureSchema) r_n
         (idx : Fin.t (numRawQSschemaSchemas qs_schema)) tup
         (H: UnConstrFreshIdx (GetUnConstrRelation (projT1 r_n) idx) (elementIndex tup)),
    refine
      {r_n0 : { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n } |
       FiniteTables_AbsR'
         (UpdateUnConstrRelation (projT1 r_n) idx (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) idx))) r_n0}
      (ret (existT AllFinite
              (UpdateUnConstrRelation (projT1 r_n) idx
                 (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) idx)))
              (insert_finite_helper r_n idx tup H))).
Proof.
  intros qsc r_n idx tup Hfreshn.
  unfold refine; intros r_n' Hr_n'. apply Return_inv in Hr_n'. subst r_n'.
  computes_to_econstructor. red; cbn. reflexivity.
Qed.


Transparent QSInsert.
Ltac drop_constraints_under_bind_insert :=
  unfold QSInsert;
  rewrite QSInsertSpec_UnConstr_refine; eauto; cycle 1;
    try (refine pick val true; [reflexivity | cbv; intros; exact I]);
    try (cbv -[refine]; intros; refine pick val true; try eauto);
    try (simplify with monad laws; higher_order_reflexivity).
  
Ltac drop_constraints_under_bind qs_schema bound_meth_tac :=
  hone representation using (@DropQSConstraints_AbsR qs_schema);
  repeat
    (match goal with
     | [H: constructorType _ _ |- _] =>
       apply Constructor_DropQSConstraints

     | [H: methodType _ _ _ |- _] =>
       simplify with monad laws; unfold Bind2;
       simplify with monad laws; cbn; etransitivity;
       [ eapply refine_bind;
         repeat
           (match goal with
            | [|- refine _ _] => reflexivity
            | [|- pointwise_relation _ refine _ _] =>
              intro a; etransitivity;
              [ apply change_refine_form
              | drop_constraints_under_bind_insert ]
            end)
       | etransitivity;
         [ eapply refine_bind;
           repeat
             (match goal with
              | [|- refine _ _] => bound_meth_tac
              | [|- pointwise_relation _ refine _ _] =>
                red; intros; higher_order_reflexivity
              end)
         | subst H; higher_order_reflexivity
         ]
       ]
     end).



Ltac hone_finite_under_bind_constructor :=
  match goal with
    [H: constructorType _ _ |- _] =>
    simplify with monad laws;
    refine pick val
      (existT _ (DropQSConstraints (QSEmptySpec _)) QSEmptyIsFinite);
    [ subst H; higher_order_reflexivity
    | apply FiniteTables_AbsR'_QSEmptySpec ]
  end.

Ltac hone_finite_under_bind_insert qs_schema idx :=
  match goal with
    [H': FiniteTables_AbsR' _ _ |- _] =>
    red; intros; red in H'; subst;
    rewrite (@IncrMaxFreshIdx_Refine qs_schema idx);
    simplify with monad laws; simpl;
    rewrite (@FiniteTables_AbsR'_Insert
               qs_schema _ idx
               ({| elementIndex := IncrMaxFreshIdx _;
                   indexedElement := icons2 _ inil2 |})
               (IncrMaxFreshIdx_Prop _));
    simplify with monad laws; higher_order_reflexivity
  end.

Ltac hone_finite_under_bind qs_schema idx :=
  hone representation using (@FiniteTables_AbsR' qs_schema);
  repeat
    (match goal with
     | [H: constructorType _ _ |- _] =>
       hone_finite_under_bind_constructor
         
     | [H: methodType _ _ _, H': FiniteTables_AbsR' _ _ |- _] =>
       simplify with monad laws; eapply refine_bind;
       repeat
         (match goal with
          | [|- refine _ _] =>
            red in H'; subst; higher_order_reflexivity
          | [|- pointwise_relation _ refine _ _] =>
            hone_finite_under_bind_insert qs_schema idx
          end)
  end).