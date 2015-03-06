Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles Coq.Bool.Bool
        ADTSynthesis.Computation
        ADTSynthesis.ADT
        ADTSynthesis.ADTRefinement
        ADTSynthesis.ADTNotation
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Operations.Query
        ADTSynthesis.QueryStructure.Specification.Operations.Insert
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.Ensembles.EnsembleListEquivalence
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.InsertRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryStructureRefinements
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements.

Fixpoint Check_List_Prop {A}
         (cond : A -> bool)
         (l : list A)
: bool :=
  match l with
    | [] => true
    | a :: l' => if (cond a) then
                   Check_List_Prop cond l'
                 else false
  end.

Lemma Check_List_Prop_dec {A} :
  forall (cond : A -> bool)
         (P : Ensemble A)
         (l : list A),
    (forall a, cond a = true <-> P a)
    -> (Check_List_Prop cond l = true <->
        forall a', List.In a' l -> P a').
Proof.
  split; induction l; simpl; intros; intuition; subst.
  generalize (H a'); find_if_inside; intuition; eauto.
  generalize (H a'); find_if_inside; intuition; eauto.
  generalize (H a); find_if_inside; intuition; eauto.
Qed.

Lemma Check_List_Prop_dec' {A} :
  forall (cond : A -> bool)
         (P : Ensemble A)
         (l : list A),
    (forall a, cond a = true <-> P a)
    -> (Check_List_Prop cond l = false <->
        (exists a', List.In a' l /\ ~ P a')).
Proof.
  split; induction l; simpl; intros; intuition; subst.
  generalize (H a); find_if_inside; intuition; eauto.
  destruct_ex; intuition; intuition; eauto.
  eexists; intuition.
  destruct_ex; intuition.
  generalize (H a); find_if_inside; intuition; eauto.
  destruct_ex; subst; intuition; eauto.
  subst; intuition.
Qed.

Definition Check_Attr_Depend
           (h : Heading)
           (attrlist attrlist' : list (Attributes h))
           (attr_eq_dec : List_Query_eq (map (Domain h) attrlist))
           (attr_eq_dec' : List_Query_eq (map (Domain h) attrlist'))
           (tup : Tuple)
           (l : list Tuple) :=
  Check_List_Prop (fun tup' => orb (negb (Tuple_Agree_eq _ attr_eq_dec' tup tup'))
                                   (Tuple_Agree_eq _ attr_eq_dec tup tup')) l.

Lemma Check_Attr_Depend_dec
: forall (h : Heading)
         (attrlist attrlist' : list (Attributes h))
         (attr_eq_dec : List_Query_eq (map (Domain h) attrlist))
         (attr_eq_dec' : List_Query_eq (map (Domain h) attrlist'))
         (tup : Tuple)
         (l : list Tuple),
    Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l = true ->
    (forall tup' : Tuple, List.In tup' l
                          -> tupleAgree tup tup' attrlist'
                          -> tupleAgree tup tup' attrlist).
Proof.
  unfold Check_Attr_Depend; intros.
  eapply Check_List_Prop_dec  with
  (P := fun tup' : Tuple => tupleAgree tup tup' attrlist'
                            -> tupleAgree tup tup' attrlist) in H; eauto.
  intuition.
  apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ _ )) in H3;
    rewrite H3 in * ; simpl in *; eapply Tuple_Agree_eq_dec; eauto.
  destruct (Tuple_Agree_dec _ _ attr_eq_dec tup a); auto;
  [ apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ _ )) in t; rewrite t, orb_true_r
  | apply (proj1 (Tuple_Agree_eq_dec' _ _ _ _ _ )) in n; rewrite n, orb_false_r]; auto.
  destruct (Tuple_Agree_dec _ _ attr_eq_dec' tup a); auto;
  [ apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ _ )) in t; rewrite t
  | apply (proj1 (Tuple_Agree_eq_dec' _ _ _ _ _ )) in n0; rewrite n0]; auto.
  elimtype False; eapply (Tuple_Agree_eq_dec' _ _ attr_eq_dec); eauto.
  apply H2; eapply Tuple_Agree_eq_dec; eauto.
Qed.

Lemma Check_Attr_Depend_dec'
: forall (h : Heading)
         (attrlist attrlist' : list (Attributes h))
         (attr_eq_dec : List_Query_eq (map (Domain h) attrlist))
         (attr_eq_dec' : List_Query_eq (map (Domain h) attrlist'))
         (tup : Tuple)
         (l : list Tuple),
    Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l = false ->
    ~ (forall tup' : Tuple, List.In tup' l
                            -> tupleAgree tup tup' attrlist'
                            -> tupleAgree tup tup' attrlist).
Proof.
  unfold Check_Attr_Depend; intros.
  eapply Check_List_Prop_dec' with
  (P := fun tup' : Tuple =>
          ~ tupleAgree tup tup' attrlist' \/
          tupleAgree tup tup' attrlist) in H; eauto.
  destruct_ex; intuition; eauto.
  intros; destruct (Tuple_Agree_dec _ _ attr_eq_dec' tup a); auto;
  [ apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ _ )) in t; rewrite t |
    apply (proj1 (Tuple_Agree_eq_dec' _ _ _ _ _ )) in n; rewrite n];
  simpl; intuition.
  right;   eapply Tuple_Agree_eq_dec; eauto.
  elimtype False; apply H1; eapply Tuple_Agree_eq_dec; eauto.
  eapply Tuple_Agree_eq_dec; eauto.
  left; eapply Tuple_Agree_eq_dec'; eauto.
Qed.

Lemma refine_unused_key_check
: forall (h : Heading)
         (attrlist attrlist' : list (Attributes h))
         (attr_eq_dec : List_Query_eq (map (Domain h) attrlist))
         (attr_eq_dec' : List_Query_eq (map (Domain h) attrlist'))
         (tup : Tuple)
         (rel : Ensemble IndexedTuple)
         (l : list Tuple),
    EnsembleIndexedListEquivalence  rel l
    -> refine {b | decides b
                           (forall tup' : IndexedTuple,
                              rel tup' ->
                              tupleAgree tup (indexedElement tup') attrlist' ->
                              tupleAgree tup (indexedElement tup') attrlist)}
              (ret (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l)).
Proof.
  intros.
  unfold refine; intros;  computes_to_inv;
  subst; computes_to_econstructor.
  case_eq (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l); simpl; intros.
  eapply Check_Attr_Depend_dec; try apply H; eauto.
  destruct H as [l' [fresh_l' [l'_eq [equiv_l_l' _]]]]; subst.
  eapply in_map; eapply equiv_l_l'; eapply H1.
  unfold not; intros.
  eapply (Check_Attr_Depend_dec' attr_eq_dec attr_eq_dec'); eauto.
  destruct H as [l' [fresh_l' [l'_eq [equiv_l_l' _]]]]; subst.
  intros.
  apply (in_map_iff indexedTuple) in H; destruct_ex;
  intuition; subst.
  intros; eapply H1; eauto.
  eapply equiv_l_l'; eauto.
Qed.

Lemma refine_unused_key_check'
: forall (h : Heading)
         (attrlist attrlist' : list (Attributes h))
         (attr_eq_dec : List_Query_eq (map (Domain h) attrlist))
         (attr_eq_dec' : List_Query_eq (map (Domain h) attrlist'))
         (tup : Tuple)
         (rel : Ensemble IndexedTuple)
         (l : list Tuple),
    EnsembleIndexedListEquivalence  rel l
    -> refine {b | decides b
                           (forall tup' : IndexedTuple,
                              rel tup' ->
                              tupleAgree (indexedElement tup') tup attrlist' ->
                              tupleAgree (indexedElement tup') tup attrlist)}
              (ret (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l)).
Proof.
  intros.
  unfold refine; intros;  computes_to_inv;
  subst; computes_to_econstructor.
  case_eq (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l); simpl; intros.
  unfold tupleAgree in *; intros; apply sym_eq.
  eapply (Check_Attr_Depend_dec _ attr_eq_dec attr_eq_dec'); unfold tupleAgree;
  intros; try apply H; try rewrite H2; eauto.
  destruct H as [l' [fresh_l' [l'_eq [equiv_l_l' _]]]]; subst.
  eapply in_map; eapply equiv_l_l'; eapply H1.
  unfold not; intros.
  eapply (Check_Attr_Depend_dec' attr_eq_dec attr_eq_dec'); eauto.
  unfold tupleAgree in *; intros.
  destruct H as [l' [fresh_l' [l'_eq [equiv_l_l' _]]]]; subst.
  apply (in_map_iff indexedTuple) in H2; destruct_ex; intuition;
  subst.
  apply sym_eq; apply H1; try eapply H; eauto.
  eapply equiv_l_l'; eauto.
  intros; rewrite H3; eauto.
Qed.

Fixpoint Check_List_Ex_Prop {A}
         (cond : A -> bool)
         (l : list A)
: bool :=
  match l with
    | [] => false
    | a :: l' => if (cond a) then
                   true else
                   Check_List_Ex_Prop cond l'
  end.

Lemma Check_List_Ex_Prop_dec {A} :
  forall (cond : A -> bool)
         (P : Ensemble A)
         (l : list A),
    (forall a, cond a = true <-> P a)
    -> (Check_List_Ex_Prop cond l = true ->
        exists a', List.In a' l /\ P a').
Proof.
  induction l; simpl; intros; intuition; subst.
  generalize (H a); find_if_inside; intuition; eauto.
  destruct_ex; intuition; eauto.
Qed.

Lemma Check_List_Ex_Prop_dec' {A} :
  forall (cond : A -> bool)
         (P : Ensemble A)
         (l : list A),
    (forall a, cond a = true <-> P a)
    -> (Check_List_Ex_Prop cond l = false ->
        ~ exists a', List.In a' l /\ P a').
Proof.
  induction l; simpl; intros; intuition; subst.
  destruct_ex; intuition.
  destruct_ex; intuition; subst; eauto;
  generalize (H x); find_if_inside; intuition; eauto.
Qed.

Lemma refine_foreign_key_check
      (h : Heading)
      (rel : Ensemble IndexedTuple)
      (l : list Tuple)
      (P : Ensemble Tuple)
      (P_dec : DecideableEnsemble P)
: EnsembleIndexedListEquivalence rel l
    -> refine {b  |
               decides b
                       (exists tup' : @IndexedTuple h,
                          rel tup' /\
                          P (indexedElement tup'))}
              (ret (Check_List_Ex_Prop (DecideableEnsembles.dec) l)).
Proof.
  intros.
  unfold refine; intros;  computes_to_inv;
  subst; computes_to_econstructor.
  case_eq (Check_List_Ex_Prop DecideableEnsembles.dec l); simpl; intros.
  destruct H as [l' [fresh_l' [l'_eq [equiv_l_l' _]]]]; subst.
  destruct (Check_List_Ex_Prop_dec DecideableEnsembles.dec P _ dec_decides_P H0);
    intuition.
  apply in_map_iff in H1; destruct_ex; intuition; subst.
  eexists; intuition; eauto; eapply equiv_l_l'; eauto.
  unfold not; intros; eapply Check_List_Ex_Prop_dec';
  eauto using dec_decides_P.
  destruct_ex; intuition; eexists; intuition; try apply H; eauto.
  destruct H as [l' [fresh_l' [l'_eq [equiv_l_l' _]]]]; subst.
  eapply in_map; eapply equiv_l_l'; unfold In; eauto.
Qed.

Add Parametric Morphism {A: Type} (b : bool):
  (If_Then_Else b)
    with signature (
      @refine A ==> @refine A ==> refine)
      as refine_refine_if.
Proof.
  unfold refine, If_Then_Else; intros.
  destruct b; eauto.
Qed.

Lemma refine_list_insert_in_other_table :
  forall (db_schema : QueryStructureSchema) (qs : UnConstrQueryStructure db_schema)
         (index1 index2 : BoundedString) (store : list Tuple),
    EnsembleIndexedListEquivalence (GetUnConstrRelation qs index2) store ->
    index1 <> index2 ->
    forall inserted : @IndexedTuple _,
      EnsembleIndexedListEquivalence
        (GetUnConstrRelation
           (UpdateUnConstrRelation qs index1
                                   (EnsembleInsert inserted (GetUnConstrRelation qs index1))) index2)
        (store).
Proof.
  intros; rewrite get_update_unconstr_neq; eauto.
Qed.

Ltac refine_list_insert_in_other_table :=
  match goal with
    | [ |- appcontext [
               EnsembleIndexedListEquivalence
                 (GetUnConstrRelation
                    (UpdateUnConstrRelation ?qs ?index1
                                            (EnsembleInsert ?inserted
                                                            (GetUnConstrRelation ?qs ?index1)))
                    ?index2) ] ] => apply (@refine_list_insert_in_other_table _ qs index1 index2);
                                   [ eauto | intuition discriminate ]
  end.

Lemma ImplementListInsert_eq qsSchema Ridx
      (tup : Tuple)
      (or : UnConstrQueryStructure qsSchema)
      (nr : list (Tuple))
      (bound : nat)
:
  EnsembleIndexedListEquivalence (GetUnConstrRelation or Ridx) nr
  -> (UnConstrFreshIdx (GetUnConstrRelation or Ridx) bound)
  -> refine
       {a |
        EnsembleIndexedListEquivalence
          (GetUnConstrRelation
             (@UpdateUnConstrRelation qsSchema or Ridx
                                     (EnsembleInsert {| elementIndex := bound;
                                                        indexedElement := tup|}
                                                     (GetUnConstrRelation or Ridx))) Ridx) a}
       (ret (tup :: nr)).
Proof.
  unfold refine; intros;  computes_to_inv; subst; computes_to_constructor.
  unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
  rewrite ith_replace_BoundIndex_eq.
  unfold EnsembleInsert, In, EnsembleIndexedListEquivalence, UnConstrFreshIdx in *;
    intuition.
  exists (S bound); unfold In in *; destruct_ex; subst; simpl.
  intros; intuition; subst.
  simpl. omega.
  destruct H2 as [l' [l'_eq [equiv_l' NoDup_l']]].
    econstructor 1 with ({| elementIndex := bound;
                            indexedElement := tup|} :: l'); split; eauto.
  simpl; subst; reflexivity.
  unfold EnsembleListEquivalence in *; intuition.
  unfold In in *; subst; intuition.
  subst; simpl; eauto.
  simpl; right; eapply equiv_l'; eauto.
  simpl in *; unfold In; intuition.
  eapply equiv_l' in H2; eauto.
  simpl; econstructor; eauto.
  unfold not; intros.
  rewrite in_map_iff in H; destruct_ex; intuition.
  apply equiv_l' in H3; apply H0 in H3; omega.
Qed.

Lemma ImplementListInsert_neq qsSchema Ridx Ridx'
      (tup : Tuple)
      (or : UnConstrQueryStructure qsSchema)
      (nr : list (Tuple))
      m
:
  Ridx <> Ridx'
  -> EnsembleIndexedListEquivalence (GetUnConstrRelation or Ridx) nr
  -> refine
       {a |
        EnsembleIndexedListEquivalence
          (GetUnConstrRelation
             (@UpdateUnConstrRelation qsSchema or Ridx'
                                     (EnsembleInsert {| elementIndex := m;
                                                        indexedElement := tup|}
 (GetUnConstrRelation or Ridx'))) Ridx) a}
       (ret nr).
Proof.
  unfold refine; intros;  computes_to_inv; subst; computes_to_constructor.
  unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
  rewrite ith_replace_BoundIndex_neq; eauto using string_dec.
Qed.

Tactic Notation "implement" "insert" "for" "lists" :=
  repeat (progress
            (try (setoid_rewrite ImplementListInsert_eq; eauto;
                  try simplify with monad laws);
             try (match goal with
                      |- context
                           [{a | EnsembleIndexedListEquivalence
                                   ((UpdateUnConstrRelation ?QSSchema ?c ?Ridx
                                                            (EnsembleInsert ?n (?c!?R)))!?R')%QueryImpl a}%comp] =>
                      setoid_rewrite ((@ImplementListInsert_neq QSSchema
                                                                {| bindex := R' |}
                                                                {| bindex := R |} n c))
                  end;
                    eauto; try simplify with monad laws);
             try (match goal with
                    | |- context [ (GetUnConstrRelation _ ?Ridx) ] =>
                      setoid_rewrite (@ImplementListInsert_neq _ Ridx)
                  end; eauto; try simplify with monad laws)));
  try reflexivity.

Ltac implement_foreign_key_check_w_lists H :=
  repeat (match goal with
              |- context [
                     forall tup' : @Tuple ?h,
                       (?qs ! ?R )%QueryImpl tup' ->
                       tupleAgree ?n tup' ?attrlist2%SchemaConstraints ->
                       tupleAgree ?n tup' ?attrlist1%SchemaConstraints ]
              =>
              setoid_rewrite (@refine_unused_key_check h attrlist1 attrlist2 _ _ n (qs ! R )%QueryImpl);
              [ simplify with monad laws |
                unfold H in *; split_and; eauto ]
              | |- context [
                       forall tup' : @Tuple ?h,
                         (?qs ! ?R )%QueryImpl tup' ->
                         tupleAgree tup' ?n ?attrlist2%SchemaConstraints ->
                         tupleAgree tup' ?n  ?attrlist1%SchemaConstraints]
                =>
                setoid_rewrite (@refine_unused_key_check' h attrlist1 attrlist2 _ _ n (qs ! R )%QueryImpl);
              [ simplify with monad laws |
                unfold H in *; split_and; eauto ]
          end).
