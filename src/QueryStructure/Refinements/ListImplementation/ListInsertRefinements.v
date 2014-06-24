Require Import String Omega List FunctionalExtensionality Ensembles Bool
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        QueryQSSpecs InsertQSSpecs QueryStructure
        ADTRefinement.BuildADTRefinements
        AdditionalLemmas GeneralQueryRefinements GeneralInsertRefinements
        GeneralQueryStructureRefinements ListQueryStructureRefinements.

Class List_Query_eq (As : list Type) :=
  { As_Query_eq : ilist Query_eq As}.

Instance nil_List_Query_eq :
  List_Query_eq [] :=
  {| As_Query_eq := inil _ |}.

Instance cons_List_Query_eq
         {A : Type}
         {As : list Type}
         {A_Query_eq : Query_eq A}
         {As_Query_eq' : List_Query_eq As}
:
  List_Query_eq (A :: As) :=
  {| As_Query_eq := icons _ A_Query_eq As_Query_eq |}.

Fixpoint Tuple_Agree_eq'
         (h : Heading)
         (attrlist : list (Attributes h))
         (attr_eq_dec : ilist (fun attr => Query_eq (Domain h attr)) attrlist)
         (tup tup' : @Tuple h)
: bool :=
  match attr_eq_dec with
      | inil => true
      | icons a attrlist' a_eq_dec attr_eq_dec' =>
        if @A_eq_dec _ a_eq_dec (tup a) (tup' a)
        then Tuple_Agree_eq' attr_eq_dec' tup tup'
        else false
  end.

Program Fixpoint ilist_map {A C : Type} {B : C -> Type}
           (As : list A)
           (f : A -> C)
           (il : ilist B (map f As))
: ilist (fun a => B (f a)) As :=
  match As as As' return ilist B (map f As') -> ilist (fun a => B (f a)) As' with
      | nil => fun _ => inil _
      | a :: As' => fun il => icons _ (ilist_hd il)
                                    (ilist_map As' f (ilist_tl il))
  end il.

Program Definition Tuple_Agree_eq h (attrlist : list (Attributes h))
        (attr_eq_dec : List_Query_eq (map (Domain h) attrlist)) tup tup' :=
  Tuple_Agree_eq' (ilist_map _ _ (@As_Query_eq _ attr_eq_dec)) tup tup'.

Lemma Tuple_Agree_eq_dec h attrlist attr_eq_dec (tup tup' : @Tuple h) :
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

Lemma Tuple_Agree_eq_dec' h attrlist attr_eq_dec (tup tup' : @Tuple h) :
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
           (attr_eq_dec : List_Query_eq (map (Domain h) attrlist)) (tup tup' : @Tuple h)
: {tupleAgree tup tup' attrlist} + {~ tupleAgree tup tup' attrlist}.
Proof.
  case_eq (Tuple_Agree_eq attrlist attr_eq_dec tup tup').
  left; eapply Tuple_Agree_eq_dec; eauto.
  right; eapply Tuple_Agree_eq_dec'; eauto.
Defined.

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
  apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ )) in H3;
    rewrite H3 in * ; simpl in *; eapply Tuple_Agree_eq_dec; eauto.
  destruct (Tuple_Agree_dec _ attr_eq_dec tup a); auto;
  [ apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ )) in t; rewrite t, orb_true_r
  | apply (proj1 (Tuple_Agree_eq_dec' _ _ _ _ )) in n; rewrite n, orb_false_r]; auto.
  destruct (Tuple_Agree_dec _ attr_eq_dec' tup a); auto;
  [ apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ )) in t; rewrite t
  | apply (proj1 (Tuple_Agree_eq_dec' _ _ _ _ )) in n0; rewrite n0]; auto.
  elimtype False; eapply (Tuple_Agree_eq_dec' _ attr_eq_dec); eauto.
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
  intros; destruct (Tuple_Agree_dec _ attr_eq_dec' tup a); auto;
  [ apply (proj1 (Tuple_Agree_eq_dec _ _ _ _ )) in t; rewrite t |
    apply (proj1 (Tuple_Agree_eq_dec' _ _ _ _ )) in n; rewrite n];
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
                              tupleAgree tup tup' attrlist' ->
                              tupleAgree tup tup' attrlist)}
              (ret (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l)).
Proof.
  intros.
  unfold refine; intros; inversion_by computes_to_inv;
  subst; econstructor.
  case_eq (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l); simpl; intros.
  eapply Check_Attr_Depend_dec; try apply H; eauto.
  destruct H as [l' [fresh_l' [l'_eq [_ equiv_l_l']]]]; subst.
  eapply in_map; eapply equiv_l_l'; eapply H1.
  unfold not; intros.
  eapply (Check_Attr_Depend_dec' attr_eq_dec attr_eq_dec'); eauto.
  destruct H as [l' [fresh_l' [l'_eq [_ equiv_l_l']]]]; subst.
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
                              tupleAgree tup' tup attrlist' ->
                              tupleAgree tup' tup attrlist)}
              (ret (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l)).
Proof.
  intros.
  unfold refine; intros; inversion_by computes_to_inv;
  subst; econstructor.
  case_eq (Check_Attr_Depend _ _ attr_eq_dec attr_eq_dec' tup l); simpl; intros.
  unfold tupleAgree in *; intros; apply sym_eq.
  eapply (Check_Attr_Depend_dec _ attr_eq_dec attr_eq_dec'); unfold tupleAgree;
  intros; try apply H; try rewrite H2; eauto.
  destruct H as [l' [fresh_l' [l'_eq [_ equiv_l_l']]]]; subst.
  eapply in_map; eapply equiv_l_l'; eapply H1.
  unfold not; intros.
  eapply (Check_Attr_Depend_dec' attr_eq_dec attr_eq_dec'); eauto.
  unfold tupleAgree in *; intros.
  destruct H as [l' [fresh_l' [l'_eq [_ equiv_l_l']]]]; subst.
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
                          P tup')}
              (ret (Check_List_Ex_Prop dec l)).
Proof.
  intros.
  unfold refine; intros; inversion_by computes_to_inv;
  subst; econstructor.
  case_eq (Check_List_Ex_Prop dec l); simpl; intros.
  destruct H as [l' [fresh_l' [l'_eq [_ equiv_l_l']]]]; subst.
  destruct (Check_List_Ex_Prop_dec dec P _ dec_decides_P H0);
    intuition.
  apply in_map_iff in H1; destruct_ex; intuition; subst.
  eexists; intuition; eauto; eapply equiv_l_l'; eauto.
  unfold not; intros; eapply Check_List_Ex_Prop_dec';
  eauto using dec_decides_P.
  destruct_ex; intuition; eexists; intuition; try apply H; eauto.
  destruct H as [l' [fresh_l' [l'_eq [_ equiv_l_l']]]]; subst.
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
  intros ** .
  rewrite get_update_unconstr_neq; eauto.
Qed.

Lemma ImplementListInsert_eq qsSchema Ridx
      (tup : Tuple)
      (or : UnConstrQueryStructure qsSchema)
      (nr : list (Tuple))
:
  EnsembleIndexedListEquivalence (GetUnConstrRelation or Ridx) nr
  -> refine
       {a |
        EnsembleIndexedListEquivalence
          (GetUnConstrRelation
             (@UpdateUnConstrRelation qsSchema or Ridx
                                     (EnsembleInsert {| tupleIndex := length nr;
                                                        indexedTuple := tup|}
                                                     (GetUnConstrRelation or Ridx))) Ridx) a}
       (ret (tup :: nr)).
Proof.
  unfold refine; intros; inversion_by computes_to_inv; subst; constructor.
  unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
  rewrite ith_replace_BoundIndex_eq.
  unfold EnsembleInsert, In, EnsembleIndexedListEquivalence in *;
    intuition.
  unfold In in *; destruct H; subst; simpl.
  omega.
  generalize (H0 _ H); omega.
  destruct H1 as [l' [l'_eq equiv_l']];
    econstructor 1 with ({| tupleIndex := length nr;
                            indexedTuple := tup|} :: l'); split; eauto.
  simpl; subst; reflexivity.
  unfold EnsembleListEquivalence  in *; intuition.
  econstructor; eauto.
  unfold not; intros.
  generalize (H0 _ (proj2 (H1 _) H2)); simpl.
  omega.
  unfold In in *; simpl; intuition.
  right; apply H1; auto.
  unfold In in *; simpl in *; intuition.
  right; apply H1; auto.
Qed.

Lemma ImplementListInsert_neq qsSchema Ridx Ridx'
      (tup : Tuple)
      (or : UnConstrQueryStructure qsSchema)
      (nr : list (Tuple))
:
  Ridx <> Ridx'
  -> EnsembleIndexedListEquivalence (GetUnConstrRelation or Ridx) nr
  -> refine
       {a |
        EnsembleIndexedListEquivalence
          (GetUnConstrRelation
             (@UpdateUnConstrRelation qsSchema or Ridx'
                                     (EnsembleInsert {| tupleIndex := length nr;
                                                        indexedTuple := tup|}
 (GetUnConstrRelation or Ridx'))) Ridx) a}
       (ret nr).
Proof.
  unfold refine; intros; inversion_by computes_to_inv; subst; constructor.
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

Tactic Notation "implement" "insert" "in" constr(relName) "with" "lists" "under" hyp(Rep_AbsR) :=
    hone method relName;
    [
      setoid_rewrite refineEquiv_split_ex;
      setoid_rewrite refineEquiv_pick_computes_to_and;
      simplify with monad laws;
      implement_foreign_key_check_w_lists Rep_AbsR;
      try (setoid_rewrite refine_foreign_key_check;
           [ | unfold Rep_AbsR in *; intuition; eauto ]);
      try simplify with monad laws;
      rewrite refine_pick_eq_ex_bind; unfold Rep_AbsR in *;
      split_and; simpl;
      rewrite refineEquiv_pick_pair_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; simpl;
      Split Constraint Checks;
        first [
          implement insert for lists; congruence
      | repeat (rewrite refine_pick_val; [rewrite refineEquiv_bind_unit | eassumption]); reflexivity ]
    | ].
