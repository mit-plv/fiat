Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        QueryQSSpecs InsertQSSpecs QueryStructure Bool
        ProcessScheduler.AdditionalLemmas GeneralQueryRefinements.

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
         (rel : Ensemble Tuple)
         (l : list Tuple),
    EnsembleListEquivalence rel l
    -> refine {b | decides b
                           (forall tup' : Tuple,
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
  unfold not; intros.
  eapply (Check_Attr_Depend_dec' attr_eq_dec attr_eq_dec'); eauto.
  intros; eapply H1; eauto; eapply H; eauto.
Qed.

Lemma refine_unused_key_check'
: forall (h : Heading)
         (attrlist attrlist' : list (Attributes h))
         (attr_eq_dec : List_Query_eq (map (Domain h) attrlist))
         (attr_eq_dec' : List_Query_eq (map (Domain h) attrlist'))
         (tup : Tuple)
         (rel : Ensemble Tuple)
         (l : list Tuple),
    EnsembleListEquivalence rel l
    -> refine {b | decides b
                           (forall tup' : Tuple,
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
  unfold not; intros.
  eapply (Check_Attr_Depend_dec' attr_eq_dec attr_eq_dec'); eauto.
  unfold tupleAgree in *; intros.
  apply sym_eq; apply H1; try eapply H; eauto.
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
      (rel : Ensemble Tuple)
      (l : list Tuple)
      (P : Ensemble Tuple)
      (P_dec : DecideableEnsemble P)
: EnsembleListEquivalence rel l
    -> refine {b  |
               decides b
                       (exists tup' : @Tuple h,
                          rel tup' /\
                          P tup')}
              (ret (Check_List_Ex_Prop dec l)).
Proof.
  intros.
  unfold refine; intros; inversion_by computes_to_inv;
  subst; econstructor.
  case_eq (Check_List_Ex_Prop dec l); simpl; intros.
  destruct (Check_List_Ex_Prop_dec dec P _ dec_decides_P H0);
    eexists; intuition; try apply H; eauto.
  unfold not; intros; eapply Check_List_Ex_Prop_dec';
  eauto using dec_decides_P.
  destruct_ex; intuition; eexists; intuition; try apply H; eauto.
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

Lemma ImplementListInsert_eq qsSchema Ridx
      (tup : Tuple)
      (or : UnConstrQueryStructure qsSchema)
      (nr : list (Tuple))
:
  EnsembleListEquivalence (GetUnConstrRelation or Ridx) nr
  -> refine
       {a |
        EnsembleListEquivalence
          (GetUnConstrRelation
             (UpdateUnConstrRelation qsSchema or Ridx
                                     (RelationInsert tup (GetUnConstrRelation or Ridx))) Ridx) a}
       (ret (tup :: nr)).
Proof.
  unfold refine; intros; inversion_by computes_to_inv; subst; constructor.
  unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
  rewrite ith_replace_BoundIndex_eq.
  unfold EnsembleListEquivalence, RelationInsert, In, List.In in *; split; intuition.
  right; apply H; auto.
  right; apply H; auto.
Qed.

Lemma ImplementListInsert_neq qsSchema Ridx Ridx'
      (tup : Tuple)
      (or : UnConstrQueryStructure qsSchema)
      (nr : list (Tuple))
:
  Ridx <> Ridx'
  -> EnsembleListEquivalence (GetUnConstrRelation or Ridx) nr
  -> refine
       {a |
        EnsembleListEquivalence
          (GetUnConstrRelation
             (UpdateUnConstrRelation qsSchema or Ridx'
                                     (RelationInsert tup (GetUnConstrRelation or Ridx'))) Ridx) a}
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
             try (setoid_rewrite ImplementListInsert_neq;
                  eauto; try simplify with monad laws);
             try (match goal with
                    | |- context [ (GetUnConstrRelation _ ?Ridx) ] =>
                      setoid_rewrite (@ImplementListInsert_neq _ Ridx)
                  end; eauto; try simplify with monad laws)));
  try reflexivity.
