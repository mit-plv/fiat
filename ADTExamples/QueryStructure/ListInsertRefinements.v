Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        QueryQSSpecs InsertQSSpecs QueryStructure
        ProcessScheduler.AdditionalLemmas GeneralQueryRefinements.

Definition decideable_Heading_Domain
           (h : Heading) :=
  forall (idx : Attributes h)
         (t t' : Domain h idx), {t = t'} + {t <> t'}.

Fixpoint Tuple_Agree_dec
         (h : Heading)
         (h_dec_eq : decideable_Heading_Domain h)
         (attrlist : list (Attributes h))
: forall (tup tup' : Tuple),
    {tupleAgree tup tup' attrlist} + {~tupleAgree tup tup' attrlist}.
Proof.
Admitted.

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

Definition In_List_Key
           (h : Heading)
           (h_dec_eq : decideable_Heading_Domain h)
           (attrlist : list (Attributes h))
           (tup : Tuple)
           (l : list Tuple) :=
  Check_List_Prop (fun tup' =>
                     if (Tuple_Agree_dec h_dec_eq attrlist tup tup')
                     then true
                     else false) l.

Lemma refine_unused_key_check
: forall (h : Heading)
         (h_dec_eq : decideable_Heading_Domain h)
         (attrlist attrlist' : list (Attributes h))
         (tup : Tuple)
         (rel : Ensemble Tuple)
         (l : list Tuple),
    EnsembleListEquivalence rel l
    -> refine {b | decides b
                           (forall tup' : Tuple,
                              rel tup' ->
                              tupleAgree tup tup' attrlist' ->
                              tupleAgree tup tup' attrlist)}
              (ret (In_List_Key h_dec_eq attrlist tup l)).
Admitted.

Lemma refine_unused_key_check'
: forall (h : Heading)
         (h_dec_eq : decideable_Heading_Domain h)
         (attrlist attrlist' : list (Attributes h))
         (tup : Tuple)
         (rel : Ensemble Tuple)
         (l : list Tuple),
    EnsembleListEquivalence rel l
    -> refine {b | decides b
                           (forall tup' : Tuple,
                              rel tup' ->
                              tupleAgree tup' tup attrlist' ->
                              tupleAgree tup' tup attrlist)}
              (ret (In_List_Key h_dec_eq attrlist tup l)).
Admitted.

Lemma refine_foreign_key_check
      (h : Heading)
      (rel : Ensemble Tuple)
      (l : list Tuple)
      (P : Ensemble Tuple)
      (P_dec : DecideableWhereClause P)
: EnsembleListEquivalence rel l
    -> refine {b  |
               decides b
                       (exists tup' : @Tuple h,
                          rel tup' /\
                          P tup')}
              (ret (Check_List_Prop cond l)).
Admitted.

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
                  simplify with monad laws);
             try (setoid_rewrite ImplementListInsert_neq;
                  eauto; simplify with monad laws);
             try (match goal with
                    | |- context [ (GetUnConstrRelation _ ?Ridx) ] =>
                      setoid_rewrite (@ImplementListInsert_neq _ Ridx)
                  end; eauto; simplify with monad laws)));
  try reflexivity.
