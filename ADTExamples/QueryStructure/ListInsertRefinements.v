Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        QueryQSSpecs InsertQSSpecs QueryStructure ProcessScheduler.AdditionalLemmas.

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
  : forall (h : Heading)
           (rel : Ensemble Tuple)
           (l : list Tuple)
           (P : Ensemble Tuple)
           (cond : Tuple -> bool),
      EnsembleListEquivalence rel l
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
