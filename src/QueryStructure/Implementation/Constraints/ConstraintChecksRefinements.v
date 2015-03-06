Require Export ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations ADTSynthesis.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List Coq.Arith.Compare_dec Coq.Bool.Bool String
        ADTSynthesis.Common.BoolFacts
        ADTSynthesis.Common.List.PermutationFacts
        ADTSynthesis.Common.List.ListMorphisms
        ADTSynthesis.QueryStructure.Specification.Operations.FlattenCompList
        ADTSynthesis.Common.Ensembles.EnsembleListEquivalence
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryRefinements
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.LogicFacts
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.QueryStructure.Specification.Constraints.tupleAgree
        ADTSynthesis.QueryStructure.Specification.Operations.Mutate.

Unset Implicit Arguments.

Local Transparent Count Query_For.

Section ConstraintCheckRefinements.
  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesAttributeConstraints
       SatisfiesTupleConstraints.

Fixpoint Tuple_Agree_eq'
         {h : Heading}
         {attrlist : list (Attributes h)}
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

Class List_Query_eq (As : list Type) :=
  { As_Query_eq : ilist Query_eq As}.

Program Definition Tuple_Agree_eq {h} (attrlist : list (Attributes h))
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


  Lemma tupleAgree_sym :
    forall (heading: Heading) tup1 tup2 attrs,
      @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
  Proof.
    intros; unfold tupleAgree;
    split; intros; rewrite H; eauto.
  Qed.

  Lemma refine_Iterate_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As)),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex As P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Lemma refine_Iterate_Ensemble_filter {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As))
           (filter : Ensemble nat)
           (filter_dec : DecideableEnsemble filter),
      refine {b | decides b (forall idx : BoundedIndex As,
                               filter (ibound idx) -> P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex_filter
                               As (@dec _ _ filter_dec) P )}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv_filter' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H.
    apply Iterate_Ensemble_equiv_filter''; auto using string_dec.
  Qed.

  Lemma refine_decides_Equiv_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P P' : Ensemble (BoundedIndex As))
           (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (forall idx : BoundedIndex As, P' idx)}.
  Proof.
    intros * equiv_P'_P v Comp_v.
     computes_to_inv; computes_to_constructor; destruct v; simpl in *.
    intros; eapply equiv_P'_P; eauto.
    unfold not; intros; eapply Comp_v; eapply equiv_P'_P; eauto.
  Qed.

  Corollary Iterate_Ensemble_filter_neq {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As))
           (Ridx : BoundedIndex As),
    (forall idx : BoundedIndex As, idx <> Ridx -> P idx)
    <-> (@Iterate_Ensemble_BoundedIndex_filter
           As (fun idx =>
                 if (eq_nat_dec (ibound Ridx) idx)
                 then false else true) P ).
  Proof.
    intros.
    assert (forall a : nat,
              (if eq_nat_dec (ibound Ridx) a then false else true) = true
              <-> a <> ibound Ridx)
      as filter_dec'
      by (intros; find_if_inside; try rewrite e; intuition).
    assert ((forall idx : BoundedIndex As, idx <> Ridx -> P idx)
            <-> (forall idx  : BoundedIndex As,
                   ibound idx <> ibound Ridx -> P idx)).
    { split; intros; eauto.
      apply H; destruct idx as [idx [n nth_n] ];
      destruct Ridx as [Ridx [n' nth_n'] ]; simpl in *.
      unfold not; intros; apply H0; injection H1; auto.
      apply H; unfold not; intros; apply H0.
      destruct idx as [idx [n nth_n] ];
        destruct Ridx as [Ridx [n' nth_n'] ]; simpl in *.
      clear H0; revert nth_n; rewrite H1; intros.
      assert (Ridx = idx) by
          (rewrite nth_n' in nth_n; congruence).
      revert nth_n' nth_n; rewrite H0.
      intros; repeat f_equal.
      apply (eq_proofs_unicity_Opt_A string_dec).
    }
    rewrite H.
    split; intros.
    - eapply Iterate_Ensemble_equiv_filter'' with
      (filter := fun idx => idx <> ibound Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |}); eauto.
      apply string_dec.
    - eapply Iterate_Ensemble_equiv_filter'  with
      (Visited := [])
      (filter := fun idx => idx <> ibound Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |});
      unfold dec; eauto using string_dec.
      intros; destruct n; simpl in *; discriminate.
  Qed.

  Lemma refine_Iterate_Equiv_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As As' : list string)
           (P : Ensemble (BoundedIndex As))
           (P' : Ensemble (BoundedIndex As'))
           (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex As' P')}.
  Proof.
    intros; setoid_rewrite refine_Iterate_Ensemble; try eassumption.
    intros v Comp_v.
     computes_to_inv; computes_to_constructor; destruct v; simpl in *.
    apply Iterate_Ensemble_equiv'' with (Visited := []);
      eauto using string_dec; simpl.
    apply equiv_P'_P; intros;
    apply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec; simpl.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply Comp_v.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
    apply equiv_P'_P;
    apply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec; simpl.
    destruct n; simpl; intros; discriminate.
  Qed.

  (* So that things play nicely with setoid rewriting *)
  Definition If_Then_Else {A}  (b : bool) (t e : A)
    := if b then t else e.

  Lemma refine_trivial_if_then_else :
    forall x,
      refine
        (If_Then_Else x (ret true) (ret false))
        (ret x).
  Proof.
    destruct x; reflexivity.
  Qed.

  Program Fixpoint Iterate_Decide_Comp' (A : Set)
          (Remaining Visited : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        Bind {b' |
              decides b' (P {| bindex := a;
                               indexb := {| ibound := List.length Visited;
                                            boundi := _ |} |})}%comp
             (fun b' =>
                If_Then_Else b'
                             (Iterate_Decide_Comp' _ Remaining' (Visited ++ [a]) _)
                             (ret false))
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.

  Lemma refine_Iterate_Decided_Ensemble' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      refine {b | decides b (Iterate_Ensemble_BoundedIndex' Visited Remaining P)}
                  (Iterate_Decide_Comp' _ Remaining Visited P).
  Proof.
    induction Remaining; simpl; intros.
    - computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
    - computes_to_econstructor; computes_to_inv; destruct_ex;
      split_and;  computes_to_inv; subst.
      destruct v0; simpl in *.
      { destruct v; simpl in *; intuition; intros; eauto.
        - generalize (IHRemaining (Visited ++ [a]) _ _ H').
          intros;  computes_to_inv; simpl in *; eauto.
        - generalize (IHRemaining (Visited ++ [a]) _ _ H').
          intros;  computes_to_inv; simpl in *; eauto.
      }
      {  computes_to_inv; subst; simpl; intuition. }
  Qed.

  Definition Iterate_Decide_Comp
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound))
  : Comp bool :=
    Iterate_Decide_Comp' _ Bound [] P.

  Definition Iterate_Decide_Comp_BoundedIndex
  : forall (Bound : list string)
           (P : Ensemble (BoundedIndex Bound)),
      refine {b | decides b (forall Ridx', P Ridx')}
             (Iterate_Decide_Comp _ P).
  Proof.
    intros.
    setoid_rewrite refine_Iterate_Ensemble; auto using string_dec.
    setoid_rewrite refine_Iterate_Decided_Ensemble'; auto using string_dec.
    reflexivity.
  Qed.

  (* Variants for inserting additional assumptions into the
   decision procedure. *)
  Program Lemma refine_Iterate_Ensemble_Pre {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As))
           (Q : Prop),
      refine {b | Q -> decides b (forall idx : BoundedIndex As, P idx)}
             {b | Q -> decides b (@Iterate_Ensemble_BoundedIndex As P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *; apply H in H0.
    intros; eapply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H0.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Program Fixpoint Iterate_Decide_Comp'_Pre (A : Set)
          (Remaining Visited : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
          (Q : Prop)
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        Bind {b' | Q ->
              decides b' (P {| bindex := a;
                               indexb := {| ibound := List.length Visited;
                                            boundi := _ |} |})}%comp
             (fun b' =>
                If_Then_Else b'
                             (Iterate_Decide_Comp'_Pre _ Remaining' (Visited ++ [a]) _ Q)
                             (ret false))
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.

  Lemma refine_Iterate_Decided_Ensemble'_Pre {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
           (Q : Prop),
      refine {b | Q -> decides b (Iterate_Ensemble_BoundedIndex' Visited Remaining P)}
             (Iterate_Decide_Comp'_Pre _ Remaining Visited P Q).
  Proof.
    induction Remaining; simpl; intros.
    - computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
    - computes_to_econstructor; computes_to_inv; destruct_ex;
      split_and;  computes_to_inv; subst.
      destruct v0; simpl in *.
      {  destruct v; simpl in *; intuition; intros; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ _ H').
           intros;  computes_to_inv; simpl in *; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ _ H').
           intros;  computes_to_inv; simpl in *; eauto.
           eapply H; eauto.
      }
      {  computes_to_inv; subst; simpl; intuition. }
  Qed.

  Definition Iterate_Decide_Comp_Pre
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound))
          (Q : Prop)
  : Comp bool :=
    Iterate_Decide_Comp'_Pre _ Bound [] P Q.

  Definition Iterate_Decide_Comp_BoundedIndex_Pre
  : forall (Bound : list string)
           (P : Ensemble (BoundedIndex Bound))
           (Q : Prop),
      refine {b | Q -> decides b (forall Ridx', P Ridx')}
             (Iterate_Decide_Comp_Pre _ P Q).
  Proof.
    intros.
    setoid_rewrite refine_Iterate_Ensemble_Pre; auto using string_dec.
    setoid_rewrite refine_Iterate_Decided_Ensemble'_Pre; auto using string_dec.
    reflexivity.
  Qed.

  Lemma decides_True :
    refine {b | decides b True}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_True_Pre (Q : Prop) :
    refine {b | Q -> decides b True}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_2_True (A : Type) (B : A -> Type) :
    refine {b' | decides b' (forall a : A, B a -> True)}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_3_True (A B : Type) (C : B -> Type) :
    refine {b' | decides b' (A -> forall b : B, C b -> True)}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_neq (A : Type) (B : Prop) (a : A) :
    refine {b' | decides b' (a <> a -> B)}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
    congruence.
  Qed.

  Definition Ensemble_opt_BoundedIndex_app_comm_cons {A : Set}
    (a : A)
    (As As' : list A)
    (P : BoundedIndex (As ++ a :: As') -> option Prop)
  : BoundedIndex ((As ++ [a]) ++ As') -> option Prop.
    rewrite app_comm_cons' in P; exact P.
  Defined.

  Program Fixpoint Iterate_Decide_Comp_opt' (A : Set)
          (Remaining Visited : list A)
          (P : BoundedIndex (Visited ++ Remaining) -> option Prop )
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        match (P {| bindex := a;
                    indexb := {| ibound := List.length Visited;
                                 boundi := _ |} |}) with
          | Some P' => b' <- {b' | decides b' P'};
                      If_Then_Else b'
                                   (Iterate_Decide_Comp_opt' _ Remaining' (Visited ++ [a])
                                                             (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P))
                                   (ret false)
          | None => (Iterate_Decide_Comp_opt' _ Remaining' (Visited ++ [a])
                                              (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P))
        end
    end%comp.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.

  Lemma refine_Iterate_Decide_Comp'
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : BoundedIndex (Visited ++ Remaining)
                -> option Prop),
      refine (@Iterate_Decide_Comp' _ Remaining Visited (fun idx => match P idx with
                                                                      | Some P' => P'
                                                                      | None => True
                                                                    end))
             (@Iterate_Decide_Comp_opt' _ Remaining Visited P).
    induction Remaining; simpl; intros.
    - reflexivity.
    - destruct (P ``(a)).
      + f_equiv; unfold pointwise_relation; intros.
        destruct a0; simpl; try reflexivity.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
      + rewrite decides_True; simplify with monad laws; simpl.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp
  : forall (Bound : list string)
           (P : BoundedIndex Bound -> option Prop),
      refine (@Iterate_Decide_Comp _ (fun idx => match P idx with
                                                 | Some P' => P'
                                                 | None => True
                                               end))
             (@Iterate_Decide_Comp_opt' _ Bound [] P).
  Proof.
    intros; unfold Iterate_Decide_Comp;
    rewrite refine_Iterate_Decide_Comp'.
    reflexivity.
    apply string_dec.
  Qed.

  Program Fixpoint Iterate_Decide_Comp_opt'_Pre (A : Set)
          (Remaining Visited : list A)
          (P : BoundedIndex (Visited ++ Remaining) -> option Prop)
          (Q : Prop)
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        match (P {| bindex := a;
                    indexb := {| ibound := List.length Visited;
                                 boundi := _ |} |}) with
          | Some P' => b' <- {b' | Q -> decides b' P'};
                      If_Then_Else b'
                                   (Iterate_Decide_Comp_opt'_Pre _ Remaining' (Visited ++ [a])
                                                             (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P) Q)
                                   (ret false)
          | None => (Iterate_Decide_Comp_opt'_Pre _ Remaining' (Visited ++ [a])
                                              (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P) Q)
        end
    end%comp.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.

  Lemma refine_Iterate_Decide_Comp'_Pre
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : BoundedIndex (Visited ++ Remaining) -> option Prop)
           (Q : Prop),
      refine (@Iterate_Decide_Comp'_Pre _ Remaining Visited
                                        (fun idx => match P idx with
                                                      | Some P' => P'
                                                      | None => True
                                                    end) Q)
             (@Iterate_Decide_Comp_opt'_Pre _ Remaining Visited P Q).
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - destruct (P ``(a)).
      + f_equiv; unfold pointwise_relation; intros.
        destruct a0; simpl; try reflexivity.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
      + rewrite decides_True_Pre; simplify with monad laws; simpl.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp_Pre
  : forall (Bound : list string)
           (P : BoundedIndex Bound -> option Prop)
           (Q : Prop),
      refine (@Iterate_Decide_Comp_Pre _ (fun idx => match P idx with
                                                 | Some P' => P'
                                                 | None => True
                                               end) Q)
             (@Iterate_Decide_Comp_opt'_Pre _ Bound [] P Q).
  Proof.
    intros; unfold Iterate_Decide_Comp_Pre;
    rewrite refine_Iterate_Decide_Comp'_Pre.
    reflexivity.
    apply string_dec.
  Qed.

  Lemma refine_Iterate_Decide_Comp_equiv_Pre
        (Q Q' : Prop)
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P P' : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx -> P' idx)
      -> (forall idx, ~ P idx -> ~ P' idx)
      -> (Q -> Q')
      -> refine (@Iterate_Decide_Comp'_Pre _ Remaining Visited P' Q)
                (@Iterate_Decide_Comp'_Pre _ Remaining Visited P Q').
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - f_equiv.
      + unfold refine; intros;  computes_to_inv; subst;
      computes_to_econstructor; destruct v; simpl in *; eauto.
      + unfold pointwise_relation; intros b; destruct b; simpl.
        apply IHRemaining; eauto.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        reflexivity.
  Qed.

  (* Consequences of ith_replace_BoundIndex_neq and ith_replace_BoundIndex_eq on updates *)

  Lemma refine_SatisfiesAttributeConstraints_self
  : forall qsSchema
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides b (SatisfiesAttributeConstraints Ridx tup )}
             match (attrConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr => {b | decides b (Constr tup) }
               | None => ret true
             end.
  Proof.
    unfold SatisfiesAttributeConstraints.
    intros; destruct (attrConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
  Qed.

  Lemma refine_SatisfiesTupleConstraints_self
  : forall qsSchema
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup tup' : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides b (SatisfiesTupleConstraints Ridx tup tup')}
             match (tupleConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr => {b | decides b (Constr tup tup') }
               | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; destruct (tupleConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
  Qed.

  Lemma refine_SatisfiesTupleConstraints
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides
                    b
                    (forall tup',
                       GetUnConstrRelation qs Ridx tup'
                       -> SatisfiesTupleConstraints
                            Ridx
                            tup
                            (indexedElement tup'))}
             match (tupleConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr =>
                 {b | decides b (forall tup',
                                   GetUnConstrRelation qs Ridx tup'
                                   -> Constr tup (indexedElement tup'))}
               | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; destruct (tupleConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesTupleConstraints'
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides b
                          (forall tup',
                             GetUnConstrRelation qs Ridx tup'
                             -> SatisfiesTupleConstraints Ridx (indexedElement tup') tup)}
             match (tupleConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr =>
                 {b | decides b (forall tup',
                                   GetUnConstrRelation qs Ridx tup'
                                   -> Constr (indexedElement tup') tup)}
               | None => ret true
             end.
  Proof.
    unfold SatisfiesTupleConstraints.
    intros; destruct (tupleConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesCrossConstraints
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine
        (@Iterate_Decide_Comp _
                              (fun Ridx' =>
                                 SatisfiesCrossRelationConstraints
                                   Ridx Ridx' tup
                                   (GetUnConstrRelation qs Ridx')))
        (@Iterate_Decide_Comp_opt' _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end)) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp_equiv
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P P' : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx -> P' idx) ->
      (forall idx, ~ P idx -> ~ P' idx) ->
      refine (@Iterate_Decide_Comp' _ Remaining Visited P')
             (@Iterate_Decide_Comp' _ Remaining Visited P).
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - f_equiv.
      + unfold refine; intros;  computes_to_inv; subst;
        computes_to_econstructor; destruct v; simpl in *; eauto.
      + unfold pointwise_relation; intros b; destruct b; simpl.
        apply IHRemaining.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        reflexivity.
  Qed.

  Lemma tupleAgree_refl :
  forall (h : Heading)
         (tup : @Tuple h)
         (attrlist : list (Attributes h)),
    tupleAgree tup tup attrlist.
  Proof.
    unfold tupleAgree; auto.
  Qed.

  Lemma refine_tupleAgree_refl_True :
    forall (h : Heading)
           (tup : @Tuple h)
           (attrlist attrlist' : list (Attributes h)),
      refine {b |
              decides b (tupleAgree tup tup attrlist'
                         -> tupleAgree tup tup attrlist)}
             (ret true).
  Proof.
    unfold refine; intros;  computes_to_inv.
    subst; computes_to_econstructor; simpl; auto using tupleAgree_refl.
  Qed.

  Lemma refine_SatisfiesCrossConstraints_Pre (Q : Prop)
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine
        (@Iterate_Decide_Comp_Pre _
                              (fun Ridx' =>
                                 SatisfiesCrossRelationConstraints
                                   Ridx Ridx' tup
                                   (GetUnConstrRelation qs Ridx')) Q)
        (@Iterate_Decide_Comp_opt'_Pre _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end) Q) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp_Pre.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.

  Lemma DeletePrimaryKeysOK {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           DeletedTuples
           attrlist1 attrlist2,
      refine {b | (forall tup tup',
                     elementIndex tup <> elementIndex tup'
                     -> GetUnConstrRelation qs Ridx tup
                     -> GetUnConstrRelation qs Ridx tup'
                     -> (FunctionalDependency_P attrlist1 attrlist2 (indexedElement tup) (indexedElement tup')))
                  -> decides b (Mutate.MutationPreservesTupleConstraints
                                  (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)
                                  (FunctionalDependency_P attrlist1 attrlist2)
                               )}
             (ret true).
  Proof.
    unfold Mutate.MutationPreservesTupleConstraints, FunctionalDependency_P;
    intros * v Comp_v;  computes_to_inv; subst.
    computes_to_constructor; simpl.
    intros.
    unfold EnsembleDelete in *; destruct H1; destruct H2; eauto.
  Qed.

  Local Transparent Count.

  Lemma refine_Where' {A B} :
    forall (P : Ensemble A)
           (P_dec : DecideableEnsemble P)
           (bod : Comp (list B)),
    forall a,
      refine
             (if (dec a) then
                bod
              else
                (ret []))
             (Where (P a) bod)%QuerySpec.
  Proof.
    unfold refine, Query_Where; intros.
     computes_to_inv; intuition.
    caseEq (dec a).
    apply dec_decides_P in H; eauto.
    rewrite H1; eauto.
    unfold not; intros H'; apply dec_decides_P in H'; congruence.
  Qed.

  Lemma In_UnConstrQuery_In {qsSchema} {A}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx bod results,
      UnConstrQuery_In qs Ridx bod ↝ results
      -> forall (a : A), List.In a results ->
                         exists (tup' : IndexedTuple) results',
                           Ensembles.In _ (GetUnConstrRelation qs Ridx) tup'
                           /\ bod (indexedElement tup') ↝ results'
                           /\ List.In a results'.
  Proof.
    unfold UnConstrQuery_In, QueryResultComp; intros;
     computes_to_inv.
    unfold UnIndexedEnsembleListEquivalence in *; destruct_ex; intuition; subst.
    rewrite map_map in H'.
    remember (GetUnConstrRelation qs Ridx); clear Hequ;
    revert u a results H0 H' H H3;
    induction x; simpl in *; intros;
     computes_to_inv; subst.
    - simpl in H0; intuition.
    - apply in_app_or in H0; intuition.
      exists a v; intuition; try eapply H; eauto.
      inversion H3; subst.
      destruct (IHx (fun tup => tup <> a /\ u tup) _ _ H1 H''); eauto.
      unfold Ensembles.In; intros; intuition; subst; eauto.
      eapply H in H6; intuition.
      apply H4; apply in_map; auto.
      apply H; intuition.
      destruct_ex; intuition.
      eexists x0, x1; intuition.
      apply H2.
  Qed.

  Lemma In_UnConstrQuery_In' {qsSchema} {A}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx
           (bod : Tuple -> Comp (list A))
           results
           (a : A) (tup' : IndexedTuple),
      Ensembles.In _ (GetUnConstrRelation qs Ridx) tup'
      -> (forall results', bod (indexedElement tup') ↝ results'
                           -> List.In a results')
      -> UnConstrQuery_In qs Ridx bod ↝ results
      -> List.In a results.
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, Ensembles.In; intros.
     computes_to_inv.
    unfold UnIndexedEnsembleListEquivalence in *; destruct_ex; intuition; subst.
    rewrite map_map in H1'.
    remember (GetUnConstrRelation qs Ridx); clear Hequ;
    revert u a results H H0 H1 H1' H4;
    induction x; simpl in *; intros;
     computes_to_inv; subst.
    - simpl in *; intuition; eapply H1; eauto.
    - apply H1 in H; intuition; subst; apply in_or_app; eauto.
    right; inversion H4; subst.
    eapply (IHx (fun tup => tup <> a /\ u tup)); eauto.
    intuition; subst; eauto.
    apply H5; eauto using in_map.
    apply H1; eauto.
    unfold Ensembles.In; intuition; intros; eauto.
    rewrite H1 in H7; intuition.
    subst; eauto using in_map.
    apply H1; eauto.
  Qed.

  Lemma DeleteForeignKeysCheck {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx Ridx' : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (DeletedTuples : Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (Delete_dec : DecideableEnsemble DeletedTuples)
           (attr : Attributes (schemaHeading (QSGetNRelSchema _ Ridx)))
           (attr' : Attributes (schemaHeading (QSGetNRelSchema _ Ridx')))
           (tupmap : Domain (schemaHeading (QSGetNRelSchema _ Ridx)) attr
                     -> Domain (schemaHeading (QSGetNRelSchema _ Ridx')) attr')
           (AgreeDelete : forall tup tup',
                            tupleAgree tup tup' [attr] ->
                            DeletedTuples tup ->
                            DeletedTuples tup')
           (attr_eq_dec : Query_eq (Domain (schemaHeading (QSGetNRelSchema _ Ridx)) attr))
           (P : Prop)
           (ForeignKey_P_P :
              P -> (forall tup' : IndexedTuple,
                        GetUnConstrRelation qs Ridx' tup' ->
                        ForeignKey_P attr' attr tupmap (indexedElement tup')
                                     (GetUnConstrRelation qs Ridx)))
           (tup_map_inj : forall a a', tupmap a = tupmap a' -> a = a'),
      refine {b' |
              P ->
               decides b'
                       (MutationPreservesCrossConstraints
                          (GetUnConstrRelation qs Ridx')
                          (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)
                          (ForeignKey_P attr' attr tupmap))}
             (x <- Count (For (UnConstrQuery_In
                                 qs Ridx'
                                 (fun tup' =>
                                    UnConstrQuery_In
                                      qs Ridx
                                      (fun tup =>
                                         Where (DeletedTuples tup)
                                         Where (tupmap (tup attr) = tup' attr')
                                         Return ()))));
              ret (match x with
                       0  => true
                     | S _ => false
                   end)).
  Proof.
    simpl; unfold ForeignKey_P; intros.
    intros v Comp_v.
    computes_to_inv; destruct_ex; split_and.
    unfold Count in *;  computes_to_inv.
    destruct v0; simpl in *; subst;  computes_to_inv; subst;
    computes_to_constructor; simpl; unfold not;
    unfold MutationPreservesCrossConstraints; intros.
    - destruct (ForeignKey_P_P H _ H0) as [tup2 [In_tup2 Agree_tup2]].
      eexists; intuition eauto.
      unfold EnsembleDelete; constructor; unfold In; intros; eauto.
      unfold Complement, Ensembles.In, not; intros.
      unfold Query_For in *;  computes_to_inv.
      rewrite Permutation_nil in Comp_v; symmetry in Comp_v'0; eauto.
      apply (fun x => In_UnConstrQuery_In' _ _ _ _ () _ H0 x Comp_v).
      intros results' H3;
        apply (fun x => In_UnConstrQuery_In' _ _ _ _ () _ In_tup2 x H3).
      intros results'0 H5.
      unfold Query_Where in H5; computes_to_inv;
      simpl in *; intuition.
      computes_to_inv; split_and.
      rewrite Agree_tup2 in H4; pose proof (H4 (refl_equal _)) as H';
      computes_to_inv; simpl in *; subst; simpl; eauto.
      apply Return_inv in H'; subst; simpl; intuition.
      rewrite Comp_v'; destruct v1; try discriminate; reflexivity.
    - unfold Query_For in *;  computes_to_inv.
      eapply In_UnConstrQuery_In with (a := tt) in Comp_v; destruct_ex;
      intuition.
      pose proof (H3 _ H2); pose proof (H0 _ H2); destruct_ex;
      intuition.
      eapply In_UnConstrQuery_In with (a := tt) in H1; destruct_ex;
      intuition.
      unfold EnsembleDelete in *; inversion H5; subst;
      unfold Ensembles.In, Complement, In in *.
      unfold Query_Where in H1; computes_to_inv;  intuition.
      case_eq (@dec _ _ Delete_dec (indexedElement x3)); intros.
      + apply Delete_dec in H1; pose proof (H13 H1) as H'.
        computes_to_inv; split_and.
        unfold indexedTuple in *.
        destruct (A_eq_dec (indexedElement x3 attr) (indexedElement x1 attr)).
        * rewrite e, H9 in *; subst;
          pose proof (H15 (refl_equal _)) as e'; computes_to_inv; simpl in *; subst.
          apply H12; eapply AgreeDelete; eauto.
          unfold tupleAgree; simpl; intros attr'' In_attr''; destruct In_attr'';
          [rewrite H17 in *; eauto | intuition ].
        * rewrite H16 in H11 by (rewrite H9; eauto); simpl in *; eauto.
      + rewrite H14 in H11; simpl in *; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
      + eapply Permutation_in; symmetry in Comp_v'; simpl; eauto.
        destruct v1; simpl in *;
        [ discriminate | destruct u; eauto].
  Qed.

  Lemma InsertForeignKeysCheck {qsSchema}
  : forall
      (qs : UnConstrQueryStructure qsSchema)
      (Ridx Ridx' : @BoundedString (map relName (qschemaSchemas qsSchema)))
      (attr : Attributes (schemaHeading (QSGetNRelSchema _ Ridx)))
      (attr' : Attributes (schemaHeading (QSGetNRelSchema _ Ridx')))
      (tupmap : Domain (schemaHeading (QSGetNRelSchema _ Ridx')) attr'
                -> Domain (schemaHeading (QSGetNRelSchema _ Ridx)) attr)
      tup
      (ForeignKey_P_P :
         (forall tup' : IndexedTuple,
            GetUnConstrRelation qs Ridx tup' ->
            ForeignKey_P attr attr' tupmap (indexedElement tup')
                         (GetUnConstrRelation qs Ridx'))),
      Ridx <> Ridx'
      -> refine {b' |
                 decides b'
                         (forall tup',
                            (GetUnConstrRelation qs Ridx) tup' ->
                            ForeignKey_P attr attr' tupmap
                                         (indexedElement tup')
                                         (EnsembleInsert tup (GetUnConstrRelation qs Ridx')))}
                (ret true).
  Proof.
    intros; apply refine_pick_val; simpl; intros.
    unfold ForeignKey_P in *.
    destruct (ForeignKey_P_P _ H0) as [tup'' [In_tup'' ?]];
      exists tup''; unfold EnsembleInsert; intuition.
  Qed.

End ConstraintCheckRefinements.

Lemma In_flatten_CompList {A} :
  forall (P : Ensemble A)
         (P_dec : forall a, P a \/ ~ P a)
         (il : list (@IndexedElement A))
         (l : list A)
         (a : A),
    In a l
    -> flatten_CompList
         (map
            (fun x1 : IndexedElement =>
               Where (P (indexedElement x1))
                     Return (indexedElement x1) ) il) ↝ l
    -> exists a', In a' il /\ indexedElement a' = a.
Proof.
  induction il; simpl; intros;  computes_to_inv; subst; simpl in *; intuition.
  apply in_app_or in H; intuition.
  unfold Query_Where in H0; computes_to_inv; intuition.
  destruct (P_dec (indexedElement a)).
  apply H in H0; unfold Query_Return in *; computes_to_inv; subst;
  simpl in H; exists a; simpl in H1; intuition; eauto.
  apply H2 in H0; subst; simpl in *; contradiction.
  destruct (IHil _ _ H1 H0') as [a' [In_a' a'_eq]]; exists a'; split; eauto.
Qed.

Lemma For_computes_to_In :
  forall {heading} P,
    (forall a, P a \/ ~ P a) ->
    forall seq ens,
      computes_to (For (QueryResultComp (heading := heading) ens
                                        (fun tup => Where (P tup) Return tup))) seq ->
      forall x,
        List.In x seq -> (P x /\ (exists x0, ens x0 /\ indexedTuple x0 = x)).
Proof.
  unfold refine, decides;
  unfold Query_For, QueryResultComp; intros * excl;
  induction seq as [ | head seq' IH ]; intros.

  exfalso; intuition.

  computes_to_inv.

  pose proof (permutation_cons_in H') as in_x0.
  apply in_split in in_x0.
  destruct in_x0 as [ x0_before [ x0_after ? ] ]; subst.
  symmetry in H'. apply Permutation_cons_app_inv in H'.

  unfold UnIndexedEnsembleListEquivalence in H; destruct_ex; intuition; subst.

  rewrite map_map in H'0.
  destruct (flatten_CompList_app_cons_inv _ excl _ _ _ _ H'0) as [ x1_before [ x1_middle [ head' [ x1_after (_eq & in_orig & before & middle & after) ] ] ] ]; subst.

  unfold boxed_option in middle; simpl in middle.
  eapply Bind_inv in middle.
  destruct middle as [head'' (middle1 & middle2)].
  apply Pick_inv in middle1.
  apply Bind_inv in middle2.
  destruct middle1 as ( spec1 & spec2 ).
  destruct middle2 as [ nil' (ret_nil & ret_cons) ].
  apply Return_inv in ret_nil; subst.
  rewrite app_nil_r in *; subst.
  apply Return_inv in ret_cons; subst.



  rewrite singleton_neq_nil in spec2.
  destruct (excl (indexedTuple head')) as [ H'' | H'' ]; try solve [exfalso; intuition].
  specialize (spec1 H'').

  apply Return_inv in spec1.
  injection spec1; intros; subst.

  destruct H0.

  - subst x; eauto.
  - pose proof (flatten_CompList_app _ _ _ _ before after) as flatten_app.
    eapply IH; try assumption.
    computes_to_econstructor; [ | computes_to_constructor; symmetry; eassumption ].
    computes_to_econstructor.
    pose proof (EnsembleListEquivalence_slice x1_before x1_middle x1_after).
    instantiate (2 := (fun x0 : IndexedTuple => ens x0 /\ ~ In x0 x1_middle)).
    eapply PickComputes with (a := map indexedElement (x1_before ++ x1_after)).
    econstructor; split; eauto; intuition.
    destruct (H1 ens).
    unfold EnsembleListEquivalence; split; eauto using NoDup_IndexedElement.
    eapply H5; eauto.
    unfold Ensembles.In; split.
    eapply H; apply in_app_or in H2; intuition.
    intros; apply NoDup_IndexedElement in H3; eapply NoDup_app_inv'; eauto using in_app_or.
    repeat rewrite map_app in *; eauto using NoDup_slice.
    unfold boxed_option in *.
    rewrite !map_app, !map_map.
    apply flatten_app.

  - rewrite map_map in H'0.
    destruct (In_flatten_CompList P excl x0 (x0_before ++ head :: x0_after) x) as [x1 [In_x1 x1_eq]];
      eauto.
    eapply Permutation_in with (l := head :: (x0_before ++ x0_after)).
    eapply Permutation_middle.
    simpl in *; intuition; right; eauto using Permutation_in.
    exists x1; split; eauto.
    apply H; eauto.
Qed.

Lemma UnIndexedEnsembleListEquivalence_eqv {A}
: forall ens l,
    @UnIndexedEnsembleListEquivalence A ens l ->
    exists l',
      EnsembleListEquivalence ens l' /\ l = map indexedElement l'.
Proof.
  unfold UnIndexedEnsembleListEquivalence, EnsembleListEquivalence; intros.
  destruct_ex; intuition.
  exists x; intuition; eauto using NoDup_IndexedElement.
Qed.

Lemma For_computes_to_nil :
  forall {heading} P,
  forall ens,
    computes_to (For (QueryResultComp (heading := heading) ens
                                      (fun tup => Where (P tup) Return tup))) [] ->
    forall x,
      ens x -> ~ (P (indexedTuple x)).
Proof.
  unfold refine, decides, Count, Query_For, QueryResultComp; intros **.
  computes_to_inv.
  symmetry in H'; apply Permutation_nil in H'; subst.
  apply UnIndexedEnsembleListEquivalence_eqv in H; destruct_ex; intuition; subst.

  apply H2 in H0.
  apply in_split in H0.
  destruct H0 as [ x1_before [ x1_after _eq ] ]; subst.

  rewrite map_map in H'0.
  eapply flatten_CompList_nil; unfold boxed_option; eauto; intuition.
Qed.

Lemma decidable_excl :
  forall {A : Type} (P : Ensemble A) (P_dec : DecideableEnsemble P),
    (forall (a: A), P a \/ ~ P a).
Proof.
  intros ** a.
  destruct (dec a) eqn:eqdec;
    [ rewrite dec_decides_P in eqdec | rewrite Decides_false in eqdec ]; intuition.
Qed.

Lemma refine_constraint_check_into_query' :
  forall {schm tbl} (c : UnConstrQueryStructure schm) P' P
         (P_dec : DecideableEnsemble P),
    Same_set _ (fun tup => P (indexedElement tup)) P'
    -> refine
         (Pick (fun (b : bool) =>
                  decides b
                          (exists tup2: @IndexedTuple _,
                             (GetUnConstrRelation c tbl tup2 /\ P' tup2))))
         (Bind
            (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return tup))))
            (fun count => ret (negb (beq_nat count 0)))).
Proof.
  Local Transparent Count.
  unfold refine, Count, UnConstrQuery_In;
    intros * excl * P_iff_P' pick_comp ** .
   computes_to_inv; subst.

  computes_to_constructor.

  destruct (Datatypes.length v0) eqn:eq_length;
    destruct v0 as [ | head tail ]; simpl in *; try discriminate; simpl.

  pose proof (For_computes_to_nil _ (GetUnConstrRelation c tbl) H).
  rewrite not_exists_forall; intro a; rewrite not_and_implication; intros.
  unfold not; intros; eapply H0; eauto; apply P_iff_P'; eauto.

  apply For_computes_to_In with (x := head) in H; try solve [intuition].
  destruct H as ( p & [ x0 ( in_ens & _eq ) ] ); subst.
  eexists; split; eauto; apply P_iff_P'; eauto.

  apply decidable_excl; assumption.
Qed.

    Corollary refine_constraint_check_into_query :
    forall {schm tbl} P (c : UnConstrQueryStructure schm)
           (P_dec : DecideableEnsemble P),
        refine
          (Pick (fun (b : bool) =>
                   decides b
                           (exists tup2: @IndexedTuple _,
                              (GetUnConstrRelation c tbl tup2 /\ P (indexedTuple tup2)))))
          (Bind
             (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return tup))))
             (fun count => ret (negb (beq_nat count 0)))).
    Proof.

      intros.
      setoid_rewrite refine_constraint_check_into_query'; eauto.
      reflexivity.
      unfold Same_set, Included; intuition.
    Qed.

Definition refine_foreign_key_check_into_query {schm tbl} :=
  @refine_constraint_check_into_query schm tbl.

Lemma refine_functional_dependency_check_into_query :
  forall {schm : QueryStructureSchema} {tbl} ref args1 args2 (c : UnConstrQueryStructure schm),
    DecideableEnsemble (fun x : Tuple => tupleAgree_computational ref x args1 /\
                                         ~ tupleAgree_computational ref x args2) ->
      ((forall tup' : IndexedTuple,
          GetUnConstrRelation c tbl tup'
          -> FunctionalDependency_P args2 args1 ref (indexedElement tup'))
       <-> (forall tup' : IndexedTuple,
          ~ (GetUnConstrRelation c tbl tup'
             /\ tupleAgree ref (indexedElement tup') args1
             /\ ~ tupleAgree ref (indexedElement tup') args2))) ->
      refine
        (Pick (fun (b : bool) =>
                 decides b
                         (forall tup' : IndexedTuple,
                            GetUnConstrRelation c tbl tup' ->
                            FunctionalDependency_P args2 args1 ref (indexedElement tup'))))
        (Bind (Count
                 For (UnConstrQuery_In c tbl
                                       (fun tup : Tuple =>
                                          Where (tupleAgree_computational ref tup args1 /\
                                                 ~ tupleAgree_computational ref tup args2)
                                                Return tup)))
              (fun count => ret (beq_nat count 0))).
Proof.
  intros * is_dec ** .

  setoid_replace (forall tup', GetUnConstrRelation c tbl tup' ->
                               tupleAgree ref (indexedElement tup') args1
                               -> tupleAgree ref (indexedElement tup') args2)
  with           (forall tup', ~ (GetUnConstrRelation c tbl tup' /\
                                  tupleAgree ref (indexedElement tup') args1 /\
                                  ~ tupleAgree ref (indexedElement tup') args2)); eauto.

  setoid_rewrite refine_decide_negation.
  setoid_rewrite tupleAgree_equivalence.
  setoid_rewrite (@refine_constraint_check_into_query _ _
                    (fun (x: Tuple ) => tupleAgree_computational ref x args1 /\
                                        ~ tupleAgree_computational ref x args2)); try assumption.

  Opaque Query_For Count.
  simplify with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.

Lemma refine_functional_dependency_check_into_query' :
  forall {schm : QueryStructureSchema} {tbl} ref args1 args2 (c : UnConstrQueryStructure schm),
    DecideableEnsemble (fun x : Tuple => tupleAgree_computational x ref args1 /\
                                         ~ tupleAgree_computational x ref args2) ->
      ((forall tup' : IndexedTuple,
          GetUnConstrRelation c tbl tup'
          -> FunctionalDependency_P args2 args1 (indexedElement tup') ref)
       <-> (forall tup' : IndexedTuple,
          ~ (GetUnConstrRelation c tbl tup'
             /\ tupleAgree (indexedElement tup') ref args1
             /\ ~ tupleAgree (indexedElement tup') ref args2))) ->
      refine
        (Pick (fun (b : bool) =>
                 decides b
                         (forall tup' : IndexedTuple,
                            GetUnConstrRelation c tbl tup' ->
                            FunctionalDependency_P args2 args1 (indexedElement tup') ref)))
        (Bind (Count
                 For (UnConstrQuery_In c tbl
                                       (fun tup : Tuple =>
                                          Where (tupleAgree_computational tup ref args1 /\
                                                 ~ tupleAgree_computational tup ref args2)
                                                Return tup)))
              (fun count => ret (beq_nat count 0))).
Proof.
  intros * is_dec ** .

  setoid_replace (forall tup', GetUnConstrRelation c tbl tup' ->
                               tupleAgree (indexedElement tup') ref args1
                               -> tupleAgree (indexedElement tup') ref args2)
  with           (forall tup', ~ (GetUnConstrRelation c tbl tup' /\
                                  tupleAgree (indexedElement tup') ref args1 /\
                                  ~ tupleAgree (indexedElement tup') ref args2)); eauto.

  setoid_rewrite refine_decide_negation.
  setoid_rewrite tupleAgree_equivalence.
  setoid_rewrite (@refine_constraint_check_into_query _ _
                    (fun (x: Tuple ) => tupleAgree_computational x ref args1 /\
                                        ~ tupleAgree_computational x ref args2)); try assumption.

  Opaque Query_For Count.
  simplify with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.


Theorem FunctionalDependency_symmetry
: forall A H (f : _ -> _ -> Comp A) (P : _ -> Prop) attrlist1 attrlist2 n,
    refine (x1 <- {b | decides b
                               (forall tup' : @IndexedTuple H,
                                  P tup'
                                  -> FunctionalDependency_P attrlist1 attrlist2 n (indexedElement tup'))};
            x2 <- {b | decides b (forall tup' : @IndexedTuple H,
                                    P tup'
                                    -> FunctionalDependency_P attrlist1 attrlist2 (indexedElement tup') n)};
            f x1 x2)
           (x1 <- {b | decides b (forall tup' : @IndexedTuple H,
                                    P tup'
                                    -> FunctionalDependency_P attrlist1 attrlist2 n (indexedElement tup'))};
            f x1 x1).
Proof.
  unfold refine, FunctionalDependency_P; intros.
  computes_to_inv; firstorder.
  computes_to_inv; firstorder.
  repeat (computes_to_econstructor; eauto).
  destruct v0; simpl in *; unfold tupleAgree in *; intros; eauto.
  erewrite H0; eauto; intros; rewrite H2; eauto.
  unfold not; intros; eapply H0; intros.
  rewrite H1; eauto; intros; rewrite H3; eauto.
Qed.

Lemma if_duplicate_cond_eq {A}
: forall (i : bool) (t e : A),
    (if i then (if i then t else e) else e) = if i then t else e.
Proof.
  destruct i; reflexivity.
Qed.

Global Instance nil_List_Query_eq :
  List_Query_eq [] :=
  {| As_Query_eq := inil _ |}.

Global Instance cons_List_Query_eq
         {A : Type}
         {As : list Type}
         {A_Query_eq : Query_eq A}
         {As_Query_eq' : List_Query_eq As}
:
  List_Query_eq (A :: As) :=
  {| As_Query_eq := icons _ A_Query_eq As_Query_eq |}.
