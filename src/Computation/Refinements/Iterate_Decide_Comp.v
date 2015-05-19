Require Import
        Coq.Lists.List
        Coq.Arith.Compare_dec
        Coq.Arith.Arith
        Coq.Bool.Bool
        Coq.Strings.String
        Coq.Sets.Ensembles
        Fiat.Common.BoolFacts
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.List.ListFacts
        Fiat.Common.LogicFacts
        Fiat.Common.DecideableEnsembles
        Fiat.Common.BoundedLookup
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation.Core
        Fiat.Computation.Monad
        Fiat.Computation.ApplyMonad
        Fiat.Computation.SetoidMorphisms
        Fiat.Computation.Refinements.General
        Fiat.Computation.Refinements.Tactics.

Section Iterate_Decide_Comp.

  (*Local Unset Implicit Arguments.

  Lemma refine_Iterate_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
    : forall (As : list A)
             (P : Ensemble (BoundedIndex As)),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex A As P)}.
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
    : forall (As : list A)
             (P : Ensemble (BoundedIndex As))
             (filter : Ensemble nat)
             (filter_dec : DecideableEnsemble filter),
      refine {b | decides b (forall idx : BoundedIndex As,
                                filter (ibound idx) -> P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex_filter
                               A As (@dec _ _ filter_dec) P )}.
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
    : forall (As : list A)
             (P : Ensemble (BoundedIndex As))
             (Ridx : BoundedIndex As),
      (forall idx : BoundedIndex As, idx <> Ridx -> P idx)
      <-> (@Iterate_Ensemble_BoundedIndex_filter
             A As (fun idx =>
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
      apply (eq_proofs_unicity_Opt_A A_eq_dec).
    }
    rewrite H.
    split; intros.
    - eapply Iterate_Ensemble_equiv_filter'' with
      (filter := fun idx => idx <> ibound Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |}); eauto.
    - eapply Iterate_Ensemble_equiv_filter'  with
      (Visited := [])
        (filter := fun idx => idx <> ibound Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |});
      unfold dec; eauto using string_dec.
      intros; destruct n; simpl in *; discriminate.
  Qed.

  Lemma refine_Iterate_Equiv_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
    : forall (As As' : list A)
             (P : Ensemble (BoundedIndex As))
             (P' : Ensemble (BoundedIndex As'))
             (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex A As' P')}.
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
    : forall (As : list A)
             (P : Ensemble (BoundedIndex As))
             (Q : Prop),
      refine {b | Q -> decides b (forall idx : BoundedIndex As, P idx)}
             {b | Q -> decides b (@Iterate_Ensemble_BoundedIndex A As P)}.
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
  Qed. *)

End Iterate_Decide_Comp.
