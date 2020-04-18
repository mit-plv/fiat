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

  Local Unset Implicit Arguments.

  Lemma refine_Iterate_Ensemble {n}
    : forall (P : Ensemble (Fin.t n)),
      refine {b | decides b (forall idx : Fin.t n, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex n P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv';
    eauto using string_dec.
    destruct n; simpl in *; intros; intuition.
    apply H1; eauto.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Lemma refine_Iterate_Ensemble_filter
        {n}
    : forall (P : Ensemble (Fin.t n))
             (filter : Ensemble (Fin.t n))
             (filter_dec : DecideableEnsemble filter),
      refine {b | decides b (forall idx : _, filter idx -> P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex_filter
                               n P (@dec _ _ filter_dec) )}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv_filter';
    eauto using string_dec.
    destruct n; simpl in *; intros; intuition.
    unfold not; intros; apply H.
    case_eq (dec Fin.F1); try econstructor.
    eapply H0; eapply dec_decides_P; eauto.
    let f := constr:(@Iterate_Ensemble_equiv_filter''
              _  (fun n' : Fin.t n => P (Fin.FS n'))
              (fun n' : Fin.t n => filter (Fin.FS n'))
              ({| dec := (fun n' : Fin.t n => dec (Fin.FS n'));
                  dec_decides_P := (fun a => dec_decides_P (Fin.FS a))|})) in
    eapply f; eauto.
    intros;
      let f := constr:(@Iterate_Ensemble_equiv_filter''
              _
              (fun n' : Fin.t n => P (Fin.FS n'))
              (fun n' : Fin.t n => filter (Fin.FS n'))
              ({| dec := (fun n' : Fin.t n => dec (Fin.FS n'));
                  dec_decides_P := (fun a => dec_decides_P (Fin.FS a))|})) in
      eapply f; eauto.
  Qed.

  Lemma refine_decides_Equiv_Ensemble {n}
    : forall (P P' : Ensemble (Fin.t n))
             (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx, P idx)}
             {b | decides b (forall idx, P' idx)}.
  Proof.
    intros * equiv_P'_P v Comp_v.
    computes_to_inv; computes_to_constructor; destruct v; simpl in *.
    intros; eapply equiv_P'_P; eauto.
    unfold not; intros; eapply Comp_v; eapply equiv_P'_P; eauto.
  Qed.

  Corollary Iterate_Ensemble_filter_neq
            {n}
    : forall (P : Ensemble (Fin.t n))
             (Ridx : Fin.t n),
      (forall idx, idx <> Ridx -> P idx)
      <-> (@Iterate_Ensemble_BoundedIndex_filter
             n P (fun idx =>
                    if (fin_eq_dec Ridx idx)
                    then false else true)).
  Proof.
    intros.
    assert (forall a : Fin.t n,
               (if fin_eq_dec Ridx a then false else true) = true
               <-> a <> Ridx)
      as filter_dec'
        by (intros; find_if_inside; try rewrite e; intuition).
    split; intros.
    - eapply Iterate_Ensemble_equiv_filter'' with
      (filter := fun idx => idx <> Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |}); eauto.
    - eapply Iterate_Ensemble_equiv_filter' with
        (filter := fun idx => idx <> Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |});
      unfold dec; eauto using string_dec.
  Qed.

  Lemma refine_Iterate_Equiv_Ensemble {n n'}
    : forall (P : Ensemble (Fin.t n))
             (P' : Ensemble (Fin.t n'))
             (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex _ P')}.
  Proof.
    intros; setoid_rewrite refine_Iterate_Ensemble; try eassumption.
    intros v Comp_v.
    computes_to_inv; computes_to_constructor; destruct v; simpl in *.
    apply Iterate_Ensemble_equiv'';
      eauto using string_dec; simpl.
    apply equiv_P'_P; intros;
    apply Iterate_Ensemble_equiv';
    eauto using string_dec; simpl.
    unfold not; intros; eapply Comp_v.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
    intros; eapply equiv_P'_P.
    apply Iterate_Ensemble_equiv'; eauto.
  Qed.

  Fixpoint Iterate_Decide_Comp
          (Remaining : nat)
          (P : Ensemble (Fin.t Remaining))
          {struct Remaining }
    : Comp bool :=
    match Remaining return Ensemble (Fin.t (Remaining)) -> Comp bool with
    | 0 => fun P => ret true
    | S Remaining' => fun P =>
      Bind {b' | decides b' (P (@Fin.F1 (Remaining')))}%comp
           (fun b' =>
              If_Then_Else b'
                           (Iterate_Decide_Comp Remaining' (fun n => P (Fin.FS n)))
                           (ret false))
    end P.

  Lemma refine_Iterate_Decided_Ensemble'
    : forall (Remaining : nat)
             (P : Ensemble (Fin.t Remaining)),
      refine {b | decides b (Iterate_Ensemble_BoundedIndex' P)}
             (Iterate_Decide_Comp Remaining P).
  Proof.
    induction Remaining; simpl; intros.
    - computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
    - computes_to_econstructor; computes_to_inv; destruct_ex;
      split_and;  computes_to_inv; subst.
      destruct v0; simpl in *.
      { destruct v; simpl in *; intuition; intros; eauto.
        - generalize (IHRemaining (fun n => P (Fin.FS n)) _ H').
          intros;  computes_to_inv; simpl in *; eauto.
        - generalize (IHRemaining (fun n => P (Fin.FS n)) _ H').
          intros;  computes_to_inv; simpl in *; eauto.
      }
      {  computes_to_inv; subst; simpl; intuition. }
  Qed.

  Definition Iterate_Decide_Comp_BoundedIndex {n}
    : forall (P : Ensemble (Fin.t n)),
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
  Program Lemma refine_Iterate_Ensemble_Pre {n}
    : forall (P : Ensemble (Fin.t n))
             (Q : Prop),
      refine {b | Q -> decides b (forall idx, P idx)}
             {b | Q -> decides b (Iterate_Ensemble_BoundedIndex P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *; apply H in H0.
    intros; eapply Iterate_Ensemble_equiv';
    eauto using string_dec.
    destruct n; simpl in *; intros; intuition.
    unfold not; intros; apply H2; eauto.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Fixpoint Iterate_Decide_Comp_Pre
          (Remaining : nat)
          (P : Ensemble (Fin.t Remaining))
          (Q : Prop)
          {struct Remaining }
    : Comp bool :=
    match Remaining return Ensemble (Fin.t Remaining) -> Comp bool with
    | 0 => fun P => ret true
    | S Remaining' => fun P =>
      Bind {b' | Q -> decides b' (P Fin.F1)}%comp
           (fun b' =>
              If_Then_Else b'
                           (Iterate_Decide_Comp_Pre Remaining' (fun n => P (Fin.FS n)) Q)
                           (ret false))
    end P.

  Lemma refine_Iterate_Decided_Ensemble_Pre
    : forall (Remaining : nat)
             (P : Ensemble (Fin.t Remaining))
             (Q : Prop),
      refine {b | Q -> decides b (Iterate_Ensemble_BoundedIndex' P)}
             (Iterate_Decide_Comp_Pre Remaining P Q).
  Proof.
    induction Remaining; simpl; intros.
    - computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
    - computes_to_econstructor; computes_to_inv; destruct_ex;
      split_and;  computes_to_inv; subst.
      destruct v0; simpl in *.
      {  destruct v; simpl in *; intuition; intros; eauto.
         - generalize (IHRemaining _ _ _ H').
           intros;  computes_to_inv; simpl in *; eauto.
         - generalize (IHRemaining _ _ _ H').
           intros;  computes_to_inv; simpl in *; eauto.
           eapply H; eauto.
      }
      {  computes_to_inv; subst; simpl; intuition. }
  Qed.

  Definition Iterate_Decide_Comp_BoundedIndex_Pre
    : forall (Bound : nat)
             (P : Ensemble (Fin.t Bound))
             (Q : Prop),
      refine {b | Q -> decides b (forall Ridx', P Ridx')}
             (Iterate_Decide_Comp_Pre _ P Q).
  Proof.
    intros.
    setoid_rewrite refine_Iterate_Ensemble_Pre; auto using string_dec.
    setoid_rewrite refine_Iterate_Decided_Ensemble_Pre; auto using string_dec.
    reflexivity.
  Qed.

  Fixpoint Iterate_Decide_Comp_opt
          (Remaining : nat)
          (P : Fin.t Remaining -> option Prop )
          {struct Remaining }
    : Comp bool :=
    match Remaining return (Fin.t Remaining -> option Prop) -> Comp bool with
    | 0 => fun P => ret true
    | S Remaining' =>
      fun P =>
        match P Fin.F1 with
        | Some P' => b' <- {b' | decides b' P'};
            If_Then_Else b'
                         (Iterate_Decide_Comp_opt Remaining' (fun n => P (Fin.FS n)))
                         (ret false)
        | None => Iterate_Decide_Comp_opt Remaining' (fun n => P (Fin.FS n))
      end
    end%comp P .

  Lemma refine_Iterate_Decide_Comp
    : forall (Remaining : nat)
             (P : Fin.t Remaining -> option Prop),
      refine (@Iterate_Decide_Comp Remaining (fun idx => match P idx with
                                                         | Some P' => P'
                                                         | None => True
                                                         end))
             (@Iterate_Decide_Comp_opt Remaining P).
        induction Remaining; simpl; intros.
        - reflexivity.
        - destruct (P Fin.F1).
          + f_equiv; unfold pointwise_relation; intros.
            destruct a; simpl; try reflexivity.
            setoid_rewrite <- IHRemaining; f_equiv.
          + rewrite decides_True; simplify with monad laws; simpl.
            setoid_rewrite <- IHRemaining; f_equiv.
  Qed.

  Fixpoint Iterate_Decide_Comp_opt_Pre
          (Remaining : nat)
          (P : Fin.t Remaining -> option Prop)
          (Q : Prop)
          {struct Remaining }
    : Comp bool :=
    match Remaining return (Fin.t Remaining -> option Prop) -> Comp bool with
    | 0 => fun P => ret true
    | S Remaining' =>
      fun P =>
      match P Fin.F1 with
      | Some P' => b' <- {b' | Q -> decides b' P'};
          If_Then_Else b'
                       (Iterate_Decide_Comp_opt_Pre Remaining'
                                                    (fun n => P (Fin.FS n)) Q)
                       (ret false)
      | None =>
        (Iterate_Decide_Comp_opt_Pre Remaining'
                                     (fun n => P (Fin.FS n)) Q)
      end
    end%comp P.

  Lemma refine_Iterate_Decide_Comp_Pre
    : forall (Remaining : nat)
             (P : Fin.t Remaining -> option Prop)
             (Q : Prop),
      refine (@Iterate_Decide_Comp_Pre Remaining
                                        (fun idx => match P idx with
                                                    | Some P' => P'
                                                    | None => True
                                                    end) Q)
             (@Iterate_Decide_Comp_opt_Pre Remaining P Q).
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - destruct (P Fin.F1).
      + f_equiv; unfold pointwise_relation; intros.
        destruct a; simpl; try reflexivity.
        setoid_rewrite <- IHRemaining; f_equiv.
      + rewrite decides_True_Pre; simplify with monad laws; simpl.
        setoid_rewrite <- IHRemaining; f_equiv.
  Qed.

  Lemma refine_Iterate_Decide_Comp_equiv_Pre
        (Q Q' : Prop)
    : forall (Remaining : nat)
             (P P' : Ensemble (Fin.t Remaining)),
      (forall idx, P idx -> P' idx)
      -> (forall idx, ~ P idx -> ~ P' idx)
      -> (Q -> Q')
      -> refine (@Iterate_Decide_Comp_Pre Remaining P' Q)
                (@Iterate_Decide_Comp_Pre Remaining P Q').
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - f_equiv.
      + unfold refine; intros;  computes_to_inv; subst;
        computes_to_econstructor; destruct v; simpl in *; eauto.
      + unfold pointwise_relation; intros b; destruct b; simpl.
        apply IHRemaining; eauto.
        reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp_equiv
    : forall (Remaining : nat)
             (P P' : Ensemble (Fin.t Remaining)),
      (forall idx, P idx -> P' idx) ->
      (forall idx, ~ P idx -> ~ P' idx) ->
      refine (@Iterate_Decide_Comp Remaining P')
             (@Iterate_Decide_Comp Remaining P).
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - f_equiv.
      + unfold refine; intros;  computes_to_inv; subst;
        computes_to_econstructor; destruct v; simpl in *; eauto.
      + unfold pointwise_relation; intros b; destruct b; simpl; eauto.
        reflexivity.
  Qed.

End Iterate_Decide_Comp.
