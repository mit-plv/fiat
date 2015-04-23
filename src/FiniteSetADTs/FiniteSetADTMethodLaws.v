(* Definition of the finite set spec *)
Require Import Coq.Strings.String
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Lists.List
  Coq.Sorting.Permutation
  Fiat.ADT
  Fiat.ADT.ComputationalADT
  Fiat.ADTRefinement.Core
  Fiat.ADTNotation
  Fiat.ADTRefinement.GeneralRefinements
  Fiat.Common.Ensembles
  Fiat.FiniteSetADTs.FiniteSetADT
  Fiat.Common.Ensembles.Notations
  Fiat.Common.Ensembles.Equivalence.

Set Implicit Arguments.

Local Open Scope Ensemble_scope.

Section method_laws.
  Variable FiniteSetImpl : FullySharpened FiniteSetSpec.

  Local Infix "≃" := (AbsR (projT2 FiniteSetImpl)).
  Definition to_ensemble fs : Ensemble W :=
    fun x => exists S0, S0 ≃ fs /\ x ∈ S0.

  Local Ltac handle_methods :=
    idtac;
    let lem := match goal with
                 | [ |- context[(CallMethod (projT1 ?impl) ?idx) ?rep ?arg] ]
                   => constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg)
                 | [ H : context[(CallMethod (projT1 ?impl) ?idx) ?rep ?arg] |- _ ]
                   => constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg)
               end in
    let H' := fresh in
    first [ pose proof (fun rep' H => lem rep' H _ (ReturnComputes _)) as H'
          | pose proof (lem _ (ReturnComputes _)) as H' ];
      simpl in H'.

  Local Ltac handle_constructors :=
    idtac;
    let lem := match goal with
                 | [ |- context[(CallConstructor (projT1 ?impl) ?idx) ?arg] ]
                   => constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg)
                 | [ H : context[(CallConstructor (projT1 ?impl) ?idx) ?arg] |- _ ]
                   => constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg)
               end in
    let H' := fresh in
    first [ pose proof (fun rep' H => lem rep' H _ (ReturnComputes _)) as H'
          | pose proof (lem _ (ReturnComputes _)) as H' ];
      simpl in H'.

  Local Ltac t_pre_step :=
    idtac;
    match goal with
      | _ => split
      | _ => intro
      | _ => progress unfold Ensembles.In, Included, to_ensemble in *
      | _ => progress destruct_head_hnf Ensembles.Empty_set
      | _ => progress subst
      | _ => progress inversion_by computes_to_inv
      | _ => progress simpl in *
      | _ => progress split_iff
      | _ => progress destruct_head bool
      | _ => progress destruct_head ex
      | _ => progress simplify_hyps
      | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
      | [ H : (_, _) = ?x |- _ ] => destruct x
      | _ => assumption
      | [ H : ?f ?A ?B, H' : forall a, ?f a ?b -> _ |- _ ] => specialize (H' _ H)
      | _ => solve [ eauto with nocore ]
      | _ => solve [ repeat esplit; eassumption ]
      | [ |- computes_to (ret ?x) ?y ]
        => let H := fresh in
           assert (H : x = y);
             [
             | rewrite H; constructor ]
      | [ |- computes_to (Return _) _ ] => constructor
      | [ |- computes_to (Bind _ _) _ ] => refine (BindComputes _ _ _)
      | [ |- computes_to (Pick _) _ ] => constructor
      | [ |- from_nat _ = from_nat _ ] => apply f_equal
    end.

  Lemma FiniteSet_AbsR_Same_set fs (S0 S1 : Ensemble W) (H0 : S0 ≃ fs) (H1 : S1 ≃ fs)
  : S0 ≅ S1.
  Proof.
    lazy; split; intros;
    match goal with
      | [ H : ?S' ≃ ?fs, H' : ?S'' ≃ ?fs |- ?S' ?x ]
        => pose proof (let f := ADTRefinementPreservesMethods
                                  (projT2 FiniteSetImpl) {| bindex := "In"%string |}
                                  S' _ x H in
                       f _ (ReturnComputes _));
          pose proof (let f := ADTRefinementPreservesMethods
                                 (projT2 FiniteSetImpl) {| bindex := "In"%string |}
                                 S'' _ x H' in
                      f _ (ReturnComputes _));
          simpl in *
    end;
    repeat t_pre_step.
  Qed.

  Local Ltac t_step :=
    idtac;
    match goal with
      | _ => progress t_pre_step
      | [ H0 : ?S0 ≃ ?fs, H1 : ?S1 ≃ ?fs |- _ ] =>
        match goal with
          | [ H'' : S0 ≅ S1 |- _ ] => fail 1
          | [ H'' : S1 ≅ S0 |- _ ] => fail 1
          | _ => let H := fresh in
                 pose proof (@FiniteSet_AbsR_Same_set fs S0 S1 H0 H1) as H;
                   pose proof (proj1 H);
                   pose proof (proj2 H)
        end
    end.

  Local Ltac t := repeat t_step.

  Section AbsR.
    Lemma AbsR_ToEnsemble_Empty
    : ∅ ≃ CallConstructor (projT1 FiniteSetImpl) sEmpty tt.
    Proof.
      handle_constructors; t.
    Qed.

    Lemma AbsR_ToEnsemble_Add S0 fs x (H : S0 ≃ fs)
    : Ensembles.Add _ S0 x ≃ fst (CallMethod (projT1 FiniteSetImpl) sAdd fs x).
    Proof.
      handle_methods; t.
    Qed.

    Lemma AbsR_ToEnsemble_Remove S0 fs x (H : S0 ≃ fs)
    : Ensembles.Subtract _ S0 x ≃ fst (CallMethod (projT1 FiniteSetImpl) sRemove fs x).
    Proof.
      handle_methods; t.
    Qed.

    Lemma AbsR_ToEnsemble_In S0 fs x (H : S0 ≃ fs)
    : S0 ≃ fst (CallMethod (projT1 FiniteSetImpl) sIn fs x).
    Proof.
      handle_methods; t.
    Qed.

    Lemma AbsR_ToEnsemble_Size S0 fs (H : S0 ≃ fs)
    : S0 ≃ fst (CallMethod (projT1 FiniteSetImpl) sSize fs tt).
    Proof.
      handle_methods; t.
    Qed.
  End AbsR.

  Lemma Same_set_ToEnsemble_AbsR S0 fs (H : S0 ≃ fs)
  : to_ensemble fs ≅ S0.
  Proof. t. Qed.

  Lemma Same_set_ToEnsemble_Empty
  : to_ensemble (CallConstructor (projT1 FiniteSetImpl) sEmpty tt) ≅ ∅.
  Proof.
    apply Same_set_ToEnsemble_AbsR, AbsR_ToEnsemble_Empty.
  Qed.

  (** N.B. This lemma takes an [AbsR] assumption, but produces a
           [Same_set] conclusion; we need to know that the finite set
           representation we start with is valid in the first place.
           (Because of how we're representing [to_ensemble], we
           actually need something stronger, essentially that [AbsR]
           respects [Same_set].)

     B.D. Is this actually point true? We can use the [In] method to
          show that any two sets related to the same [fs] are the
          [Same_set], w/o relying on a stronger assumption. See in
          [FiniteSets]

     J.G. Yes.  I do what you say above in [FiniteSet_AbsR_Same_set]
          (potentially duplicated lemma?).  Here I need to assume the
          other direction, that if an ensemble [S0] is related to a
          finite set [fs], then any ensemble [S'] which is the
          [Same_set] as [S0] is also related to [fs]; this is the
          [forall S', S' ≅ S0 -> S' ...] bit in [H : exists S0, forall
          S', S' ≅ S0 -> S' ≃ fs]. *)

  Lemma Same_set_ToEnsemble_Add' fs S0 x (H : S0 ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sAdd fs x)) ≅ Ensembles.Add _ S0 x.
  Proof.
    apply Same_set_ToEnsemble_AbsR, AbsR_ToEnsemble_Add; assumption.
  Qed.
  Lemma Same_set_ToEnsemble_Add fs x (H : exists S0, forall S', S' ≅ S0 -> S' ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sAdd fs x)) ≅ Ensembles.Add _ (to_ensemble fs) x.
  Proof.
    destruct H as [? H].
    pose proof (H _ (reflexivity _)).
    apply Same_set_ToEnsemble_Add', H; t.
  Qed.

  Lemma Same_set_ToEnsemble_Remove' fs S0 x (H : S0 ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sRemove fs x)) ≅ Ensembles.Subtract _ S0 x.
  Proof.
    apply Same_set_ToEnsemble_AbsR, AbsR_ToEnsemble_Remove; assumption.
  Qed.
  Lemma Same_set_ToEnsemble_Remove fs x (H : exists S0, forall S', S' ≅ S0 -> S' ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sRemove fs x)) ≅ Ensembles.Subtract _ (to_ensemble fs) x.
  Proof.
    destruct H as [? H].
    pose proof (H _ (reflexivity _)).
    apply Same_set_ToEnsemble_Remove', H; t.
  Qed.

  Lemma ToEnsemble_In_iff' fs S0 x (H : S0 ≃ fs)
  : (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)) = true
    <-> x ∈ S0.
  Proof.
    handle_methods; t.
  Qed.
  Lemma ToEnsemble_In_iff fs x (H : exists S0, forall S', S' ≅ S0 -> S' ≃ fs)
  : (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)) = true
    <-> x ∈ (to_ensemble fs).
  Proof.
    destruct H as [? H].
    pose proof (H _ (reflexivity _)).
    apply ToEnsemble_In_iff', H; t.
  Qed.

  Lemma ToEnsemble_In_refineEquiv' fs S0 x (H : S0 ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)))
                { b : bool | decides b (x ∈ S0) }.
  Proof.
    setoid_rewrite <- (@ToEnsemble_In_iff' fs S0 x H).
    setoid_rewrite refineEquiv_decides_eqb.
    rewrite refineEquiv_pick_eq; reflexivity.
  Qed.
  Lemma ToEnsemble_In_refineEquiv fs x (H : exists S0, forall S', S' ≅ S0 -> S' ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)))
                { b : bool | decides b (x ∈ to_ensemble fs) }.
  Proof.
    setoid_rewrite <- (@ToEnsemble_In_iff fs x H).
    setoid_rewrite refineEquiv_decides_eqb.
    rewrite refineEquiv_pick_eq; reflexivity.
  Qed.

  Lemma ToEnsemble_Size_refineEquiv' fs S0 (H : S0 ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sSize fs tt)))
                (cardinal S0).
  Proof.
    handle_methods; unfold cardinal in *; t.
    eapply cardinal_unique; eassumption.
  Qed.
  Lemma ToEnsemble_Size_refineEquiv fs (H : exists S0, forall S', S' ≅ S0 -> S' ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sSize fs tt)))
                (cardinal (to_ensemble fs)).
  Proof.
    destruct H as [? H].
    pose proof (H _ (reflexivity _)).
    apply ToEnsemble_Size_refineEquiv', H; t.
  Qed.
End method_laws.
