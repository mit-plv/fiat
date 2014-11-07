(** * Definition of the finite set spec *)
Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List Coq.Sorting.Permutation.
Require Import ADTSynthesis.ADT ADTSynthesis.ADT.ComputationalADT ADTSynthesis.ADTRefinement.Core ADTSynthesis.ADTNotation ADTSynthesis.ADTRefinement.GeneralRefinements ADTSynthesis.Common.AdditionalEnsembleDefinitions.
Require Import ADTSynthesis.FiniteSetADTs.FiniteSetADT.
Require Import ADTSynthesis.Common.Ensembles.Notations ADTSynthesis.Common.AdditionalEnsembleLemmas.

Set Implicit Arguments.

Local Open Scope Ensemble_scope.

Section method_laws.
  Variable FiniteSetImpl : FullySharpened FiniteSetSpec.

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

  Local Ltac t_step :=
    match goal with
      | _ => split
      | _ => intro
      | _ => progress unfold Ensembles.In in *
      | _ => progress destruct_head_hnf Ensembles.Empty_set
      | _ => progress subst
      | _ => progress inversion_by computes_to_inv
      | _ => progress simpl in *
      | _ => progress split_iff
      | _ => progress destruct_head bool
      | _ => progress simplify_hyps
      | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
      | [ H : (_, _) = ?x |- _ ] => destruct x
      | _ => assumption
      | [ H : ?f ?A ?B, H' : forall a, ?f a ?b -> _ |- _ ] => specialize (H' _ H)
    end.

  Local Ltac t := repeat t_step.

  Local Notation to_ensemble fs :=
    (snd (CallMethod (projT1 FiniteSetImpl) sToEnsemble fs tt)).
  Local Infix "≃" := (AbsR (projT2 FiniteSetImpl)).

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
  End AbsR.

  Lemma Same_set_ToEnsemble_AbsR S0 fs (H : S0 ≃ fs)
  : to_ensemble fs ≅ S0.
  Proof.
    handle_methods; t.
  Qed.

  Lemma Same_set_ToEnsemble_Empty
  : to_ensemble (CallConstructor (projT1 FiniteSetImpl) sEmpty tt) ≅ ∅.
  Proof.
    apply Same_set_ToEnsemble_AbsR, AbsR_ToEnsemble_Empty.
  Qed.

  (** N.B. This lemma takes an [AbsR] assumption, but produces a
           [Same_set] conclusion; we need to know that the finite set
           representation we start with is valid in the first
           place. *)
  Lemma Same_set_ToEnsemble_Add' fs S0 x (H : S0 ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sAdd fs x)) ≅ Ensembles.Add _ S0 x.
  Proof.
    apply Same_set_ToEnsemble_AbsR, AbsR_ToEnsemble_Add; assumption.
  Qed.
  Lemma Same_set_ToEnsemble_Add fs x (H : exists S0, S0 ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sAdd fs x)) ≅ Ensembles.Add _ (to_ensemble fs) x.
  Proof.
    apply Same_set_ToEnsemble_Add'.
    handle_methods; t.
  Qed.

  Lemma Same_set_ToEnsemble_Remove' fs S0 x (H : S0 ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sRemove fs x)) ≅ Ensembles.Subtract _ S0 x.
  Proof.
    apply Same_set_ToEnsemble_AbsR, AbsR_ToEnsemble_Remove; assumption.
  Qed.
  Lemma Same_set_ToEnsemble_Remove fs x (H : exists S0, S0 ≃ fs)
  : to_ensemble (fst (CallMethod (projT1 FiniteSetImpl) sRemove fs x)) ≅ Ensembles.Subtract _ (to_ensemble fs) x.
  Proof.
    apply Same_set_ToEnsemble_Remove'.
    handle_methods; t.
  Qed.

  Lemma ToEnsemble_In_iff' fs S0 x (H : S0 ≃ fs)
  : (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)) = true
    <-> x ∈ S0.
  Proof.
    handle_methods; t.
  Qed.
  Lemma ToEnsemble_In_iff fs x (H : exists S0, S0 ≃ fs)
  : (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)) = true
    <-> x ∈ (to_ensemble fs).
  Proof.
    apply ToEnsemble_In_iff'.
    handle_methods; t.
  Qed.

  Lemma ToEnsemble_In_refineEquiv' fs S0 x (H : S0 ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)))
                { b : bool | decides b (x ∈ S0) }.
  Proof.
    setoid_rewrite <- (@ToEnsemble_In_iff' fs S0 x H).
    setoid_rewrite refineEquiv_decides_eqb.
    rewrite refineEquiv_pick_eq; reflexivity.
  Qed.
  Lemma ToEnsemble_In_refineEquiv fs x (H : exists S0, S0 ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sIn fs x)))
                { b : bool | decides b (x ∈ to_ensemble fs) }.
  Proof.
    setoid_rewrite <- (@ToEnsemble_In_iff fs x H).
    setoid_rewrite refineEquiv_decides_eqb.
    rewrite refineEquiv_pick_eq; reflexivity.
  Qed.

  Lemma ToEnsemble_Size_iff' fs S0 (H : S0 ≃ fs) n
  : (snd (CallMethod (projT1 FiniteSetImpl) sSize fs tt)) = n
    <-> cardinal _ S0 n.
  Proof.
    handle_methods; t.
    eapply cardinal_unique; eassumption.
  Qed.
  Lemma ToEnsemble_Size_iff fs (H : exists S0, S0 ≃ fs) n
  : (snd (CallMethod (projT1 FiniteSetImpl) sSize fs tt)) = n
    <-> cardinal _ (to_ensemble fs) n.
  Proof.
    apply ToEnsemble_Size_iff'.
    handle_methods; t.
  Qed.

  Lemma ToEnsemble_Size_refineEquiv' fs S0 (H : S0 ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sSize fs tt)))
                { n : nat | cardinal _ S0 n }.
  Proof.
    setoid_rewrite <- (@ToEnsemble_Size_iff' fs S0 H).
    rewrite refineEquiv_pick_eq'; reflexivity.
  Qed.
  Lemma ToEnsemble_Size_refineEquiv fs (H : exists S0, S0 ≃ fs)
  : refineEquiv (ret (snd (CallMethod (projT1 FiniteSetImpl) sSize fs tt)))
                { n : nat | cardinal _ (to_ensemble fs) n }.
  Proof.
    apply ToEnsemble_Size_refineEquiv'.
    handle_methods; t.
  Qed.
End method_laws.
