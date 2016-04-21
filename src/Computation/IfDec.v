Require Import
        Fiat.Common
        Fiat.Computation.Decidable
        Fiat.Computation.Core
        Fiat.Computation.Refinements.General
        Fiat.Computation.Monad
        Fiat.Computation.Refinements.General.

Local Open Scope comp.
Definition IfDec_Then_Else {A} (P : Prop) (t e : Comp A) :=
  b <- { b | decides b P}; if b then t else e.
Arguments IfDec_Then_Else {A} P t e _ : simpl never.

Notation "'IfDec' P 'Then' t 'Else' e" :=
  (IfDec_Then_Else P t e) (at level 70) : comp_scope.

Lemma refine_IfDec
  : forall (P : Prop) b ResultT (t e : Comp ResultT),
    decides b P
    -> refine (IfDec P Then t Else e) (If b Then t Else e).
Proof.
  intros.
  unfold IfDec_Then_Else.
  refine pick val b; eauto.
  rewrite refineEquiv_bind_unit; reflexivity.
Qed.

Corollary refine_IfDec_true
  : forall (P : Prop) ResultT (t e : Comp ResultT),
  P -> refine (IfDec P Then t Else e) t.
Proof.
  intros; rewrite refine_IfDec with (b := true); simpl; eauto.
  reflexivity.
Qed.

Corollary refine_IfDec_false
  : forall (P : Prop) ResultT (t e : Comp ResultT),
    ~ P -> refine (IfDec P Then t Else e) e.
Proof.
  intros; rewrite refine_IfDec with (b := false); simpl; eauto.
  reflexivity.
Qed.

Lemma refine_IfDec_decides :
  forall `{Decidable P} ResultT (t e : Comp ResultT),
    refineEquiv (IfDec P Then t Else e)
                (If Decidable_witness Then t Else e).
Proof.
  split; intros.
  - apply refine_IfDec; eauto.
    case_eq (@Decidable_witness _ H); simpl.
    + intros; eapply Decidable_spec; eauto.
    + intros; eapply Decidable_complete_alt; eauto.
  - unfold IfDec_Then_Else, If_Then_Else, refine;
      intros; computes_to_inv.
    destruct v0.
    + simpl in H0; apply Decidable_spec in H0; rewrite H0; eauto.
    + simpl in H0; eapply Decidable_sound_alt in H0; rewrite H0; eauto.
Qed.

Add Parametric Morphism A P
  : (IfDec_Then_Else P)
    with signature (@refine A)
                     ==> (@refine A)
                     ==> (@refine A)
  as refine_IfDec_Then_Else.
Proof.
  intros.
  unfold IfDec_Then_Else; f_equiv; intro.
  rewrite !refine_if_If.
  rewrite H0, H.
  apply refine_PreOrder.
Qed.

(*Lemma refine_IfDec_Then_Else_ret :
  forall P ResultT (t e : ResultT),
    refine (IfDec P Then ret t Else ret e)
           (ret (IfDec P Then t Else e)%comp).
Proof.
  intros.
  unfold IfDec_Then_Else.
  setoid_rewrite refine_If_Then_Else_ret; trivial.
Qed. *)
