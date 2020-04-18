Require Import Fiat.Common.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.Equality.

Section reflective_forall.
  Context {A : Type} (P : A -> bool)
          {eq_A : BoolDecR A}
          {Abl : BoolDec_bl (@eq A)}
          {Alb : BoolDec_lb (@eq A)}
          {Henum : Enumerable { x : A | is_true (P x) }}.

  Section inner.
    Context {R : Type}
            (x : A)
            (f : A -> R)
            (base : R).

    Definition forall_enumerable_by_beq : R
      := List.fold_right
           (fun y else_case
            => If beq x y Then f y Else else_case)
           base
           (List.map (@proj1_sig _ _) (enumerate { x : A | is_true (P x) })).

    Lemma forall_enumerable_by_beq_correct
    : forall_enumerable_by_beq = if P x then f x else base.
    Proof.
      unfold forall_enumerable_by_beq.
      destruct Henum as [ls Hls]; clear Henum; simpl.
      specialize (fun p => Hls (exist _ x p)); simpl in Hls.
      case_eq (P x); intro Heq; [ specialize (Hls Heq) | clear Hls ].
      { induction ls as [|k ks IHks]; simpl in *;
        destruct_head False;
        destruct Hls as [Hls|Hls];
        specialize_by assumption;
        subst;
        simpl in *.
        { rewrite lb by reflexivity; simpl; reflexivity. }
        { rewrite IHks.
          destruct (beq x (proj1_sig k)) eqn:Heq'; simpl; trivial.
          apply bl in Heq'; subst; reflexivity. } }
      { induction ls as [|k ks IHks]; simpl in *.
        { reflexivity. }
        { rewrite IHks.
          destruct (beq x (proj1_sig k)) eqn:Heq'; simpl; trivial.
          apply bl in Heq'; subst x.
          destruct k; simpl in *; congruence. } }
    Qed.

    Lemma forall_enumerable_by_beq_correct_reachable
          (H : is_true (P x))
    : forall_enumerable_by_beq = f x.
    Proof.
      rewrite forall_enumerable_by_beq_correct, H; reflexivity.
    Qed.
  End inner.

  Global Instance forall_enumerable_by_beq_Proper
         {RT x} (R : relation RT)
  : Proper
      (pointwise_relation _ R ==> R ==> R)
      (@forall_enumerable_by_beq RT x).
  Proof.
    unfold pointwise_relation.
    intros ?? H0 ?? H1.
    rewrite !forall_enumerable_by_beq_correct.
    destruct (P x); eauto with nocore.
  Qed.
End reflective_forall.
