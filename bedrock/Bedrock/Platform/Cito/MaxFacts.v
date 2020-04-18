Set Implicit Arguments.

Local Open Scope nat.

Require Import Coq.Arith.Le.
Require Import Coq.Arith.Max.

Ltac max_solver :=
  repeat
    match goal with
      | |- ?A <= ?A => eapply le_n
      | |- 0 <= _ => eapply le_0_n
      | |- max _ _ <= _ => eapply max_lub
      | |- ?S <= max ?A _ =>
        match A with
            context [ S ] => eapply le_trans; [ | eapply le_max_l]
        end
      | |- ?S <= max _ ?B =>
        match B with
            context [ S ] => eapply le_trans; [ .. | eapply le_max_r]
        end
    end.

Lemma both_le : forall a b a' b', a <= a' -> b <= b' -> max a b <= max a' b'.
  intros; max_solver; eauto.
  eapply le_trans; [ | eapply le_max_l]; eauto.
  eapply le_trans; [ | eapply le_max_r]; eauto.
Qed.

Local Close Scope nat.
