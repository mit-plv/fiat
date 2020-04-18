Require Import Coq.omega.Omega.
Set Implicit Arguments.

Require Import Coq.Structures.OrderedType.

Module W_as_MOT <: MiniOrderedType.

  Require Import Bedrock.Memory.

  Definition t := W.

  Require Import Bedrock.Word.

  Definition eq := @eq t.

  Local Open Scope nat.

  Definition lt (x y : t) := wordToNat x < wordToNat y.

  Lemma eq_refl : forall x : t, eq x x.
    unfold eq; eauto.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    unfold eq; eauto.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    unfold eq; intuition.
    congruence.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    unfold lt; intros; omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    unfold lt; unfold eq; intuition.
    subst.
    omega.
  Qed.

  Require Import Bedrock.Platform.Cito.WordFacts.

  Definition compare : forall x y : t, Compare lt eq x y.
    unfold lt; unfold eq.
    intros.
    destruct (Compare_dec.lt_eq_lt_dec (wordToNat x) (wordToNat y)).
    destruct s.
    econstructor 1; eauto.
    econstructor 2; eauto.
    eapply wordToNat_eq_eq; eauto.
    econstructor 3; eauto.
  Defined.

End W_as_MOT.

Module W_as_OT := MOT_to_OT W_as_MOT.
Require Import Coq.Structures.OrdersAlt.
Module W_as_OT_new := Update_OT W_as_OT.
Require Import Coq.Structures.Equalities.
Module W_as_UDT := Make_UDT W_as_OT.
