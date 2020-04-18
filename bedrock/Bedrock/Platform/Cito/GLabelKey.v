Set Implicit Arguments.

Require Import Coq.Structures.OrderedType.

Module GLabel_as_MOT <: MiniOrderedType.

  Require Import Bedrock.Platform.Cito.GLabel.

  Definition t := glabel.

  Definition eq := @eq t.

  Require Import Bedrock.LabelMap.

  Definition to_bl (lbl : t) : Labels.label := (fst lbl, Labels.Global (snd lbl)).

  Definition lt (x y : t) := LabelKey.lt (to_bl x) (to_bl y).

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
    unfold lt; intros.
    eapply LabelKey.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    unfold lt; unfold eq; intuition.
    subst.
    eapply LabelKey.lt_not_eq in H.
    contradict H.
    unfold LabelKey.eq.
    eauto.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
    unfold lt; unfold eq.
    intros.
    destruct (LabelKey.compare (to_bl x) (to_bl y)).
    econstructor 1; eauto.
    econstructor 2; eauto.
    unfold LabelKey.eq in *.
    unfold to_bl in *.
    destruct x; destruct y; simpl in *.
    injection e; intros; subst.
    eauto.
    econstructor 3; eauto.
  Defined.

End GLabel_as_MOT.

Module GLabel_as_OT := MOT_to_OT GLabel_as_MOT.
Require Import Coq.Structures.OrdersAlt.
Module GLabel_as_OT_new := Update_OT GLabel_as_OT.
Require Import Coq.Structures.Equalities.
Module GLabel_as_UDT := Make_UDT GLabel_as_OT.
