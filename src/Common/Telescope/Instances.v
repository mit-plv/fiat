Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Classes.Morphisms.
Require Import Fiat.Common.Telescope.Core.

Module Export Telescope.
  Global Instance flattenT_eq_Reflexive {t : Telescope} {X : Type}
  : Reflexive (@flattenT_eq t X).
  Proof.
    repeat intro; induction t; simpl in *.
    { reflexivity. }
    { eauto with nocore. }
  Defined.

  Global Instance flattenT_eq_Symmetric {t : Telescope} {X : Type}
  : Symmetric (@flattenT_eq t X).
  Proof.
    repeat intro; induction t; simpl in *.
    { symmetry; assumption. }
    { eauto with nocore. }
  Defined.

  Global Instance flattenT_eq_Transitive {t : Telescope} {X : Type}
  : Transitive (@flattenT_eq t X).
  Proof.
    repeat intro; induction t; simpl in *.
    { etransitivity; eassumption. }
    { eauto with nocore. }
  Defined.

  Global Instance flatten_forall_eq_relation_Reflexive {t P}
  : Reflexive (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ reflexivity | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_Symmetric {t P}
  : Symmetric (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ symmetry; assumption | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_Transitive {t P}
  : Transitive (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ etransitivity; eassumption | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_Reflexive {t P}
  : Reflexive (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Reflexive.

  Global Instance flatten_forall_eq_Symmetric {t P}
  : Symmetric (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Symmetric.

  Global Instance flatten_forall_eq_Transitive {t P}
  : Transitive (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Transitive.

  Lemma flatten_append_forall_Proper {B P Q}
  : forall f g,
      @flatten_forall_eq B P f g
      -> @flatten_append_forall B P Q f
      -> @flatten_append_forall B P Q g.
  Proof.
    induction B; simpl in *; eauto with nocore.
    intros; subst; assumption.
  Defined.

  Global Instance flattenT_unapply_Proper {t X}
  : Proper (pointwise_relation _ eq ==> flattenT_eq)
           (@flattenT_unapply t X).
  Proof.
    repeat intro; unfold pointwise_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flattenT_apply_Proper {t X}
  : Proper (flattenT_eq ==> pointwise_relation _ eq)
           (@flattenT_apply t X).
  Proof.
    repeat intro; unfold pointwise_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_unapply_Proper {t P}
  : Proper (forall_relation (fun _ => eq) ==> flatten_forall_eq)
           (@flatten_forall_unapply t P).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_apply_Proper {t P}
  : Proper (flatten_forall_eq ==> forall_relation (fun _ => eq))
           (@flatten_forall_apply t P).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_eq_rect_Proper {t P Q H}
  : Proper (flatten_forall_eq ==> flatten_forall_eq)
           (@flatten_forall_eq_rect t P Q H).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore;
    subst; simpl; reflexivity.
  Defined.
End Telescope.
