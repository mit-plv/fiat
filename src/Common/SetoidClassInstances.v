Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Fiat.Common.Tactics.SplitInContext.

Set Implicit Arguments.


Section class_proper.
  Local Ltac class_proper_t := compute; repeat (intro || subst || split_and || split); eauto.
  Local Hint Extern 0 (Proper _ _) => progress class_proper_t : typeclass_instances.
  Local Notation Proper_class_iff_iff
    := (Proper (pointwise_relation _ (pointwise_relation _ iff) ==> iff)) (only parsing).
  Local Notation Proper_class_iff_flip_impl
    := (Proper (pointwise_relation _ (pointwise_relation _ iff) ==> Basics.flip Basics.impl))
         (only parsing).
  Local Notation Proper_class_iff_impl
    := (Proper (pointwise_relation _ (pointwise_relation _ iff) ==> Basics.impl)) (only parsing).
  Local Notation Proper_class_flip_impl_flip_impl
    := (Proper (pointwise_relation _ (pointwise_relation _ (Basics.flip Basics.impl)) ==> Basics.flip Basics.impl))
         (only parsing).
  Local Notation Proper_class_impl_impl
    := (Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl))
         (only parsing).
  Global Instance Reflexive_Proper_iff_iff {A}
    : Proper_class_iff_iff (@Reflexive A) | 5 := _.
  Global Instance Reflexive_Proper_iff_flip_impl {A}
    : Proper_class_iff_flip_impl (@Reflexive A) := _.
  Global Instance Reflexive_Proper_iff_impl {A}
    : Proper_class_iff_impl (@Reflexive A) := _.
  Global Instance Reflexive_Proper_flip_impl_flip_impl {A}
    : Proper_class_flip_impl_flip_impl (@Reflexive A) := _.
  Global Instance Reflexive_Proper_impl_impl {A}
    : Proper_class_impl_impl (@Reflexive A) := _.

  Global Instance Symmetric_Proper_iff_iff {A}
    : Proper_class_iff_iff (@Symmetric A) | 5 := _.
  Global Instance Symmetric_Proper_iff_flip_impl {A}
    : Proper_class_iff_flip_impl (@Symmetric A) := _.
  Global Instance Symmetric_Proper_iff_impl {A}
    : Proper_class_iff_impl (@Symmetric A) := _.

  Global Instance Transitive_Proper_iff_iff {A}
    : Proper_class_iff_iff (@Transitive A) | 5 := _.
  Global Instance Transitive_Proper_iff_flip_impl {A}
    : Proper_class_iff_flip_impl (@Transitive A) := _.
  Global Instance Transitive_Proper_iff_impl {A}
    : Proper_class_iff_impl (@Transitive A) := _.

  Global Instance Proper_Proper_eq_eq_iff {A}
    : Proper (eq ==> eq ==> iff) (@Proper A) := _.
  Global Instance Proper_Proper_eq_eq_impl {A}
    : Proper (eq ==> eq ==> Basics.flip Basics.impl) (@Proper A) := _.
  Global Instance Proper_Proper_eq_eq_flip_impl {A}
    : Proper (eq ==> eq ==> Basics.impl) (@Proper A) := _.
  Global Instance Proper_Proper_subrelation_eq_impl {A}
    : Proper (subrelation ==> eq ==> Basics.impl) (@Proper A) | 5 := _.
  Global Instance Proper_Proper_flip_subrelation_eq_flip_impl {A}
    : Proper (Basics.flip subrelation ==> eq ==> Basics.flip Basics.impl) (@Proper A) | 5 := _.
  Global Instance Proper_Proper_equiv_eq_iff {A}
    : Proper (relation_equivalence ==> eq ==> iff) (@Proper A) | 5 := _.

  Global Instance Proper_iff_eq_iff_impl : Proper (iff ==> eq ==> iff) Basics.impl | 2 := _.
End class_proper.
