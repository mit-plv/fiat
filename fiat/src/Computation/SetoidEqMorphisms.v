Require Import Coq.Classes.Morphisms.
Require Import Fiat.Computation.Core.

Global Instance ret_Proper_eq {A}
  : Proper (eq ==> eq) (ret (A:=A)).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance refine_Proper_eq_iff {A}
  : Proper (eq ==> eq ==> iff) (@refine A).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance refine_Proper_eq_impl {A}
  : Proper (eq ==> eq ==> Basics.impl) (@refine A) | 1.
Proof. repeat (assumption || subst || intro). Qed.
Global Instance refine_Proper_eq_flip_impl {A}
  : Proper (eq ==> eq ==> Basics.flip Basics.impl) (@refine A) | 1.
Proof. repeat (assumption || subst || intro). Qed.
