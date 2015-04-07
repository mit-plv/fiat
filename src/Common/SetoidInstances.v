Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Set Implicit Arguments.

Instance proper_if {A B R}
         {test : bool} {then_case else_case}
         `{Proper (A -> B) R then_case, Proper (A -> B) R else_case}
: Proper R (fun x => if test then then_case x else else_case x).
Proof.
  destruct test; trivial.
Qed.
Instance proper_idmap {A R}
: Proper (R ==> R) (fun x : A => x).
Proof. repeat intro; assumption. Qed.
Instance proper_const {A B} {R1 : relation A} {R2}
         `{Reflexive B R2} v
: Proper (R1 ==> R2) (fun _ => v).
Proof.
  repeat intro; reflexivity.
Qed.
Instance pointwise_Proper {A B} R (f : A -> B) `{forall x, Proper R (f x)}
: Proper (pointwise_relation A R) f.
Proof.
  unfold Proper in *.
  repeat intro; trivial.
Qed.
