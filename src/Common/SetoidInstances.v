Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

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

Global Instance sumbool_rect_Proper {L R : Prop} {P} {R1}
: Proper (pointwise_relation L R1 ==> pointwise_relation R R1 ==> @forall_relation _ (fun _ : {L} + {R} => P) (fun _ => R1))
         (@sumbool_rect L R (fun _ => P)).
Proof.
  intros ?????? [a|a]; simpl in *; eauto.
Qed.

Global Hint Extern 0 (Proper _ (@sumbool_rect ?L ?R (fun _ => ?P))) => refine (@sumbool_rect_Proper L R P _) : typeclass_instances.


Global Instance andb_Proper
: Proper (eq ==> eq ==> eq) andb.
Proof.
  repeat ((intro; progress subst) || intros []); try reflexivity.
Qed.
Global Instance orb_Proper
: Proper (eq ==> eq ==> eq) orb.
Proof.
  repeat ((intro; progress subst) || intros []); try reflexivity.
Qed.

Global Instance map_Proper_eq {A B}
: Proper (pointwise_relation _ eq ==> eq ==> eq) (@map A B).
Proof.
  intros ?? H ? ls ?; subst.
  induction ls; trivial; simpl.
  hnf in H; rewrite H, IHls; reflexivity.
Qed.

Global Instance bool_rect_Proper {P} {R1}
: Proper (R1 ==> R1 ==> @forall_relation _ (fun _ : bool => P) (fun _ => R1))
         (@bool_rect (fun _ => P)).
Proof.
  intros ?????? [|]; simpl in *; eauto.
Qed.

Global Instance fst_eq_Proper {A B} : Proper (eq ==> eq) (@fst A B).
Proof.
  repeat intro; subst; reflexivity.
Qed.
Global Instance snd_eq_Proper {A B} : Proper (eq ==> eq) (@snd A B).
Proof.
  repeat intro; subst; reflexivity.
Qed.

Global Instance: Proper (eq ==> Basics.flip Basics.impl) is_true | 1 := _.
Global Instance: Proper (eq ==> Basics.impl) is_true | 1 := _.
Global Instance: Proper (eq ==> iff) is_true | 0 := _.
