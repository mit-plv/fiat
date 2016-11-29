Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Set Implicit Arguments.

Local Coercion is_true : bool >-> Sortclass.

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

Global Instance: Proper (eq ==> Basics.flip Basics.impl) is_true | 10 := _.
Global Instance: Proper (eq ==> Basics.impl) is_true | 10 := _.
Global Instance: Proper (eq ==> iff) is_true | 5 := _.
Global Instance: Proper (eq ==> eq) is_true | 0 := _.

Global Instance istrue_impl_Proper
: Proper (implb ==> Basics.impl) is_true.
Proof.
  intros [] []; compute; trivial.
Qed.

Global Instance istrue_flip_impl_Proper
: Proper (Basics.flip implb ==> Basics.flip Basics.impl) is_true.
Proof.
  intros [] []; compute; trivial.
Qed.

Global Instance implb_Reflexive : Reflexive implb | 1.
Proof. intros []; reflexivity. Qed.
Global Instance implb_Transitive : Transitive implb | 1.
Proof. intros [] [] []; simpl; trivial. Qed.
Global Instance implb_Antisymmetric : @Antisymmetric _ eq _ implb | 1.
Proof. intros [] [] []; simpl; trivial. Qed.

Global Instance flip_implb_Reflexive : Reflexive (Basics.flip implb) | 1.
Proof. intros []; reflexivity. Qed.
Global Instance flip_implb_Transitive : Transitive (Basics.flip implb) | 1.
Proof. intros [] [] []; simpl; trivial. Qed.
Global Instance flip_implb_Antisymmetric : @Antisymmetric _ eq _ (Basics.flip implb) | 1.
Proof. intros [] []; compute; intros [] []; trivial. Qed.



Global Instance implb_implb_Proper0
: Proper (implb ==> Basics.flip implb ==> Basics.flip implb) implb.
Proof. intros [] [] ? [] []; compute; trivial. Qed.

Global Instance implb_implb_Proper1
: Proper (Basics.flip implb ==> implb ==> implb) implb.
Proof. intros [] [] ? [] []; compute; trivial. Qed.

Global Instance implb_flip_implb_Proper0
: Proper (Basics.flip implb ==> implb ==> Basics.flip implb) (Basics.flip implb).
Proof. intros [] [] ? [] []; compute; trivial. Qed.

Global Instance implb_flip_implb_Proper1
: Proper (implb ==> Basics.flip implb ==> implb) (Basics.flip implb).
Proof. intros [] [] ? [] []; compute; trivial. Qed.

Global Instance subrelation_eq_pointwise {A B} : subrelation (@eq (A -> B)) (pointwise_relation A eq).
Proof.
  compute; intros; subst; reflexivity.
Qed.

Global Instance and_flip_impl_Proper
  : Proper (Basics.flip Basics.impl ==> Basics.flip Basics.impl ==> Basics.flip Basics.impl) and | 10.
Proof. lazy; tauto. Qed.

Hint Extern 0 (Proper (_ ==> Basics.impl --> _) and) => apply and_flip_impl_Proper : typeclass_instances.
Hint Extern 0 (Proper (Basics.impl --> _ ==> _) and) => apply and_flip_impl_Proper : typeclass_instances.

Global Instance eq_eq_impl_impl_Proper
  : Proper (eq ==> eq ==> Basics.impl) Basics.impl | 1
  := _.

Global Instance map_Proper_eq_In {A B ls}
  : Proper (forall_relation (fun a x y => List.In a ls -> x = y) ==> eq) (fun f => @List.map A B f ls).
Proof.
  induction ls as [|l ls IHls];
    unfold forall_relation.
  { repeat intro; reflexivity. }
  { intros ?? H.
    simpl; rewrite H by (left; reflexivity).
    f_equal.
    rewrite IHls; [ reflexivity | ].
    intros ??; apply H; right; assumption. }
Qed.

(** If we don't know the relation, default to assuming that it's equality, if the type is not a function *)
Hint Extern 0 (@Reflexive ?T ?e)
 => is_evar e;
      lazymatch T with
      | forall x : _, _ => fail
      | _ => refine eq_Reflexive
      end : typeclass_instances.

Lemma pointwise_Reflexive {A B R} {_ : @Reflexive B R}
  : Reflexive (pointwise_relation A R).
Proof.
  repeat intro; reflexivity.
Qed.
Hint Extern 1 (Reflexive (pointwise_relation _ _)) => apply @pointwise_Reflexive : typeclass_instances.

Ltac solve_Proper_eqs :=
  idtac;
  lazymatch goal with
  | [ |- Proper _ _ ] => apply @reflexive_proper; solve_Proper_eqs
  | [ |- Reflexive (_ ==> _)%signature ]
    => apply @reflexive_eq_dom_reflexive; solve_Proper_eqs
  | [ |- Reflexive _ ] => try apply eq_Reflexive
  end.
Ltac is_evar_or_eq e :=
  first [ is_evar e
        | match e with
          | eq => idtac
          end ].
Ltac is_evar_or_eq_or_evar_free e :=
  first [ is_evar_or_eq e
        | try (has_evar e; fail 1) ].
Hint Extern 1 (Proper ?e _) =>
is_evar_or_eq e; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2) _) =>
is_evar_or_eq e1; is_evar_or_eq_or_evar_free e2; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq_or_evar_free e3; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq_or_evar_free e4; solve_Proper_eqs : typeclass_instances.
