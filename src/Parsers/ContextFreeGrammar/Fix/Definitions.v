Require Import Coq.PArith.BinPos Coq.PArith.Pnat.
Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Common.Tactics.SplitInContext.
Require Import Fiat.Common.Notations.

Set Implicit Arguments.

Local Coercion is_true : bool >-> Sortclass.
Delimit Scope grammar_fixedpoint_scope with fixedpoint.
Local Open Scope grammar_fixedpoint_scope.

Inductive lattice_for T := top | constant (_ : T) | bottom.
Bind Scope grammar_fixedpoint_scope with lattice_for.
Scheme Equality for lattice_for.

Definition collapse_lattice_for {T} (l : lattice_for T) : option T
  := match l with
       | constant n => Some n
       | _ => None
     end.

Arguments bottom {_}.
Arguments top {_}.
Notation "'⊥'" := bottom : grammar_fixedpoint_scope.
Notation "'⊤'" := top : grammar_fixedpoint_scope.

Global Instance lattice_for_Reflexive {T} {beq : T -> T -> bool}
       {H : Reflexive beq}
  : Reflexive (lattice_for_beq beq).
Proof.
  intros [|?|]; simpl; reflexivity.
Qed.

Global Instance lattice_for_Symmetric {T} {beq : T -> T -> bool}
       {H : Symmetric beq}
  : Symmetric (lattice_for_beq beq).
Proof.
  intros [|?|] [|?|]; simpl; trivial; intro; symmetry; assumption.
Qed.

Global Instance lattice_for_Transitive {T} {beq : T -> T -> bool}
       {H : Transitive beq}
  : Transitive (lattice_for_beq beq).
Proof.
  intros [|?|] [|?|] [|?|]; simpl; trivial;
    try reflexivity;
    try congruence;
    intros; etransitivity; eassumption.
Qed.

Global Instance lattice_for_Equivalence {T} {beq : T -> T -> bool}
       {H : Equivalence beq}
  : Equivalence (lattice_for_beq beq).
Proof.
  split; exact _.
Qed.

Definition lattice_for_lt {T} (lt : T -> T -> bool) (x y : lattice_for T)
  := match x, y with
     | ⊤, ⊤ => false
     | constant x', constant y' => lt x' y'
     | ⊥, ⊥ => false
     | _, ⊤ => true
     | ⊤, _ => false
     | _, constant _ => true
     | constant _, _ => false
     end.

Global Instance lattice_for_lt_Proper {T} {beq lt : T -> T -> bool}
       {H : Proper (beq ==> beq ==> eq) lt}
  : Proper (lattice_for_beq beq ==> lattice_for_beq beq ==> eq) (lattice_for_lt lt).
Proof.
  intros [|a|] [|b|] H0 [|a'|] [|b'|] H1; simpl in *;
    trivial; try congruence.
  apply H; assumption.
Qed.

Definition lattice_for_lub {T} (lub : T -> T -> lattice_for T) (x y : lattice_for T)
  := match x, y with
     | ⊤, ⊤ => ⊤
     | constant x', constant y' => lub x' y'
     | ⊥, ⊥ => ⊥
     | ⊤, _
     | _, ⊤
       => ⊤
     | ⊥, v
     | v, ⊥
       => v
     end.

Section lub_correct.
  Context {T} (beq : T -> T -> bool) (lt : T -> T -> bool) (lub : T -> T -> lattice_for T).

  Local Notation "x <= y" := (orb (lattice_for_beq beq x y) (lattice_for_lt lt x y)).

  Context (lub_correct_l : forall x y, constant x <= lub x y)
          (lub_correct_r : forall x y, constant y <= lub x y)
          (beq_Reflexive : Reflexive beq).

  Lemma lattice_for_lub_correct_l x y
    : x <= lattice_for_lub lub x y.
  Proof.
    clear lub_correct_r.
    destruct x as [|x|], y as [|y|]; try reflexivity.
    { exact (lub_correct_l x y). }
    { simpl.
      rewrite (reflexivity x : is_true (beq x x)).
      reflexivity. }
  Qed.

  Lemma lattice_for_lub_correct_r x y
    : y <= lattice_for_lub lub x y.
  Proof.
    clear lub_correct_l.
    destruct x as [|x|], y as [|y|]; try reflexivity.
    { exact (lub_correct_r x y). }
    { simpl.
      rewrite (reflexivity y : is_true (beq y y)).
      reflexivity. }
  Qed.

  Global Instance lattice_for_lub_Proper
         {lub_Proper : Proper (beq ==> beq ==> lattice_for_beq beq) lub}
    : Proper (lattice_for_beq beq ==> lattice_for_beq beq ==> lattice_for_beq beq) (lattice_for_lub lub).
  Proof.
    intros [|a|] [|b|] H [|a'|] [|b'|] H'; simpl in *;
      trivial; try congruence.
    apply lub_Proper; assumption.
  Qed.
End lub_correct.

Definition lattice_for_gt_well_founded {T} {lt : T -> T -> bool}
           (gt_wf : well_founded (Basics.flip lt))
  : well_founded (Basics.flip (lattice_for_lt lt)).
Proof.
  do 3 (constructor;
        repeat match goal with
               | [ v : T, H : well_founded _ |- _ ] => specialize (H v); induction H
               | [ x : lattice_for _ |- _ ] => destruct x
               | _ => progress simpl in *
               | _ => progress unfold Basics.flip in *
               | [ H : is_true false |- _ ] => exfalso; clear -H; abstract congruence
               | _ => intro
               | _ => solve [ eauto with nocore ]
               end).
Defined.

Global Instance lattice_for_lt_Transitive {T} {lt : T -> T -> bool} {_ : Transitive lt}
  : Transitive (lattice_for_lt lt).
Proof.
  intros [|?|] [|?|] [|?|]; simpl; trivial; try congruence; [].
  intros.
  etransitivity; eassumption.
Qed.

Class grammar_fixedpoint_lattice_data prestate :=
  { state :> _ := lattice_for prestate;
    prestate_lt : prestate -> prestate -> bool;
    state_lt : state -> state -> bool
    := lattice_for_lt prestate_lt;
    prestate_beq : prestate -> prestate -> bool;
    state_beq : state -> state -> bool
    := lattice_for_beq prestate_beq;
    prestate_le s1 s2 := (prestate_beq s1 s2 || prestate_lt s1 s2)%bool;
    state_le s1 s2 := (state_beq s1 s2 || state_lt s1 s2)%bool;
    prestate_beq_Equivalence : Equivalence prestate_beq;
    state_beq_Equivalence : Equivalence state_beq
    := lattice_for_Equivalence;
    preleast_upper_bound : prestate -> prestate -> state;
    least_upper_bound : state -> state -> state
    := lattice_for_lub preleast_upper_bound;
    preleast_upper_bound_correct_l
    : forall a b, state_le (constant a) (preleast_upper_bound a b);
    preleast_upper_bound_correct_r
    : forall a b, state_le (constant b) (preleast_upper_bound a b);
    least_upper_bound_correct_l
    : forall a b, state_le a (least_upper_bound a b)
    := lattice_for_lub_correct_l prestate_beq prestate_lt preleast_upper_bound preleast_upper_bound_correct_l _;
    least_upper_bound_correct_r
    : forall a b, state_le b (least_upper_bound a b)
    := lattice_for_lub_correct_r prestate_beq prestate_lt preleast_upper_bound preleast_upper_bound_correct_r _;
    prestate_gt_wf : well_founded (Basics.flip prestate_lt);
    state_gt_wf : well_founded (Basics.flip state_lt)
    := lattice_for_gt_well_founded prestate_gt_wf;
    preleast_upper_bound_Proper : Proper (prestate_beq ==> prestate_beq ==> state_beq) preleast_upper_bound;
    least_upper_bound_Proper : Proper (state_beq ==> state_beq ==> state_beq) least_upper_bound
    := @lattice_for_lub_Proper _ _ _ _;
    prestate_lt_Proper : Proper (prestate_beq ==> prestate_beq ==> eq) prestate_lt;
    state_lt_Proper : Proper (state_beq ==> state_beq ==> eq) state_lt
    := lattice_for_lt_Proper;
    prestate_lt_Transitive : Transitive prestate_lt;
    state_lt_Transitive : Transitive state_lt
    := lattice_for_lt_Transitive }.

Record grammar_fixedpoint_data :=
  { prestate : Type;
    lattice_data :> grammar_fixedpoint_lattice_data prestate;
    step_constraints : (default_nonterminal_carrierT -> state) -> (default_nonterminal_carrierT -> state -> state);
    step_constraints_ext : Proper (pointwise_relation _ state_beq ==> eq ==> state_beq ==> state_beq) step_constraints }.

Record grammar_fixedpoint_lattice_data_relation
       {xT yT} (x : grammar_fixedpoint_lattice_data xT) (y : grammar_fixedpoint_lattice_data yT) :=
  { state_relation :> @state _ x -> @state _ y -> Prop;
    top_state_related : state_relation ⊤ ⊤;
    state_relation_Proper : Proper (state_beq ==> state_beq ==> iff) state_relation }.

Global Existing Instance lattice_data.
Global Existing Instance step_constraints_ext.
Global Existing Instance state_lt_Transitive.
Global Existing Instance state_beq_Equivalence.
Global Existing Instance prestate_beq_Equivalence.
Global Existing Instance state_lt_Proper.
Global Existing Instance prestate_lt_Proper.
Global Existing Instance least_upper_bound_Proper.
Global Existing Instance preleast_upper_bound_Proper.
Global Existing Instance state_relation_Proper.

Global Arguments state_lt_Transitive {_ _} [_ _ _] _ _.
Global Arguments state_le _ _ !_ !_ / .
Global Arguments state {_ _}, {_} _.

Infix "<=" := (@state_le _ _) : grammar_fixedpoint_scope.
Infix "<" := (@state_lt _ _) : grammar_fixedpoint_scope.
Infix "⊔" := (@least_upper_bound _ _) : grammar_fixedpoint_scope.
Infix "=b" := (@state_beq _ _) : grammar_fixedpoint_scope.

Definition nonterminal_to_positive (nt : default_nonterminal_carrierT) : positive
  := Pos.of_nat (S nt).
Definition positive_to_nonterminal (nt : positive) : default_nonterminal_carrierT
  := pred (Pos.to_nat nt).
Lemma positive_to_nonterminal_to_positive nt : nonterminal_to_positive (positive_to_nonterminal nt) = nt.
Proof.
  unfold nonterminal_to_positive, positive_to_nonterminal.
  erewrite <- S_pred by apply Pos2Nat.is_pos.
  rewrite Pos2Nat.id.
  reflexivity.
Qed.
Lemma nonterminal_to_positive_to_nonterminal nt : positive_to_nonterminal (nonterminal_to_positive nt) = nt.
Proof.
  unfold nonterminal_to_positive, positive_to_nonterminal.
  rewrite Nat2Pos.id_max; simpl.
  reflexivity.
Qed.

Global Instance lattice_for_rect_Proper {A}
  : Proper (eq ==> forall_relation (fun _ => eq) ==> eq ==> forall_relation (fun _ => Basics.flip Basics.impl))
           (@lattice_for_rect A (fun _ => Prop)) | 3.
Proof.
  unfold forall_relation; intros ??? ?? H' ??? [|?|] H''; subst; simpl in *; trivial.
  rewrite H'; assumption.
Qed.

Global Instance lattice_for_rect_Proper_85 {A}
  : Proper (eq ==> forall_relation (fun _ => eq) ==> eq ==> eq ==> Basics.flip Basics.impl)
           (@lattice_for_rect A (fun _ => Prop)) | 3.
Proof.
  unfold forall_relation; intros ??? ?? H' ??? [|?|] ?? H''; subst; simpl in *; trivial.
  rewrite H'; assumption.
Qed.

Lemma lattice_for_rect_pull {A B C} f t c b v
  : f (@lattice_for_rect A (fun _ => B) t c b v)
    = @lattice_for_rect A (fun _ => C) (f t) (fun x => f (c x)) (f b) v.
Proof. destruct v; reflexivity. Qed.


Global Instance state_relation_Proper_impl
       {xT yT x y} (R : @grammar_fixedpoint_lattice_data_relation xT yT x y)
  : Proper (state_beq ==> state_beq ==> Basics.impl) R | 2.
Proof.
  pose proof (state_relation_Proper R) as H.
  unfold Proper, respectful in *; split_iff; eauto.
Qed.
Global Instance state_relation_Proper_flip_impl
       {xT yT x y} (R : @grammar_fixedpoint_lattice_data_relation xT yT x y)
  : Proper (state_beq ==> state_beq ==> Basics.flip Basics.impl) R | 2.
Proof.
  pose proof (state_relation_Proper R) as H.
  unfold Proper, respectful in *; split_iff; eauto.
Qed.
