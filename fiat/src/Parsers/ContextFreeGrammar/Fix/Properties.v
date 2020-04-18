Require Export Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Common.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.BoolFacts.

Set Implicit Arguments.
Local Open Scope grammar_fixedpoint_scope.

Lemma state_beq_lb {prestate} {fp : grammar_fixedpoint_lattice_data prestate} (s s' : state) (H : s = s') : s =b s'.
Proof.
  subst; reflexivity.
Qed.

Lemma state_beq_refl {prestate} {fp : grammar_fixedpoint_lattice_data prestate} (s : state) : s =b s.
Proof.
  reflexivity.
Qed.

Lemma state_le_refl {prestate} {fp : grammar_fixedpoint_lattice_data prestate} (s : state) : s <= s.
Proof.
  unfold state_le.
  rewrite state_beq_lb by reflexivity.
  reflexivity.
Qed.

Global Instance state_lt_Irreflexive {T d} : Irreflexive (@state_lt T d).
Proof.
  intros x H.
  induction (state_gt_wf x) as [x H' IH].
  eauto.
Qed.

Global Instance state_le_Reflexive {T d} : Reflexive (@state_le T d).
Proof.
  unfold state_le; repeat intro; rewrite state_beq_refl; reflexivity.
Qed.

Global Instance state_beq_Proper_Proper {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : Proper (state_beq ==> state_beq ==> eq) state_beq.
Proof.
  intros a b H a' b' H'.
  destruct (b =b b') eqn:H'';
    fold_is_true.
  { etransitivity; [ eassumption | ].
    etransitivity; [ eassumption | ].
    symmetry; assumption. }
  { destruct (a =b a') eqn:H'''; trivial;
    rewrite <- H''; clear H''; symmetry;
    fold_is_true.
    etransitivity; [ | eassumption ].
    etransitivity; [ | eassumption ].
    symmetry; assumption. }
Qed.


Global Instance state_beq_Proper_le {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : Proper (state_beq ==> state_beq ==> eq) state_le.
Proof.
  intros a b H a' b' H'.
  unfold state_le.
  rewrite H, H'.
  reflexivity.
Qed.

Global Instance beq_subrelation_le {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : subrelation state_beq state_le.
Proof.
  intros ?? H.
  setoid_rewrite H.
  reflexivity.
Qed.

Global Instance state_le_Transitive {T d} : Transitive (@state_le T d).
Proof.
  unfold state_le, is_true; repeat intro;
    rewrite Bool.orb_true_iff in *;
    destruct_head or;
    repeat match goal with
           | [ H : context[?x = true] |- _ ] => progress fold (is_true x) in *
           | [ |- context[?x = true] ] => progress fold (is_true x) in *
           | [ H : is_true (?x =b ?y) |- _ ] => rewrite H in *; clear x H
           | _ => left; reflexivity
           | _ => solve [ eauto ]
           | _ => right; etransitivity; eassumption
           end.
Qed.

Lemma bottom_bottom {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : ⊥ <= s.
Proof.
  destruct s; reflexivity.
Qed.

Lemma top_top {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : s <= ⊤.
Proof.
  destruct s; reflexivity.
Qed.

Lemma no_state_lt_bottom {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (s < ⊥) = false.
Proof.
  destruct s; reflexivity.
Qed.

Lemma no_state_gt_top {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (⊤ < s) = false.
Proof.
  destruct s; reflexivity.
Qed.

Lemma state_le_bottom_eq_bottom {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (s <= ⊥) = (s =b ⊥).
Proof.
  destruct s; reflexivity.
Qed.

Lemma state_ge_top_eq_top {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (⊤ <= s) = (s =b ⊤).
Proof.
  destruct s; reflexivity.
Qed.

Lemma top_lub_r {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (s ⊔ ⊤) = ⊤.
Proof.
  destruct s; reflexivity.
Qed.

Lemma top_lub_l {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (⊤ ⊔ s) = ⊤.
Proof.
  destruct s; reflexivity.
Qed.

Lemma bottom_lub_r {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (s ⊔ ⊥) = s.
Proof.
  destruct s; reflexivity.
Qed.

Lemma bottom_lub_l {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (⊥ ⊔ s) = s.
Proof.
  destruct s; reflexivity.
Qed.

Global Instance state_le_Proper_le {state} {d : grammar_fixedpoint_lattice_data state}
: Proper (@state_le _ d ==> Basics.flip (@state_le _ d) ==> Basics.flip Basics.impl) (@state_le _ d).
Proof.
  unfold Basics.flip; intros ?? H ?? H' H''.
  repeat first [ eassumption | etransitivity; [ eassumption | ] ].
Qed.

Global Instance state_le_Proper_le' {state} {d : grammar_fixedpoint_lattice_data state}
: Proper (@state_le _ d ==> Basics.flip (@state_le _ d) ==> Basics.flip implb) (@state_le _ d).
Proof.
  unfold Basics.flip; intros (*?? [??]*) ?? H ?? H'; subst.
  match goal with |- is_true (implb ?v _) => destruct v eqn:?; simpl; [ | reflexivity ] end.
  repeat first [ eassumption | etransitivity; [ eassumption | ] ].
Qed.

Global Instance state_le_flip_Reflexive {state} {d : grammar_fixedpoint_lattice_data state}
: Reflexive (Basics.flip (@state_le _ d)) | 2.
Proof.
  unfold Basics.flip; intro; reflexivity.
Qed.

Global Instance prestate_le_Antisymmetric {prestate} {fpdata : grammar_fixedpoint_lattice_data prestate}
  : Antisymmetric _ prestate_beq prestate_le.
Proof.
  unfold prestate_le.
  intros x y H0 H1.
  bool_congr_setoid.
  destruct H0 as [H0|H0]; [ | destruct H1 as [H1|H1] ];
    [ assumption
    | symmetry; assumption
    | ].
  exfalso; eapply no_wf_cycle; [ eexact prestate_gt_wf | | ];
    unfold flip; eassumption.
Qed.

Global Instance state_le_Antisymmetric {prestate} {fpdata : grammar_fixedpoint_lattice_data prestate}
  : Antisymmetric _ state_beq state_le.
Proof.
  unfold state_le.
  intros x y H0 H1.
  bool_congr_setoid.
  destruct H0 as [H0|H0]; [ | destruct H1 as [H1|H1] ];
    [ assumption
    | symmetry; assumption
    | ].
  exfalso; eapply no_wf_cycle; [ eexact state_gt_wf | | ];
    unfold flip; eassumption.
Qed.

Global Instance state_beq_Proper_eq {a b}
  : Proper (eq ==> eq ==> eq) (@state_beq a b)
  := _.
