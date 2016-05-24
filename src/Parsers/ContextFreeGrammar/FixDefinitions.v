Require Import Coq.Classes.RelationClasses.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Common.Notations.

Set Implicit Arguments.

Local Coercion is_true : bool >-> Sortclass.

Class grammar_fixedpoint_lattice_data state :=
  { state_lt : state -> state -> bool;
    state_beq : state -> state -> bool;
    state_le s1 s2 := (state_beq s1 s2 || state_lt s1 s2)%bool;
    state_beq_refl : forall s, state_beq s s;
    state_beq_bl : forall s1 s2, state_beq s1 s2 -> s1 = s2;
    greatest_lower_bound : state -> state -> state;
    greatest_lower_bound_correct_l
    : forall a b, state_le (greatest_lower_bound a b) a;
    greatest_lower_bound_correct_r
    : forall a b, state_le (greatest_lower_bound a b) b;
    initial_state : default_nonterminal_carrierT -> state;
    bottom : state;
    bottom_bottom : forall st, state_le bottom st;
    state_lt_wf : well_founded state_lt;
    state_lt_Transitive : Transitive state_lt }.

Record grammar_fixedpoint_data :=
  { state :> Type;
    lattice_data :> grammar_fixedpoint_lattice_data state;
    step_constraints : (default_nonterminal_carrierT -> state) -> (default_nonterminal_carrierT -> state -> state) }.

Global Existing Instance lattice_data.

Delimit Scope grammar_fixedpoint_scope with fixedpoint.
Local Open Scope grammar_fixedpoint_scope.

Infix "<=" := (@state_le _ _) : grammar_fixedpoint_scope.
Infix "<" := (@state_lt _ _) : grammar_fixedpoint_scope.
Infix "⊓" := (@greatest_lower_bound _ _) : grammar_fixedpoint_scope.
Infix "=b" := (@state_beq _ _) : grammar_fixedpoint_scope.
Notation "'⊥'" := (@bottom _ _) : grammar_fixedpoint_scope.

Arguments state_lt_Transitive {_ _} [_ _ _] _ _.
Global Existing Instance state_lt_Transitive.

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
