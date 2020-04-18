Require Export Fiat.Parsers.ContextFreeGrammar.Core.
Require Export Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Export Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Export Coq.Strings.String.
Require Export Fiat.Computation.Core.
Require Export Coq.Program.Program.
Require Export Fiat.Computation.ApplyMonad.
Require Export Fiat.Computation.SetoidMorphisms.
Require Export Fiat.Common.
Require Export Fiat.Parsers.StringLike.Core.

Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.NatFacts.

Export Common.opt2.Notations.

Global Open Scope string_scope.
Global Open Scope list_scope.
Global Arguments string_beq : simpl never.
Global Arguments ascii_beq : simpl never.
Global Arguments item_beq : simpl never.
Global Arguments production_beq : simpl never.
Global Arguments productions_beq : simpl never.
Delimit Scope char_scope with char.
Infix "=p" := (production_beq _) (at level 70, no associativity).

(** Unfolding rules for enumerated ascii *)
Global Arguments Ascii.one / .
Global Arguments Ascii.shift _ !_ / .
Global Arguments Ascii.ascii_of_pos !_ / .
Global Arguments Ascii.ascii_of_nat !_ / .
Global Arguments Carriers.default_nonterminal_carrierT / .

Section tac_helpers.
  Lemma pull_match_list {A R R' rn rc} {ls : list A} (f : R -> R')
  : match ls with
      | nil => f rn
      | cons x xs => f (rc x xs)
    end = f (match ls with
               | nil => rn
               | cons x xs => rc x xs
             end).
  Proof.
    destruct ls; reflexivity.
  Qed.

  Lemma pull_match_item {A R R' rn rc} {ls : item A} (f : R -> R')
  : match ls with
      | NonTerminal x => f (rn x)
      | Terminal x => f (rc x)
    end = f (match ls with
               | NonTerminal x => rn x
               | Terminal x => rc x
             end).
  Proof.
    destruct ls; reflexivity.
  Qed.

  Lemma pull_match_bool {R R' rn rc} {b : bool} (f : R -> R')
  : (if b then f rn else f rc)
    = f (if b then rn else rc).
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma pull_If_bool {R R' rn rc} {b : bool} (f : R -> R')
  : (If b Then f rn Else f rc)
    = f (If b Then rn Else rc).
  Proof.
    destruct b; reflexivity.
  Qed.
End tac_helpers.

Lemma unguard {T} (x : T)
: refine { x' : T | True }
         (ret x).
Proof.
  repeat intro; computes_to_inv; subst.
  apply PickComputes; constructor.
Qed.

Global Arguments unguard {_} _ [_] _.

Ltac parser_pull_tac :=
  repeat match goal with
           | [ |- context G[match ?ls with
                              | nil => [?x]
                              | (_::_) => [?y]
                            end] ]
             => rewrite (@pull_match_list _ _ _ x (fun _ _ => y) ls (fun k => [k]))
           | [ |- context G[match ?it with
                              | NonTerminal _ => [?x]
                              | Terminal _ => [?y]
                            end] ]
             => rewrite (@pull_match_item _ _ _ (fun _ => x) (fun _ => y) it (fun k => [k]))
           | [ |- context G[match ?b with
                              | true => [?x]
                              | false => [?y]
                            end] ]
             => rewrite (@pull_match_bool _ _ x y b (fun k => [k]))
           | [ |- context G[match ?b with
                              | true => ret ?x
                              | false => ret ?y
                            end] ]
             => rewrite (@pull_match_bool _ _ x y b (fun k => ret k))
           | [ |- context G[If ?b Then [?x] Else [?y] ] ]
             => rewrite (@pull_If_bool _ _ x y b (fun k => [k]))
           | [ |- context G[If ?b Then ret ?x Else ret ?y] ]
             => rewrite (@pull_If_bool _ _ x y b (fun k => ret k))
         end.

Ltac unguard :=
  rewrite ?(unguard [0]).

Ltac solve_prod_beq :=
  clear;
  repeat match goal with
           | [ |- context[true = false] ] => congruence
           | [ |- context[false = true] ] => congruence
           | [ |- context[EqNat.beq_nat ?x ?y] ]
             => is_var x;
               let H := fresh in
               destruct (EqNat.beq_nat x y) eqn:H;
                 [ apply EqNat.beq_nat_true in H; subst x
                 | ];
                 simpl
           | [ |- context[EqNat.beq_nat ?x ?y] ]
             => first [ is_var x; fail 1
                      | generalize x; intro ]
         end.

Definition if_aggregate {A} (b1 b2 : bool) (x y : A)
: (If b1 Then x Else If b2 Then x Else y) = (If (b1 || b2)%opt2_bool Then x Else y)
  := if_aggregate b1 b2 x y.
Definition if_aggregate2 {A} (b1 b2 b3 : bool) (x y z : A) (H : b1 = false -> b2 = true -> b3 = true -> False)
: (If b1 Then x Else If b2 Then y Else If b3 Then x Else z) = (If (b1 || b3)%opt2_bool Then x Else If b2 Then y Else z)
  := if_aggregate2 x y z H.
Definition if_aggregate3 {A} (b1 b2 b3 b4 : bool) (x y z w : A) (H : b1 = false -> (b2 || b3)%bool = true -> b4 = true -> False)
: (If b1 Then x Else If b2 Then y Else If b3 Then z Else If b4 Then x Else w) = (If (b1 || b4)%opt2_bool Then x Else If b2 Then y Else If b3 Then z Else w)
  := if_aggregate3 _ _ x y z w H.

Module opt2.
  Definition orb_false_r : forall b, (b || false)%opt2_bool = b
    := Bool.orb_false_r.
  Definition andb_orb_distrib_r : forall b1 b2 b3 : bool,
      (b1 && (b2 || b3))%opt2_bool = (b1 && b2 || b1 && b3)%opt2_bool
    := Bool.andb_orb_distrib_r.
  Definition andb_orb_distrib_l : forall b1 b2 b3 : bool,
      ((b1 || b2) && b3)%opt2_bool = (b1 && b3 || b2 && b3)%opt2_bool
    := Bool.andb_orb_distrib_l.
  Definition orb_andb_distrib_r
    : forall b1 b2 b3 : bool,
      (b1 || b2 && b3)%opt2_bool = ((b1 || b2) && (b1 || b3))%opt2_bool
    := Bool.orb_andb_distrib_r.
  Definition orb_andb_distrib_l
    : forall b1 b2 b3 : bool,
      (b1 && b2 || b3)%opt2_bool = ((b1 || b3) && (b2 || b3))%opt2_bool
    := Bool.orb_andb_distrib_l.
  Definition andb_assoc
    : forall b1 b2 b3 : bool, (b1 && (b2 && b3))%opt2_bool = (b1 && b2 && b3)%opt2_bool
    := Bool.andb_assoc.
  Definition orb_assoc
    : forall b1 b2 b3 : bool, (b1 || (b2 || b3))%opt2_bool = (b1 || b2 || b3)%opt2_bool
    := Bool.orb_assoc.
  Definition andb_orb_distrib_r_assoc
    : forall b1 b2 b3 b4 : bool,
      (b1 && (b2 || b3) || b4)%opt2_bool = (b1 && b2 || (b1 && b3 || b4))%opt2_bool
    := andb_orb_distrib_r_assoc.
  Definition beq_0_1_leb
    : forall x : nat,
      (opt2.beq_nat x 1 || opt2.beq_nat x 0)%opt2_bool = opt2.leb x 1
    := beq_0_1_leb.
  Definition beq_S_leb
    : forall x n : nat,
      (opt2.beq_nat x (S n) || opt2.leb x n)%opt2_bool = opt2.leb x (S n)
    := beq_S_leb.
End opt2.
