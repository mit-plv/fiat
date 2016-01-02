Require Export Fiat.Parsers.ContextFreeGrammar.Core.
Require Export Fiat.Parsers.ContextFreeGrammar.Notations.
Require Export Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Export Coq.Strings.String.
Require Export Fiat.Computation.Core.
Require Export Coq.Program.Program.
Require Export Fiat.Computation.ApplyMonad.
Require Export Fiat.Computation.SetoidMorphisms.
Require Export Fiat.Common.
Require Export Fiat.Parsers.StringLike.Core.

Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Computation.Refinements.General.

Global Open Scope string_scope.
Global Open Scope list_scope.
Global Arguments string_beq : simpl never.
Global Arguments ascii_beq : simpl never.
Global Arguments item_beq : simpl never.
Global Arguments production_beq : simpl never.
Global Arguments productions_beq : simpl never.
Delimit Scope char_scope with char.
Infix "=p" := (production_beq _) (at level 70, no associativity).

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
           | [ |- context G[If ?b Then [?x] Else [?y]] ]
             => rewrite (@pull_If_bool _ _ x y b (fun k => [k]))
           | [ |- context G[If ?b Then ret ?x Else ret ?y] ]
             => rewrite (@pull_If_bool _ _ x y b (fun k => ret k))
         end.

Ltac unguard :=
  rewrite ?(unguard [0]).

Ltac solve_prod_beq :=
  repeat match reverse goal with
           | _ => intro
           | [ H : production_beq _ _ _ = true |- _ ] => apply (production_bl (@ascii_bl)) in H
           | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_iff in H
           | [ H : (_::_) = (_::_) |- _ ] => inversion H; clear H
           | [ H : _ = fst ?x |- _ ] => atomic x; destruct x
           | [ H : [] = (_::_) |- _ ] => exfalso; clear -H; inversion H
           | _ => progress subst
           | _ => progress simpl @fst in *
           | _ => progress simpl @snd in *
           | [ H : _ \/ _ |- _ ] => destruct H
         end.

Definition if_aggregate {A} (b1 b2 : bool) (x y : A)
: (If b1 Then x Else If b2 Then x Else y) = (If (b1 || b2)%bool Then x Else y)
  := if_aggregate b1 b2 x y.
Definition if_aggregate2 {A} (b1 b2 b3 : bool) (x y z : A) (H : b1 = false -> b2 = true -> b3 = true -> False)
: (If b1 Then x Else If b2 Then y Else If b3 Then x Else z) = (If (b1 || b3)%bool Then x Else If b2 Then y Else z)
  := if_aggregate2 x y z H.
Definition if_aggregate3 {A} (b1 b2 b3 b4 : bool) (x y z w : A) (H : b1 = false -> (b2 || b3)%bool = true -> b4 = true -> False)
: (If b1 Then x Else If b2 Then y Else If b3 Then z Else If b4 Then x Else w) = (If (b1 || b4)%bool Then x Else If b2 Then y Else If b3 Then z Else w)
  := if_aggregate3 _ _ x y z w H.

Tactic Notation "simplify" "parser" "splitter" :=
  repeat first [ progress unguard
               | progress simplify with monad laws
               | rewrite !if_aggregate
               | idtac;
                 match goal with
                   | [ |- context[If ?b Then ?x Else If ?b' Then ?x Else _] ]
                     => idtac
                 end;
                 progress repeat setoid_rewrite if_aggregate
               | rewrite !if_aggregate2 by solve_prod_beq
               | rewrite !if_aggregate3 by solve_prod_beq
               | progress parser_pull_tac
               | progress (simpl @fst; simpl @snd) ].
