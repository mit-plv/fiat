(** * Properties about Context Free Grammars *)
Require Import Fiat.Parsers.StringLike.Core Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.

Section cfg.
  Context {Char} {HSLM1 HSLM2 : StringLikeMin Char}
          {HSL1 : @StringLike _ HSLM1}
          {HSL2 : @StringLike _ HSLM2}
          (G : @grammar Char).
  Context (R : @String _ HSLM1 -> @String _ HSLM2 -> Prop).
  Context {is_respectful : transfer_respectful R}.

  Local Ltac t' :=
    repeat match goal with
           | _ => assumption
           | [ |- context[match ?e with _ => _ end] ]
             => is_var e; destruct e
           | _ => tauto
           | _ => solve [ eauto with nocore ]
           | _ => intro
           | [ H : and _ _ |- _ ] => destruct H
           | [ H : ex _ |- _ ] => destruct H
           | [ H : transfer_respectful _ |- _ ] => destruct H; try clear H
           | [ |- and _ _ ] => split
           | [ |- ex _ ] => eexists; solve [ t' ]
           | [ H : is_true (andb ?x _) |- is_true (andb ?x _) ]
             => destruct x eqn:?; simpl in *
           end.

  Local Ltac t :=
    lazymatch goal with
    | [ p : _ |- _ ] => destruct p
    end;
    simpl_simple_parse_of_correct;
    t'.

  Fixpoint transfer_simple_parse_of_correct {str1 str2 pats} (H : R str1 str2) (p : @simple_parse_of Char)
    : simple_parse_of_correct G str1 pats p -> simple_parse_of_correct G str2 pats p
  with transfer_simple_parse_of_production_correct {str1 str2 pat} (H : R str1 str2) (p : @simple_parse_of_production Char)
    : simple_parse_of_production_correct G str1 pat p -> simple_parse_of_production_correct G str2 pat p
  with transfer_simple_parse_of_item_correct {str1 str2 it} (H : R str1 str2) (p : @simple_parse_of_item Char)
    : simple_parse_of_item_correct G str1 it p -> simple_parse_of_item_correct G str2 it p.
  Proof.
    { t. }
    { t. }
    { t. }
  Defined.
End cfg.
