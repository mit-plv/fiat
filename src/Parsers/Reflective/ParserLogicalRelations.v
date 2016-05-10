Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.PartialUnfold.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.
Require Import Fiat.Parsers.Reflective.ParserSyntax Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.ParserPartialUnfold.
Require Import Fiat.Parsers.Reflective.ParserSyntaxEquivalence.
Require Import Fiat.Parsers.Reflective.LogicalRelations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListMorphisms.
Require Import Fiat.Common.Wf2.

Definition extract_Term {var} (E : has_parse_term var) : Term var _
  := match E with
     | RFix2 G_length up_to_G_length f valid_len valids nt_idx
       => f
     end.

Theorem polypnormalize_correct
        (is_valid_nonterminal : list nat -> nat -> bool)
        (strlen : nat)
        (char_at_matches : nat -> (Ascii.ascii -> bool) -> bool)
        (split_string_for_production : nat * (nat * nat) -> nat -> nat -> list nat)
  : forall (E : polyhas_parse_term),
    has_parse_term_equiv nil (E interp_TypeCode) (E (normalized_of interp_TypeCode))
    -> interp_has_parse_term
         is_valid_nonterminal strlen char_at_matches split_string_for_production
         (E _)
       = interp_has_parse_term
           is_valid_nonterminal strlen char_at_matches split_string_for_production
           (polypnormalize E _).
Proof.
  intros E H.
  unfold polypnormalize, pnormalize.
  pose proof (fun H => @polynormalize_correct _ (fun var => extract_Term (E _)) H) as H''.
  unfold extract_Term in *.
  unfold polynormalize in *.
  destruct H; simpl.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
         end.
  refine (Fix2_5_Proper_eq _ _ _ _ _ _ _ _ _ _);
    unfold forall_relation, pointwise_relation;
    repeat intro.
  rewrite <- H''.
  unfold step_option_rec.
  edestruct Compare_dec.lt_dec; simpl;
    [
    | edestruct Sumbool.sumbool_of_bool; simpl; [ | reflexivity ] ].
  (*
    rewrite H''.
    Focus 2.
  { change (fun x => ?f x) with f.
    simpl in *.

  unfold interp_has_parse_term.
  unfold interp_Term, polynormalize, normalize; eauto.*)
  admit.
  admit.
Qed.
