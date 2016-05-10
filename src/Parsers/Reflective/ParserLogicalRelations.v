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
        (char_at_matches : nat -> Reflective.RCharExpr Ascii.ascii -> bool)
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
  simpl in *.
  unfold step_option_rec.
  unfold Proper, respectful, pointwise_relation in *.
  edestruct Compare_dec.lt_dec; simpl;
    [
    | edestruct Sumbool.sumbool_of_bool; simpl; [ | reflexivity ] ];
    (erewrite <- H''; [ reflexivity | .. ]);
    try solve [ intros; subst; reflexivity
              | intros; subst; eauto using eq_refl with nocore ].
Qed.
