Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.SemanticsOptimized.
Require Import Fiat.Parsers.Reflective.ParserSemanticsOptimized.
Require Import Fiat.Parsers.Reflective.ParserSoundness.
Require Import Fiat.Parsers.Reflective.PartialUnfold.
Require Import Fiat.Parsers.Reflective.ParserPartialUnfold.
Set Implicit Arguments.

Module opt.
  Section polypnormalize.
    Context (is_valid_nonterminal : list nat -> nat -> bool)
            (strlen : nat)
            (char_at_matches_interp : nat -> Reflective.RCharExpr Ascii.ascii -> bool)
            (split_string_for_production : nat * (nat * nat) -> nat -> nat -> list nat).

    Let interp := opt.interp_has_parse_term is_valid_nonterminal strlen char_at_matches_interp split_string_for_production.

    Lemma polypnormalize_correct (term : polyhas_parse_term)
      : ParserSyntaxEquivalence.has_parse_term_equiv
          nil
          (term interp_TypeCode) (term (normalized_of interp_TypeCode))
        -> interp (term _) = interp (polypnormalize term _).
    Proof.
      apply polypnormalize_correct; assumption.
    Qed.
  End polypnormalize.
End opt.
