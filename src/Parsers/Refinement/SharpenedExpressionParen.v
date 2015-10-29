(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ExpressionParen.
Require Import Fiat.Parsers.Refinement.FixedLengthLemmas.

Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec paren_expr_grammar string_stringlike).
  Proof.

    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      set_evars.
      simplify parser splitter.
      finish honing parser method.
    }

    finish_SharpeningADT_WithoutDelegation.
  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec paren_expr_grammar string_stringlike).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Definition paren_expr_parser (str : String.string) : bool.
Proof.
  Time make_parser ComputationalSplitter. (* 13 s *)
Defined.

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
