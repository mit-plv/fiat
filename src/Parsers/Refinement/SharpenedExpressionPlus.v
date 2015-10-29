(** Sharpened ADT for an expression grammar with + *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ExpressionNumPlus.
Require Import Fiat.Parsers.Refinement.FixedLengthLemmas.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)

Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec plus_expr_grammar string_stringlike).
  Proof.
    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    { set_evars.
      simplify parser splitter.
      setoid_rewrite refine_disjoint_search_for; [ | reflexivity.. ].
      simpl.
      finish honing parser method.
    }
    finish_SharpeningADT_WithoutDelegation.
  Defined.

  Lemma ComputationalSplitter
    : FullySharpened (string_spec plus_expr_grammar string_stringlike).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Definition paren_expr_parser (str : String.string) : bool.
Proof.
  Time make_parser ComputationalSplitter. (* 15 s *)
Defined.

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
