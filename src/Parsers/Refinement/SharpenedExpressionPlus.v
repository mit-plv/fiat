(** Sharpened ADT for an expression grammar with + *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.Refinement.Tactics.
Require Import ADTSynthesis.Parsers.Grammars.ExpressionNumPlus.
Require Import ADTSynthesis.Computation.Refinements.General.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTSynthesis.Common.
Require Import ADTSynthesis.Common.Wf.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Parsers.BaseTypes.
Require Import ADTSynthesis.Parsers.Refinement.FixedLengthLemmas.

Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec plus_expr_grammar).
  Proof.
    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      Require Import ParserInterface.
      unfold split_list_is_complete.
      Import ContextFreeGrammarProperties.
      finish honing parser method.
    }

    FullySharpenEachMethodWithoutDelegation.
    extract delegate-free implementation.
    simpl; higher_order_reflexivityT.
  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec paren_expr_grammar).
  Proof.
    let impl := (eval simpl in (projT1 ComputationalSplitter')) in
    refine (existT _ impl _).
    abstract (exact (projT2 ComputationalSplitter')).
  Defined.

End IndexedImpl.

Global Arguments ComputationalSplitter / .

Require Import ADTSynthesis.Parsers.ParserFromParserADT.
Require Import ADTSynthesis.Parsers.ExtrOcamlParsers.
Import ADTSynthesis.Parsers.ExtrOcamlParsers.HideProofs.

Time Definition paren_expr_parser (str : String.string) : bool
  := Eval simpl in has_parse (parser ComputationalSplitter) str.

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
