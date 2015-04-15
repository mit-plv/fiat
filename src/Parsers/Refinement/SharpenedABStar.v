(** Sharpened ADT for (ab)* *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ABStar.
Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec ab_star_grammar).
  Proof.
    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      finish honing parser method.
    }

    FullySharpenEachMethodWithoutDelegation.
    extract delegate-free implementation.
    simpl; higher_order_reflexivityT.
  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec ab_star_grammar).
  Proof.
    let impl := (eval simpl in (projT1 ComputationalSplitter')) in
    refine (existT _ impl _).
    abstract (exact (projT2 ComputationalSplitter')).
  Defined.

End IndexedImpl.

Global Arguments ComputationalSplitter / .

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Time Definition ab_star_parser (str : String.string) : bool
  := Eval simpl in has_parse (parser ComputationalSplitter) str.

Print ab_star_parser.

Recursive Extraction ab_star_parser.
