(** Sharpened ADT for (ab)* *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ABStar.
Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec ab_star_grammar).
  Proof.

    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      finish honing parser method.
    }

    Time finish_SharpeningADT_WithoutDelegation.
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

Definition test0 := ab_star_parser "".
Definition test1 := ab_star_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := ab_star_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
