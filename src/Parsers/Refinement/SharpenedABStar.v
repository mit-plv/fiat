(** Sharpened ADT for (ab)* *)
Require Import ADTSynthesis.Parsers.Refinement.Tactics.
Require Import ADTSynthesis.Parsers.Grammars.ABStar.
Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter
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
  Defined.

End IndexedImpl.

Require Import ADTSynthesis.Parsers.ParserFromParserADT.
Require Import ADTSynthesis.Parsers.ParserImplementation.
Require Import ADTSynthesis.ADT.ComputationalADT.

Definition ab_star_parser : String.string -> bool.
Proof.
  refine (fun s => has_parse (parser (adt_based_splitter ComputationalSplitter)) _).
  pose (cConstructors (projT1 ComputationalSplitter) {| StringBound.bindex := "new" |} s).
  Require Import StringLike.Core StringLike.String.
  simpl.
  pose .
  simpl in c.
  unfold cConstructorType in *.

lazy.
 (s, (0, String.length s))).
    simpl in b.
Require Import StringLike.Core.
simpl in b.
Set Printing All.


Check ab_star_parser.
Check .
