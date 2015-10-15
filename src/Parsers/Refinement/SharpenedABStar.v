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
      set_evars.
      simplify parser splitter.
      finish honing parser method.
    }
    finish_SharpeningADT_WithoutDelegation.

  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec ab_star_grammar).
  Proof.
    let impl := (eval simpl in (projT1 ComputationalSplitter')) in
    pose impl.
    exfalso.
    Set Printing All.
    idtac.

    idtac.

    abstract (exact (projT2 ComputationalSplitter')).
  Defined.

End IndexedImpl.

Global Arguments ComputationalSplitter / .

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

(* Ben : Taking too long to run; commenting so I can debug build. *)
Time Definition ab_star_parser (str : String.string) : bool.
  pose (has_parse (parser ComputationalSplitter) str).
  Set Printing Implicit.
  idtac.
  unfold callcADTMethod in b.
  unfold has_parse, parser, ComputationalSplitter in b.
  unfold ParserImplementationOptimized.parser in b.
  unfold transfer_parser,
  ParserImplementation.parser,
  SplitterFromParserADT.adt_based_splitter in b.
  unfold new_string_of_string in b.
  cbv delta [BooleanRecognizerEquality.proj] in b.
  cbv beta in b.
  cbv iota beta delta [adtProj] in b.
  unfold proj1_sig in b.
  unfold new_string_of_base_string in b.
  unfold projT1 in b.
  unfold ComputationalADT.cConstructors in b.
  unfold ComputationalADT.pcConstructors in b.
  unfold projT2 in b.
  unfold BuildcADT in b.
  unfold getcConsDef in b.
  unfold ilist.icons in b.
  unfold ilist.inil in b.
  unfold newS in b.
  unfold BoundedLookup.ibound, BoundedLookup.indexb in b.
  simpl ilist.ith in b.
  cbv beta iota in b.
  unfold Fin.R in b.
  unfold Vector.caseS in b.
  unfold ilist.ilist_hd in b.
  unfold ilist.prim_fst in b.
  Locate "Def".
  unfold cConsBody in b.
  unfold BooleanRecognizerOptimized.to_string,
  BooleanRecognizerOptimized.of_string in b.
  unfold BooleanRecognizerOptimized.str_carrier_default, callcADTMethod in b.
  unfold projT2, proj1_sig in b.
  unfold ComputationalADT.cMethods in b.
  unfold ComputationalADT.pcMethods in b.
  unfold projT2 in b.
  unfold BuildcADT in b.
  unfold getcMethDef, projT1 in b.
  unfold StringLike.length in b.
  unfold SplitterFromParserADT.adt_based_StringLike_lite in b.
  unfold SplitterFromParserADT.mlength in b.
  unfold BooleanRecognizerOptimized.str_carrier_default, callcADTMethod in b.
  unfold projT2, proj1_sig in b.
  unfold ComputationalADT.cMethods in b.
  unfold ComputationalADT.pcMethods in b.
  unfold projT2 in b.
  unfold BuildcADT in b.
  unfold getcMethDef, projT1 in b.
  unfold BoundedLookup.ibound, BoundedLookup.indexb in b.
  simpl ilist.ith in b.
  unfold snd in b.
  unfold VectorFacts.Vector_caseS' in b.
  unfold Vector.caseS, ilist.ilist_tl in b.
  unfold ilist.ilist_hd, ilist.prim_snd, ilist.prim_fst in b.
  unfold cMethBody in b.
  unfold StringLike.String in b.
  unfold ComputationalADT.cRep, projT1 in b.
  simpl @fst in b.
  unfold SplitterFromParserADT.msplits, SplitterFromParserADT.mget in b.
  simpl List.hd in b.
  simpl List.length in b.
  simpl List.map in b.
  Set Printing Implicit.
  idtac.
  unfold callcADTMethod in b.
  unfold projT2, proj1_sig in b.
  unfold ComputationalADT.cMethods in b.
  unfold ComputationalADT.pcMethods in b.
  unfold projT2 in b.
  unfold BuildcADT in b.
  cbv beta iota in b.
  unfold BoundedLookup.ibound, BoundedLookup.indexb in b.
  simpl ilist.ith in b.
  unfold ilist.ith in b.
  unfold VectorFacts.Vector_caseS' in b.
  unfold Vector.caseS in b.
  unfold ilist.ilist_hd, ilist.ilist_tl, ilist.prim_snd, ilist.prim_fst in b.
  unfold SplitterFromParserADT.adt_based_StringLike in b.
  unfold StringLike.String in b.
  unfold ComputationalADT.cRep in b.
  unfold pdata in b.
  unfold projT1, BooleanRecognizerEquality.data' in b.
  unfold BaseTypes.predata in b.
  unfold ParserImplementation.parser_data in b.
  Timeout 45 simpl in b.
  unfold ibound, BoundedLindexb
  simpl in b.
  Print ilist.ith.
  Locate "cADTRep".
  Print ab_star_parser.

Recursive Extraction ab_star_parser.

Definition test0 := ab_star_parser "".
Definition test1 := ab_star_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := ab_star_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
