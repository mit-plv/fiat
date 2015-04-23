Require Import Coq.Arith.Compare_dec Coq.Strings.String.
Require Import Fiat.Common.Equality Fiat.Parsers.ParserFromParserADT Fiat.Parsers.SplitterFromParserADT Fiat.Parsers.ParserInterface.
Require Import Coq.Arith.Wf_nat.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.NatFacts.
Require Export Fiat.Parsers.Refinement.Tactics.
Require Export Fiat.ADTNotation.BuildComputationalADT.
Require Export Fiat.Common.NatFacts.
Require Export Coq.Strings.Ascii.
Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.
Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Inlined Constant Sumbool.sumbool_of_bool => "(fun x -> x)".
Extract Inlined Constant Equality.ascii_beq => "(=)".
Extract Inlined Constant ascii_eq_dec => "(=)".
Extract Constant minusr => "fun n m -> Pervasives.max 0 (n-m)".

Global Arguments string_dec : simpl never.
Global Arguments Equality.string_beq : simpl never.
Global Arguments SplitterFromParserADT.msplits / .
Global Arguments splits_for / .
Global Arguments Equality.ascii_beq !_ !_ / .
Global Arguments SplitterFromParserADT.mlength / .
Global Arguments SplitterFromParserADT.mis_char / .
Global Arguments SplitterFromParserADT.mtake / .
Global Arguments SplitterFromParserADT.mdrop / .
Global Arguments SplitterFromParserADT.mto_string / .
Global Arguments new_string_of_string / .
Global Arguments ComputationalADT.cRep / .
Global Arguments new_string_of_base_string / .
Global Arguments ComputationalADT.cConstructors / .
Global Arguments Wf.prod_relation / .
Global Arguments Wf_nat.ltof / .

Module HideProofs.
  Notation hex := (ex _).
  Notation exist' x := (exist _ x _).
  Notation horr := (or_intror _).
  Notation horl := (or_introl _).
End HideProofs.
