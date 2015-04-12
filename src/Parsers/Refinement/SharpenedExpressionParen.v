(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.Refinement.Tactics.
Require Import ADTSynthesis.Parsers.Grammars.ExpressionParen.
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
  : FullySharpened (string_spec paren_expr_grammar).
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
(*
Ltac do_simpl_in x hyp :=
  let x' := (eval simpl in x) in
  change x with x' in hyp.
Ltac do_compute_in x hyp :=
  let x' := (eval compute in x) in
  change x with x' in hyp.

Definition paren_expr_parser (str : String.string) : bool.
Proof.
  pose (has_parse (parser ComputationalSplitter) str) as impl.
  Timeout 60 cbv beta iota zeta delta [has_parse parser ParserImplementationOptimized.parser transfer_parser prod_relation ltof list_to_productions new_string_of_string new_string_of_base_string item_ascii_cons item_ascii item_of_char item_of_string BooleanRecognizer.parse_production BooleanRecognizer.parse_item ComputationalSplitter BooleanBaseTypes.split_string_for_production If_Then_Else fst snd projT1 projT2 ContextFreeGrammarEquality.production_beq Equality.list_beq ContextFreeGrammarEquality.item_beq Equality.ascii_beq StringBound.bindex StringBound.indexb ComputationalADT.cConstructors Equality.bool_beq map hd fold_left fold_right list_to_grammar Start_symbol Lookup bool_rect StringLike.String item_ascii_cons item_ascii item_of_char item_of_string new_string_of_base_string BooleanRecognizer.parse_production BooleanRecognizer.parse_item BooleanBaseTypes.split_string_for_production ParserImplementation.parser is_char StringLike.length string_stringlike BooleanRecognizerOptimized.parse_nonterminal_opt proj1_sig proj2_sig ComputationalADT.cADT string_rep ComputationalADT.LiftcADT SplitterFromParserADT.adt_based_splitter orb andb] in impl.

Print CallConstructor.
Locate "=p".
  Timeout 2 simpl is_char in impl.
  Timeout 2 simpl ((CallConstructor (projT1 ComputationalSplitter) "new")) in impl.
  Timeout 2 cbv beta iota zeta in impl.
  Timeout 15 simpl (BooleanBaseTypes.split_string_for_production _ _) in impl.
  Timeout 5 cbv beta iota zeta in impl.
  Timeout 2 simpl hd in impl.
  Timeout 2 simpl (map fst _) in impl.
  Timeout 2 cbv beta iota zeta delta [map] in impl.
  Timeout 2 change (fst (?x, _)) with x in impl.
  Timeout 2 change (snd (_, ?x)) with x in impl.
  Timeout 2 cbv beta iota zeta delta [hd] in impl.
  Timeout 2 cbv beta iota zeta delta [fold_left] in impl.
  Timeout 2 change (fst (?x, _)) with x in impl.
  Timeout 2 change (snd (_, ?x)) with x in impl.
  Timeout 2 cbv beta iota zeta delta [fold_right] in impl.
  Timeout 5 change (fst (?x, _)) with x in impl.
  Timeout 5 change (snd (_, ?x)) with x in impl.
  Timeout 5 cbv beta iota zeta in impl.
  Timeout 5 cbv beta iota zeta delta [] in impl.
  Timeout 10 change (orb false) with (fun x : bool => x) in impl.
  Timeout 2 cbv beta iota zeta delta [new_string_of_base_string] in impl.
  Timeout 2 cbv beta iota zeta delta [] in impl.
  Timeout 2 cbv beta iota zeta delta [item_ascii_cons item_ascii item_of_char item_of_string] in impl.
  Timeout 10 cbv beta iota zeta delta [BooleanRecognizer.parse_production] in impl.
  Timeout 10 cbv beta iota zeta delta [BooleanRecognizer.parse_item] in impl.

  Timeout 5 lazymatch eval cbv delta [impl] in impl with
    | appcontext [@BooleanBaseTypes.split_string_for_production
                 ?a ?b ?c ?d ?e]
      => set (X := @BooleanBaseTypes.split_string_for_production
                     a b c d e)
  end.
                           (Terminal "1"%char) [])).
  Timeout 25 simpl (BooleanBaseTypes.split_string_for_production _) in impl.
  Timeout 10 cbv beta iota zeta delta [] in impl.
  Timeout 5 cbv beta iota zeta delta [map] in impl.
  Timeout 10 cbv beta iota zeta delta [fold_left] in impl.
  Timeout 10 cbv beta iota zeta delta [fold_left] in impl.


  Timeout 2 change (fst (?x, _)) with x in impl.
  Timeout 2 change (snd (_, ?x)) with x in impl.
  Timeout 2 cbv beta iota zeta delta [fold_right] in impl.
  Timeout 2 change (fst (?x, _)) with x in impl.
  Timeout 5 change (snd (_, ?x)) with x in impl.


  Unset Printing Notations.
 := item Ascii.ascii.
Coercion item_of_char (ch : Ascii.ascii) : item_ascii := Terminal ch.
Coercion item_of_string (nt : string) : item_ascii := NonTerminal nt.
Definition production_of_string] in impl.

  Timeout 2 simpl fst in impl.

Timeout 2 simpl @list_to_grammar in impl.
  Timeout 2 simpl @list_to_productions in impl.

  Timeout 10 simpl map in impl.


  Timeout 2 cbv beta iota zeta delta [has_parse] in impl.
*)
Time Definition paren_expr_parser (str : String.string) : bool
  := Eval simpl in has_parse (parser ComputationalSplitter) str.

Print paren_expr_parser.
Import ADTSynthesis.Parsers.ExtrOcamlParsers.HideProofs.
Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
