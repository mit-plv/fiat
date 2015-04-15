(** * Simplified parser for (ab)* *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.

Require Import Fiat.Parsers.MinimalParse.
Require Import Fiat.Parsers.ContextFreeGrammarNotations.
Require Import Fiat.Parsers.Grammars.ABStar.

Require Import Fiat.Parsers.BooleanRecognizer Fiat.Parsers.BooleanRecognizerCorrect Fiat.Parsers.Splitters.FirstChar Fiat.Parsers.ContextFreeGrammarProperties.

Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.
Local Notation StringT := (StringWithSplitState string_stringlike (fun _ => True)).

Local Coercion StringT_of_string (str : string) : StringT
  := {| string_val := str : string_stringlike ; state_val := I |}.

Section on_ab_star.
  Definition parse (str : string) : bool
    := let data := ab_star_data in parse_nonterminal (G := ab_star_grammar) str ab_star_grammar.

  Local Notation correct_parse_T
    := ({ parse : string -> bool
                            & forall str,
                                (parse str -> parse_of_item Char_stringlike ab_star_grammar str (NonTerminal _ ab_star_grammar))
                                * (forall p : parse_of string_stringlike ab_star_grammar str (Lookup ab_star_grammar ab_star_grammar),
                                     Forall_parse_of_item
                                       (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
                                       (ParseNonTerminal _ p)
                                     -> parse_nonterminal (G := ab_star_grammar) str ab_star_grammar) }) (only parsing).

  Definition parse_with_correct
  : correct_parse_T.
  Proof.
    exists parse.
    exact (fun str => @parse_nonterminal_correct _ _ _ ab_star_cdata str ab_star_grammar).
  Defined.

  Local Opaque string_dec.

  Definition simplified_parse_with_correct
  : correct_parse_T.
  Proof.
    pose parse_with_correct as p.
    unfold parse_with_correct in p.
    Notation "( x ; *** )" := (existT _ x _).
    unfold parse, parse_nonterminal, parse_nonterminal_or_abort, parse_nonterminal_step, parse_productions, parse_production in p.
    simpl in p.
  Abort.

  Definition simplified_parse (str : string) : bool.
  Proof.
    pose (parse str) as p.
    unfold parse, parse_nonterminal, parse_nonterminal_or_abort, parse_nonterminal_step, parse_productions in p.
    simpl in p.
    unfold parse in p.
  Abort.
End on_ab_star.

Section on_ab_star'.
  Definition parse' (str : string) : bool
    := let data := ab_star'_data in parse_nonterminal (G := ab_star_grammar') str ab_star_grammar'.

  Local Notation correct_parse_T
    := ({ parse : string -> bool
                            & forall str,
                                (parse str -> parse_of_item Char_stringlike ab_star_grammar' str (NonTerminal _ ab_star_grammar'))
                                * (forall p : parse_of string_stringlike ab_star_grammar' str (Lookup ab_star_grammar' ab_star_grammar'),
                                     Forall_parse_of_item
                                       (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
                                       (ParseNonTerminal _ p)
                                     -> parse_nonterminal (G := ab_star_grammar') str ab_star_grammar') }) (only parsing).

  Definition parse_with_correct'
  : correct_parse_T.
  Proof.
    exists parse'.
    exact (fun str => @parse_nonterminal_correct _ _ _ ab_star'_cdata str ab_star_grammar').
  Defined.

  Local Arguments string_dec : simpl never.

  (*Definition simplified_parse_with_correct'
  : correct_parse_T.
  Proof.
    pose parse_with_correct' as p.
    unfold parse_with_correct' in p.
    Notation "( x ; *** )" := (existT _ x _).
    unfold parse', parse_nonterminal, parse_nonterminal_or_abort, parse_nonterminal_step, parse_productions, parse_production in p.
    simpl in p.
  Abort.*)

  Arguments parse_production_subproof {_ _ _ _ _ _ _}.
  Arguments or_intror {_ _ _}.
  Arguments conj {_ _ _ _}.
  Notation or_introrh := (or_intror _).
  Infix "<wf" := (Wf.prod_relation _ _) (at level 50).

  Definition simplified_parse' (str : string) : bool.
  Proof.
    pose (parse' str) as p.
    unfold parse', parse_nonterminal, parse_nonterminal_or_abort, parse_nonterminal_step, parse_productions, combine_sig, rdp_list_is_valid_nonterminal in p.
    simpl in p.
    unfold rdp_list_is_valid_nonterminal, rdp_list_remove_nonterminal, rdp_list_nonterminals_listT, rdp_list_ntl_wf, rdp_list_nonterminals_listT in p.
    let p' := (eval unfold p in p) in
    exact p'.
  Defined.

  Definition simplified_parse'' := Eval cbv beta iota zeta delta [simplified_parse' Common.Wf.Fix3] in simplified_parse'.

  Print simplified_parse'.
End on_ab_star'.

Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Definition test0 := simplified_parse'' "".
Definition test1 := simplified_parse'' "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := simplified_parse'' (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
