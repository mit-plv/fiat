(** * Simplified parser for (ab)* *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.BaseTypes Parsers.BooleanBaseTypes.
Require Import Parsers.Splitters.RDPList.
Require Import Common.

Require Import Parsers.MinimalParse.
Require Import Parsers.ContextFreeGrammarNotations.
Require Import Parsers.Grammars.ABStar.

Require Import Parsers.BooleanRecognizer Parsers.BooleanRecognizerCorrect Parsers.Splitters.FirstChar Parsers.ContextFreeGrammarProperties.

Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.
Local Notation StringT := (StringWithSplitState string_stringlike (fun _ => True)).

Local Coercion StringT_of_string : string >-> StringWithSplitState.

Section on_ab_star.
  Definition parse (str : string) : bool
    := let data := ab_star_data in parse_nonterminal (G := ab_star_grammar) str ab_star_grammar.

  Local Notation correct_parse_T
    := ({ parse : string -> bool
                            & forall str,
                                (parse str -> parse_of_item string_stringlike ab_star_grammar str (NonTerminal _ ab_star_grammar))
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
                                (parse str -> parse_of_item string_stringlike ab_star_grammar' str (NonTerminal _ ab_star_grammar'))
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

  Definition simplified_parse' (str : string) : bool.
  Proof.
    pose (parse' str) as p.
    unfold parse', parse_nonterminal, parse_nonterminal_or_abort, parse_nonterminal_step, parse_productions, combine_sig in p.
    simpl in p.
  Abort.
End on_ab_star'.
