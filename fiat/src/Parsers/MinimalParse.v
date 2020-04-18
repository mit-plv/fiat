(** * Definition of minimal parse trees *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.

  (** The [nonterminals_listT] is the current list of valid nonterminals to compare
      against; the extra [String] argument to some of these is the
      [String] we're using to do well-founded recursion, which the
      current [String] must be no longer than. *)

  Inductive minimal_parse_of
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      productions Char -> Type :=
  | MinParseHead : forall len0 valid str pat pats,
                     @minimal_parse_of_production len0 valid str pat
                     -> @minimal_parse_of len0 valid str (pat::pats)
  | MinParseTail : forall len0 valid str pat pats,
                     @minimal_parse_of len0 valid str pats
                     -> @minimal_parse_of len0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      production Char -> Type :=
  | MinParseProductionNil : forall len0 valid str,
                              length str = 0
                              -> @minimal_parse_of_production len0 valid str nil
  | MinParseProductionCons : forall len0 valid str n pat pats,
                               length str <= len0
                               -> @minimal_parse_of_item len0 valid (take n str) pat
                               -> @minimal_parse_of_production len0 valid (drop n str) pats
                               -> @minimal_parse_of_production len0 valid str (pat::pats)
  with minimal_parse_of_item
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      item Char -> Type :=
  | MinParseTerminal : forall len0 valid str ch P,
                         is_true (P ch)
                         -> str ~= [ ch ]
                         -> @minimal_parse_of_item len0 valid str (Terminal P)
  | MinParseNonTerminal
    : forall len0 valid str (nt : String.string),
        @minimal_parse_of_nonterminal len0 valid str nt
        -> @minimal_parse_of_item len0 valid str (NonTerminal nt)
  with minimal_parse_of_nonterminal
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      String.string -> Type :=
  | MinParseNonTerminalStrLt
    : forall len0 valid (nt : String.string) str,
        length str < len0
        -> is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)
        -> @minimal_parse_of (length str) initial_nonterminals_data str (Lookup G nt)
        -> @minimal_parse_of_nonterminal len0 valid str nt
  | MinParseNonTerminalStrEq
    : forall len0 str valid nonterminal,
        length str = len0
        -> is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal)
        -> is_valid_nonterminal valid (of_nonterminal nonterminal)
        -> @minimal_parse_of len0 (remove_nonterminal valid (of_nonterminal nonterminal)) str (Lookup G nonterminal)
        -> @minimal_parse_of_nonterminal len0 valid str nonterminal.

End cfg.
