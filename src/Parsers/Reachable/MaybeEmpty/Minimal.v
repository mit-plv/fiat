(** * Definition of minimal parse trees *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Import Fiat.Parsers.BaseTypes.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}.

  Inductive minimal_maybe_empty_productions : nonterminals_listT -> productions Char -> Type :=
  | MinMaybeEmptyHead : forall valid pat pats, minimal_maybe_empty_production valid pat
                                               -> minimal_maybe_empty_productions valid (pat::pats)
  | MinMaybeEmptyTail : forall valid pat pats, minimal_maybe_empty_productions valid pats
                                               -> minimal_maybe_empty_productions valid (pat::pats)
  with minimal_maybe_empty_production : nonterminals_listT -> production Char -> Type :=
  | MinMaybeEmptyProductionNil : forall valid, minimal_maybe_empty_production valid nil
  | MinMaybeEmptyProductionCons : forall valid it its, minimal_maybe_empty_item valid it
                                                       -> minimal_maybe_empty_production valid its
                                                       -> minimal_maybe_empty_production valid (it::its)
  with minimal_maybe_empty_item : nonterminals_listT -> item Char -> Type :=
  | MinMaybeEmptyNonTerminal : forall valid nt, is_valid_nonterminal valid nt
                                                -> minimal_maybe_empty_productions (remove_nonterminal valid nt) (Lookup G nt)
                                                -> minimal_maybe_empty_item valid (NonTerminal nt).

End cfg.
