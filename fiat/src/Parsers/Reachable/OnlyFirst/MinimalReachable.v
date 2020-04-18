(** * Definition of minimal parse trees *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Minimal.
Require Import Fiat.Parsers.BaseTypes.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Context (valid0 : nonterminals_listT) (ch : Char).

  Inductive minimal_reachable_from_productions : nonterminals_listT -> productions Char -> Type :=
  | MinReachableHead : forall valid pat pats, minimal_reachable_from_production valid pat
                                              -> minimal_reachable_from_productions valid (pat::pats)
  | MinReachableTail : forall valid pat pats, minimal_reachable_from_productions valid pats
                                              -> minimal_reachable_from_productions valid (pat::pats)
  with minimal_reachable_from_production : nonterminals_listT -> production Char -> Type :=
  | MinReachableProductionHead : forall valid it its, minimal_reachable_from_item valid it
                                                      -> minimal_reachable_from_production valid (it::its)
  | MinReachableProductionTail : forall valid it its, minimal_maybe_empty_item (G := G) valid0 it
                                                      -> minimal_reachable_from_production valid its
                                                      -> minimal_reachable_from_production valid (it::its)
  with minimal_reachable_from_item : nonterminals_listT -> item Char -> Type :=
  | MinReachableTerminal : forall valid P, is_true (P ch) -> minimal_reachable_from_item valid (Terminal P)
  | MinReachableNonTerminal : forall valid nt, is_valid_nonterminal valid (of_nonterminal nt)
                                               -> minimal_reachable_from_productions (remove_nonterminal valid (of_nonterminal nt)) (Lookup G nt)
                                               -> minimal_reachable_from_item valid (NonTerminal nt).

End cfg.
