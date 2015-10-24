(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT} (G : grammar Char).

  Context (ch : Char) (valid : nonterminals_listT).

  (** Relation defining if a character is reachable *)
  Inductive reachable_from_productions : productions Char -> Type :=
  | ReachableHead : forall pat pats, reachable_from_production pat
                                     -> reachable_from_productions (pat::pats)
  | ReachableTail : forall pat pats, reachable_from_productions pats
                                     -> reachable_from_productions (pat::pats)
  with reachable_from_production : production Char -> Type :=
  | ReachableProductionHead : forall it its, reachable_from_item it
                                             -> reachable_from_production (it::its)
  | ReachableProductionTail : forall it its, maybe_empty_item G valid it
                                             -> reachable_from_production its
                                             -> reachable_from_production (it::its)
  with reachable_from_item : item Char -> Type :=
  | ReachableTerminal : reachable_from_item (Terminal ch)
  | ReachableNonTerminal : forall nt, is_valid_nonterminal valid nt
                                      -> reachable_from_productions (Lookup G nt)
                                      -> reachable_from_item (NonTerminal nt).
End cfg.
