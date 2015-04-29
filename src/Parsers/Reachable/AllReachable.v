(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT} (G : grammar Char).

  Context (ch : Char).

  (** Relation defining if a character is reachable *)
  Inductive reachable_from_productions : productions Char -> Prop :=
  | ReachableHead : forall pat pats, reachable_from_production pat
                                     -> reachable_from_productions (pat::pats)
  | ReachableTail : forall pat pats, reachable_from_productions pats
                                     -> reachable_from_productions (pat::pats)
  with reachable_from_production : production Char -> Type :=
  | ReachableProductionHead : forall it its, reachable_from_item it
                                             -> reachable_from_production (it::its)
  | ReachableProductionTail : forall it its, reachable_from_production its
                                             -> reachable_from_production (it::its)
  with reachable_from_item : item Char -> Prop :=
  | ReachableTerminal : reachable_from_item (Terminal ch)
  | ReachableNonTerminal : forall nt, is_valid_nonterminal initial_nonterminals_data nt
                                      -> reachable_from_productions (Lookup G nt)
                                      -> reachable_from_item (NonTerminal nt).
End cfg.
