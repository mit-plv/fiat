(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLikeMin Char} {predata : @parser_computational_predataT Char} (G : grammar Char).

  Context (valid : nonterminals_listT).

  (** Relation defining if a productions is maybe empty *)
  Inductive maybe_empty_productions : productions Char -> Type :=
  | MaybeEmptyHead : forall pat pats, maybe_empty_production pat
                                      -> maybe_empty_productions (pat::pats)
  | MaybeEmptyTail : forall pat pats, maybe_empty_productions pats
                                      -> maybe_empty_productions (pat::pats)
  with maybe_empty_production : production Char -> Type :=
  | MaybeEmptyProductionNil : maybe_empty_production nil
  | MaybeEmptyProductionCons : forall it its, maybe_empty_item it
                                              -> maybe_empty_production its
                                              -> maybe_empty_production (it::its)
  with maybe_empty_item : item Char -> Type :=
  | MaybeEmptyNonTerminal : forall nt, is_valid_nonterminal valid (of_nonterminal nt)
                                      -> maybe_empty_productions (Lookup G nt)
                                      -> maybe_empty_item (NonTerminal nt).
End cfg.
