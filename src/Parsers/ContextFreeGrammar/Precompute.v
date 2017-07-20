Require Import Coq.Strings.String.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.

Module opt.
  Section syntax.
    Context {T : Type}.

    Inductive item :=
    | Terminal (_ : T)
    | NonTerminal (nt : String.string) (_ : nat).

    Definition production := list item.
    Definition productions := list production.
  End syntax.

  Global Arguments item : clear implicits.
  Global Arguments production : clear implicits.
  Global Arguments productions : clear implicits.

  Section semantics.
    Context {Char : Type} {T : Type}.

    Class compile_item_data :=
      { on_terminal : (Char -> bool) -> T;
        nonterminal_names : list String.string;
        invalid_nonterminal : String.string }.

    Context {cidata : compile_item_data}.
    Definition compile_nonterminal nt
      := List.first_index_default (string_beq nt) (List.length nonterminal_names) nonterminal_names.
    Definition compile_item (expr : Core.item Char) : opt.item T
      := match expr with
         | Core.Terminal ch => Terminal (on_terminal ch)
         | Core.NonTerminal nt => NonTerminal nt (compile_nonterminal nt)
         end.

    Definition compile_production (expr : Core.production Char) : opt.production T
      := List.map compile_item expr.

    Definition compile_productions (expr : Core.productions Char) : opt.productions T
      := List.map compile_production expr.
  End semantics.

  Global Arguments compile_item_data : clear implicits.
End opt.
