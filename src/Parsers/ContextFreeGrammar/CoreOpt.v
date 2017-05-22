(** * Optimized nonreflective forms for context free grammars *)
Require Import Coq.Strings.Ascii.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.

Module opt.
  Section syntax.
    Context {Char : Type}.
    Inductive item :=
    | Terminal (_ : Char -> bool)
    | NonTerminal (_ : nat).

    Definition production := list item.
    Definition productions := list production.
  End syntax.

  Scheme Minimality for item Sort Type.
  Scheme Minimality for item Sort Set.
  Scheme Minimality for item Sort Prop.

  Global Arguments item : clear implicits.
  Global Arguments production : clear implicits.
  Global Arguments productions : clear implicits.

  Section semantics.
    Context {Char : Type}.

    Class interp_item_data :=
      { inonterminal_names : list String.string;
        iinvalid_nonterminal : String.string }.

    Context {iidata : interp_item_data}.
    Definition compile_nonterminal nt
      := List.first_index_default (string_beq nt) (List.length inonterminal_names) inonterminal_names.
    Definition compile_item (expr : Core.item Char) : opt.item Char
      := match expr with
         | Core.Terminal ch => Terminal ch
         | Core.NonTerminal nt => NonTerminal (compile_nonterminal nt)
         end.
    Definition interp_nonterminal nt
      := List.nth nt inonterminal_names iinvalid_nonterminal.
    Definition interp_item (expr : opt.item Char) : Core.item Char
      := match expr with
         | Terminal ch => Core.Terminal ch
         | NonTerminal nt
           => Core.NonTerminal (interp_nonterminal nt)
         end.

    Definition compile_production (expr : Core.production Char) : opt.production Char
      := List.map compile_item expr.
    Definition interp_production (expr : opt.production Char) : Core.production Char
      := List.map interp_item expr.

    Definition compile_productions (expr : Core.productions Char) : opt.productions Char
      := List.map compile_production expr.
    Definition interp_productions (expr : opt.productions Char) : Core.productions Char
      := List.map interp_production expr.
  End semantics.

  Global Arguments interp_item_data : clear implicits.
End opt.
