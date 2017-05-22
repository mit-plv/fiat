(** * Optimized reflective forms for context free grammars *)
Require Import Coq.Strings.Ascii.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.

Module opt.
  Section syntax.
    Context {Char : Type}.
    Inductive ritem :=
    | RTerminal (_ : RCharExpr Char)
    | RNonTerminal (_ : nat).

    Definition rproduction := list ritem.
    Definition rproductions := list rproduction.
  End syntax.

  Scheme Minimality for ritem Sort Type.
  Scheme Minimality for ritem Sort Set.
  Scheme Minimality for ritem Sort Prop.

  Scheme Equality for ritem.

  Global Instance ritem_BoolDecR {Char} {Char_beq : BoolDecR Char} : BoolDecR (@ritem Char)
    := ritem_beq Char_beq.
  Global Instance ritem_BoolDec_bl {Char} {Char_beq : BoolDecR Char} {Char_bl : BoolDec_bl eq} : BoolDec_bl (@eq (@ritem Char))
    := internal_ritem_dec_bl0 Char_beq Char_bl.
  Global Instance ritem_BoolDec_lb {Char} {Char_beq : BoolDecR Char} {Char_lb : BoolDec_lb eq} : BoolDec_lb (@eq (@ritem Char))
    := internal_ritem_dec_lb0 Char_beq Char_lb.

  Global Arguments ritem : clear implicits.
  Global Arguments rproduction : clear implicits.
  Global Arguments rproductions : clear implicits.

  Section semantics.
    Context {Char : Type}.

    Class interp_ritem_data :=
      { irnonterminal_names : list String.string;
        irinvalid_nonterminal : String.string }.

    Context {iidata : interp_ritem_data}.
    Definition compile_nonterminal nt
      := List.first_index_default (string_beq nt) (List.length irnonterminal_names) irnonterminal_names.
    Definition compile_ritem (expr : Reflective.ritem Char) : opt.ritem Char
      := match expr with
         | Reflective.RTerminal ch => RTerminal ch
         | Reflective.RNonTerminal nt => RNonTerminal (compile_nonterminal nt)
         end.
    Definition interp_nonterminal nt
      := List.nth nt irnonterminal_names irinvalid_nonterminal.
    Definition interp_ritem (expr : opt.ritem Char) : Reflective.ritem Char
      := match expr with
         | RTerminal ch => Reflective.RTerminal ch
         | RNonTerminal nt
           => Reflective.RNonTerminal (interp_nonterminal nt)
         end.

    Definition compile_rproduction (expr : Reflective.rproduction Char) : opt.rproduction Char
      := List.map compile_ritem expr.
    Definition interp_rproduction (expr : opt.rproduction Char) : Reflective.rproduction Char
      := List.map interp_ritem expr.

    Definition compile_rproductions (expr : Reflective.rproductions Char) : opt.rproductions Char
      := List.map compile_rproduction expr.
    Definition interp_rproductions (expr : opt.rproductions Char) : Reflective.rproductions Char
      := List.map interp_rproduction expr.
  End semantics.

  Global Arguments interp_ritem_data : clear implicits.
End opt.
