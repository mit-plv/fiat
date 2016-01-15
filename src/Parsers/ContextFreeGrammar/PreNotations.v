Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.

Export Coq.Strings.Ascii.
Export Coq.Strings.String.
Export Fiat.Parsers.ContextFreeGrammar.Core.

Global Arguments nat_of_ascii !_ / .
Global Arguments Compare_dec.leb !_ !_ / .
Global Arguments BinPos.Pos.to_nat !_ / .

Delimit Scope item_scope with item.
Bind Scope item_scope with item.
Delimit Scope production_scope with production.
Delimit Scope production_assignment_scope with prod_assignment.
Bind Scope production_scope with production.
Delimit Scope productions_scope with productions.
Delimit Scope productions_assignment_scope with prods_assignment.
Bind Scope productions_scope with productions.
Delimit Scope grammar_scope with grammar.
Bind Scope grammar_scope with grammar.

Class NoDupR {T} beq (ls : list T) := nodupr : uniquize beq ls = ls.
Hint Extern 1 (NoDupR _ _) => clear; abstract (vm_compute; reflexivity) : typeclass_instances.

Definition list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
  := fun nt
     => option_rect
          (fun _ => T)
          snd
          default
          (find (fun k => string_beq nt (fst k)) ls).

Definition list_to_grammar {T} (default : productions T) (ls : list (string * productions T)) : grammar T
  := {| Start_symbol := hd ""%string (map fst ls);
        Lookup := list_to_productions default ls;
        Valid_nonterminals := map fst ls |}.

Global Arguments list_to_grammar {_} _ _.
Global Arguments nat_of_ascii !_ / .
Global Arguments Compare_dec.leb !_ !_ / .
Global Arguments BinPos.Pos.to_nat !_ / .
