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

Definition list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
  := fun nt
     => option_rect
          (fun _ => T)
          (fun idx => nth idx (map snd (uniquize (fun x y => string_beq (fst x) (fst y)) ls)) default)
          default
          (first_index_error (string_beq nt) (uniquize string_beq (map fst ls))).

Definition list_to_grammar {T} (default : productions T) (ls : list (string * productions T)) : grammar T
  := {| Start_symbol := hd ""%string (uniquize string_beq (map fst ls));
        Lookup := list_to_productions default ls;
        Valid_nonterminals := uniquize string_beq (map fst ls) |}.

Global Arguments nat_of_ascii !_ / .
Global Arguments Compare_dec.leb !_ !_ / .
Global Arguments BinPos.Pos.to_nat !_ / .
