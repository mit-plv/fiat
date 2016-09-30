Require Import Coq.Strings.String Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Gensym.

Delimit Scope item_scope with item.
Bind Scope item_scope with item.
Delimit Scope production_scope with production.
Delimit Scope prod_assignment_scope with prod_assignment.
Bind Scope production_scope with production.
Delimit Scope productions_scope with productions.
Delimit Scope productions_assignment_scope with prods_assignment.
Bind Scope productions_scope with productions.
Delimit Scope grammar_scope with grammar.
Bind Scope grammar_scope with grammar.

(** [abstract] doesn't work in definitions *)
Class NoDupR {T} beq (ls : list T) := nodupr : uniquize beq ls = ls.
Hint Extern 5 (NoDupR _ _) => clear; (*abstract*) (vm_compute; reflexivity) : typeclass_instances.

Definition list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
  := fun nt
     => option_rect
          (fun _ => T)
          snd
          default
          (find (fun k => string_beq nt (fst k)) ls).

Record pregrammar Char :=
  {
    pregrammar_rproductions : list (string * rproductions Char);
    pregrammar_idata : interp_RCharExpr_data Char;
    pregrammar_rnonterminals : list string
    := map fst pregrammar_rproductions;
    rnonterminals_unique
    : NoDupR string_beq pregrammar_rnonterminals;
    RLookup_idx : nat -> rproductions Char
    := fun n => nth n (map snd pregrammar_rproductions) nil
  }.

Global Existing Instance pregrammar_idata.

Record pregrammar' (Char : Type) :=
  {
    pregrammar_productions :> list (string * productions Char);
    pregrammar_nonterminals : list string
    := map fst pregrammar_productions;
    invalid_nonterminal : string
    := gensym pregrammar_nonterminals;
    Lookup_idx : nat -> productions Char
    := fun n => nth n (map snd pregrammar_productions) nil;
    Lookup_string : string -> productions Char
    := list_to_productions nil pregrammar_productions;
    nonterminals_unique
    : NoDupR string_beq pregrammar_nonterminals
  }.

Global Arguments pregrammar_nonterminals / _ _.
Global Arguments Lookup_idx {_} !_ !_  / .
Global Arguments Lookup_string {_} !_ !_ / .

Existing Instance nonterminals_unique.
Arguments nonterminals_unique {_} _.

Definition pregrammar'_of_pregrammar {Char} (g : pregrammar Char) : pregrammar' Char.
Proof.
  eapply {| pregrammar_productions := List.map (fun xy => (fst xy, interp_rproductions (snd xy))) (pregrammar_rproductions g) |}.
  Grab Existential Variables.
  2:eapply (pregrammar_idata g). (* wheee, dependent subgoals in Coq 8.4 *)
  abstract (
      rewrite map_map; simpl;
      apply (rnonterminals_unique g)
    ).
Defined.

Coercion pregrammar'_of_pregrammar : pregrammar >-> pregrammar'.

Coercion grammar_of_pregrammar {Char} (g : pregrammar' Char) : grammar Char
  := {| Start_symbol := hd ""%string (pregrammar_nonterminals g);
        Lookup := Lookup_string g;
        Valid_nonterminals := (pregrammar_nonterminals g) |}.

Global Instance valid_nonterminals_unique {Char} {G : pregrammar' Char}
: NoDupR string_beq (Valid_nonterminals G)
  := nonterminals_unique _.

Definition list_to_grammar {T} (default : productions T) (ls : list (string * productions T)) : grammar T
  := {| Start_symbol := hd ""%string (map fst ls);
        Lookup := list_to_productions default ls;
        Valid_nonterminals := map fst ls |}.

Global Arguments list_to_grammar {_} _ _.
