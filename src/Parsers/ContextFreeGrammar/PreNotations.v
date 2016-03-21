Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Gensym.

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

Record pregrammar (Char : Type) :=
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

Global Arguments pregrammar_nonterminals / .
Global Arguments Lookup_idx {_} !_ !_  / .
Global Arguments Lookup_string {_} !_ !_ / .

Existing Instance nonterminals_unique.
Arguments nonterminals_unique {_} _.

Coercion grammar_of_pregrammar {Char} (g : pregrammar Char) : grammar Char
  := {| Start_symbol := hd ""%string (pregrammar_nonterminals g);
        Lookup := Lookup_string g;
        Valid_nonterminals := (pregrammar_nonterminals g) |}.

Global Instance valid_nonterminals_unique {Char} {G : pregrammar Char}
: NoDupR string_beq (Valid_nonterminals G)
  := nonterminals_unique _.

Definition list_to_grammar {T} (default : productions T) (ls : list (string * productions T)) : grammar T
  := {| Start_symbol := hd ""%string (map fst ls);
        Lookup := list_to_productions default ls;
        Valid_nonterminals := map fst ls |}.

Global Arguments list_to_grammar {_} _ _.
Global Arguments nat_of_ascii !_ / .
Global Arguments Compare_dec.leb !_ !_ / .
Global Arguments BinPos.Pos.to_nat !_ / .

(** Variant of [nat_of_ascii] that will extract more cleanly, because
    it doesn't depend on various other constants (only inductives) *)
(** Keep this outside the module so it doesn't get extracted. *)
Definition nat_of_ascii_sig ch : { n : nat | n = nat_of_ascii ch }.
Proof.
  unfold nat_of_ascii.
  unfold N_of_ascii, N_of_digits.
  eexists.
  refine (_ : (let (a0, a1, a2, a3, a4, a5, a6, a7) := ch in _) = _).
  destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
  repeat rewrite ?Nnat.N2Nat.inj_add, ?Nnat.N2Nat.inj_mul.
  repeat match goal with
           | [ |- context[BinNat.N.to_nat (if ?b then ?x else ?y)] ]
             => replace (BinNat.N.to_nat (if b then x else y))
                with (if b then BinNat.N.to_nat x else BinNat.N.to_nat y)
               by (destruct b; reflexivity)
         end.
  simpl @BinNat.N.to_nat.
  rewrite Mult.mult_0_r, Plus.plus_0_r.
  reflexivity.
Defined.

Module opt.
  Definition nat_of_ascii ch
    := Eval cbv beta iota zeta delta [proj1_sig nat_of_ascii_sig] in
        proj1_sig (nat_of_ascii_sig ch).
End opt.

Global Arguments opt.nat_of_ascii !_ / .
