(** * Reflective notations for context free grammars *)
Require Import Coq.Strings.Ascii.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.Equality.

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

Delimit Scope rchar_scope with rchar.

Section syntax.
  Context {Char : Type}.

  Inductive RCharExpr :=
  | rbeq (ch : Char)
  | ror (_ _ : RCharExpr)
  | rand (_ _ : RCharExpr)
  | rneg (_ : RCharExpr)
  | rcode_le_than (code : nat)
  | rcode_ge_than (code : nat).

  Bind Scope rchar_scope with RCharExpr.

  Inductive ritem :=
  | RTerminal (_ : RCharExpr)
  | RNonTerminal (_ : String.string).

  Definition rproduction := list ritem.
  Definition rproductions := list rproduction.
End syntax.

Scheme Minimality for ritem Sort Type.
Scheme Minimality for ritem Sort Set.
Scheme Minimality for ritem Sort Prop.

Global Arguments RCharExpr : clear implicits.
Global Arguments ritem : clear implicits.
Global Arguments rproduction : clear implicits.
Global Arguments rproductions : clear implicits.
Global Arguments rbeq {Char%type_scope} _.
Global Arguments ror {Char%type_scope} (_ _)%rchar_scope.
Global Arguments rand {Char%type_scope} (_ _)%rchar_scope.
Global Arguments rneg {Char%type_scope} (_)%rchar_scope.
Global Arguments rcode_le_than {Char%type_scope} (_)%nat_scope.
Global Arguments rcode_ge_than {Char%type_scope} (_)%nat_scope.

Infix "||" := ror : rchar_scope.
Infix "&&" := rand : rchar_scope.
Notation "~ x" := (rneg x) : rchar_scope.

Section semantics.
  Context {Char : Type}.

  Class interp_RCharExpr_data :=
    { irbeq : Char -> Char -> bool;
      irnat_of : Char -> nat }.

  Context {idata : interp_RCharExpr_data}.

  Fixpoint interp_RCharExpr (expr : RCharExpr Char) : Char -> bool
    := match expr with
       | rbeq ch => irbeq ch
       | ror a b => fun ch => interp_RCharExpr a ch || interp_RCharExpr b ch
       | rand a b => fun ch => interp_RCharExpr a ch && interp_RCharExpr b ch
       | rneg x => fun ch => negb (interp_RCharExpr x ch)
       | rcode_le_than code => fun ch => Compare_dec.leb (irnat_of ch) code
       | rcode_ge_than code => fun ch => Compare_dec.leb code (irnat_of ch)
       end%bool.

  (*Global Coercion interp_RCharExpr : RCharExpr >-> Funclass.*)

  Definition interp_ritem (expr : ritem Char) : item Char
    := match expr with
       | RTerminal x => Terminal (interp_RCharExpr x)
       | RNonTerminal x => NonTerminal x
       end.

  Definition interp_rproduction (expr : rproduction Char) : production Char
    := List.map interp_ritem expr.

  Definition interp_rproductions (expr : rproductions Char) : productions Char
    := List.map interp_rproduction expr.
End semantics.

Global Arguments interp_RCharExpr_data : clear implicits.

Global Instance ascii_interp_RCharExpr_data : interp_RCharExpr_data Ascii.ascii
  := { irbeq := Equality.ascii_beq;
       irnat_of := opt.nat_of_ascii }.
