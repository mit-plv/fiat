(** * Reflective notations for context free grammars *)
Require Import Coq.Strings.Ascii.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.Equality.

Global Arguments N_of_ascii !_ / .
Global Arguments Compare_dec.leb !_ !_ / .
Global Arguments BinNat.N.leb !_ !_ / .
Global Arguments BinNat.N.compare !_ !_ / .
Global Arguments BinPos.Pos.to_nat !_ / .

Module opt.
  Local Arguments N_of_ascii / _ .
  Local Arguments N_of_digits / _ .
  Local Arguments BinNat.N.add !_ !_ / .
  Local Arguments BinNat.N.mul !_ !_ / .
  Definition N_of_ascii ch
    := Eval simpl in N_of_ascii ch.
End opt.

Global Arguments opt.N_of_ascii !_ / .

Delimit Scope rchar_scope with rchar.

Section syntax.
  Context {Char : Type}.

  Inductive RCharExpr :=
  | rbeq (ch : Char)
  | ror (_ _ : RCharExpr)
  | rand (_ _ : RCharExpr)
  | rneg (_ : RCharExpr)
  | rcode_le_than (code : BinNums.N)
  | rcode_ge_than (code : BinNums.N).

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

Scheme Equality for RCharExpr.
Scheme Equality for ritem.
Global Instance RCharExpr_BoolDecR {Char} {Char_beq : BoolDecR Char} : BoolDecR (@RCharExpr Char)
  := RCharExpr_beq Char_beq.
Global Instance RCharExpr_BoolDec_bl {Char} {Char_beq : BoolDecR Char} {Char_bl : BoolDec_bl eq} : BoolDec_bl (@eq (@RCharExpr Char))
  := internal_RCharExpr_dec_bl Char_beq Char_bl.
Global Instance RCharExpr_BoolDec_lb {Char} {Char_beq : BoolDecR Char} {Char_lb : BoolDec_lb eq} : BoolDec_lb (@eq (@RCharExpr Char))
  := internal_RCharExpr_dec_lb Char_beq Char_lb.
Global Instance ritem_BoolDecR {Char} {Char_beq : BoolDecR Char} : BoolDecR (@ritem Char)
  := ritem_beq Char_beq.
Global Instance ritem_BoolDec_bl {Char} {Char_beq : BoolDecR Char} {Char_bl : BoolDec_bl eq} : BoolDec_bl (@eq (@ritem Char))
  := internal_ritem_dec_bl Char_beq Char_bl.
Global Instance ritem_BoolDec_lb {Char} {Char_beq : BoolDecR Char} {Char_lb : BoolDec_lb eq} : BoolDec_lb (@eq (@ritem Char))
  := internal_ritem_dec_lb Char_beq Char_lb.

Global Arguments RCharExpr : clear implicits.
Global Arguments ritem : clear implicits.
Global Arguments rproduction : clear implicits.
Global Arguments rproductions : clear implicits.
Global Arguments rbeq {Char%type_scope} _.
Global Arguments ror {Char%type_scope} (_ _)%rchar_scope.
Global Arguments rand {Char%type_scope} (_ _)%rchar_scope.
Global Arguments rneg {Char%type_scope} (_)%rchar_scope.
Global Arguments rcode_le_than {Char%type_scope} (_)%N_scope.
Global Arguments rcode_ge_than {Char%type_scope} (_)%N_scope.

Infix "||" := ror : rchar_scope.
Infix "&&" := rand : rchar_scope.
Notation "~ x" := (rneg x) : rchar_scope.

Section semantics.
  Context {Char : Type}.

  Class interp_RCharExpr_data :=
    { irbeq : Char -> Char -> bool;
      irN_of : Char -> BinNums.N }.

  Context {idata : interp_RCharExpr_data}.

  Fixpoint interp_RCharExpr (expr : RCharExpr Char) : Char -> bool
    := match expr with
       | rbeq ch => irbeq ch
       | ror a b => fun ch => interp_RCharExpr a ch || interp_RCharExpr b ch
       | rand a b => fun ch => interp_RCharExpr a ch && interp_RCharExpr b ch
       | rneg x => fun ch => negb (interp_RCharExpr x ch)
       | rcode_le_than code => fun ch => BinNat.N.leb (irN_of ch) code
       | rcode_ge_than code => fun ch => BinNat.N.leb code (irN_of ch)
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
       irN_of := opt.N_of_ascii }.

(** Alternative that isn't higher order *)
Definition char_at_matches_interp {Char} {HSLM : StringLikeMin Char}
           {_ : interp_RCharExpr_data Char} n str P
  := char_at_matches n str (interp_RCharExpr P).
