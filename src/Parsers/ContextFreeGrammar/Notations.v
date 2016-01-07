Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.
Require Export Fiat.Parsers.ContextFreeGrammar.PreNotations.

Export Coq.Strings.Ascii.
Export Coq.Strings.String.
Export Fiat.Parsers.ContextFreeGrammar.Core.

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

(** single characters are terminals, everything else is a nonterminal *)
Coercion production_of_string (s : string) : production Ascii.ascii
  := match s with
       | EmptyString => nil
       | String.String ch EmptyString => (Terminal (ascii_beq ch))::nil
       | _ => (NonTerminal s)::nil
     end.

Global Arguments production_of_string / .

(** juxtaposition of productions should yield concatenation *)
Definition magic_juxta_append_production {T} (p ps : production T) : production T
  := Eval compute in p ++ ps.
Coercion magic_juxta_append_production : production >-> Funclass.

Coercion productions_of_production {T} (p : production T) : productions T
  := p::nil.

Definition magic_juxta_append_productions {T} (p ps : productions T) : productions T
  := Eval compute in p ++ ps.

Notation "p || p'" := (magic_juxta_append_productions p%productions p'%productions) : productions_scope.

Definition char_test := Ascii.ascii -> bool.

Coercion char_to_test_eq (c : Ascii.ascii) : char_test
  := Equality.ascii_beq c.

Definition or_chars (c1 c2 : char_test) : char_test
  := fun c => (c1 c || c2 c)%bool.

Definition neg_chars (c1 : char_test) : char_test
  := fun c => negb (c1 c).

(*Definition magic_juxta_append_from_char_test (ch : char_test) (p : production ascii) : production ascii
  := (Terminal ch)::p.
Coercion magic_juxta_append_from_char_test : char_test >-> Funclass.*)

Notation "p || p'" := (or_chars p%char p'%char) : char_scope.
Notation "p || p'" := ((p || p')%char : production _) : production_scope.

Notation "~ p" := (neg_chars p%char) : char_scope.
Notation "¬ p" := ((~p)%char) (at level 75, right associativity) : char_scope.
Notation "~ p" := ((~p)%char : production _) : productions_scope.
Notation "¬ p" := ((~p)%productions) (at level 75, right associativity) : productions_scope.

Coercion production_of_chartest (c : char_test) : production Ascii.ascii
  := (Terminal c :: nil)%list.

Global Arguments char_test / .
Global Arguments char_to_test_eq / .
Global Arguments or_chars / .
Global Arguments neg_chars / .
Global Arguments production_of_chartest / .
Global Arguments production_of_string / .
Global Arguments magic_juxta_append_production / .
Global Arguments productions_of_production / .
Global Arguments magic_juxta_append_productions / .
(*Global Arguments magic_juxta_append_from_char_test / .*)

Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions _)%productions) (at level 100) : production_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_productions nil (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  ({| pregrammar_productions := (cons x%prod_assignment .. (cons y%prod_assignment nil) .. ) |}) : grammar_scope.

Local Open Scope string_scope.
Global Open Scope grammar_scope.
Global Open Scope string_scope.

Notation code_le ch ch' := (Compare_dec.leb (nat_of_ascii ch) (nat_of_ascii ch')).
Notation code_in_range ch ch_low ch_high := (code_le ch_low ch && code_le ch ch_high)%bool.

Notation "'[0-9]'" := (Terminal (fun ch => code_in_range ch "0" "9")) : item_scope.
Notation "'[0-9]'" := (([0-9]%item::nil) : production _) : production_scope.
Notation "'[0-9]'" := ([0-9]%production) : productions_scope.
Notation "'[A-Z]'" := (Terminal (fun ch => code_in_range ch "A" "Z")) : item_scope.
Notation "'[A-Z]'" := (([A-Z]%item::nil) : production _) : production_scope.
Notation "'[A-Z]'" := ([A-Z]%production) : productions_scope.
Notation "'[a-z]'" := (Terminal (fun ch => code_in_range ch "a" "z")) : item_scope.
Notation "'[a-z]'" := (([a-z]%item::nil) : production _) : production_scope.
Notation "'[a-z]'" := ([a-z]%production) : productions_scope.

Local Notation LF := (ascii_of_nat 10).
Local Notation CR := (ascii_of_nat 13).
Local Notation TAB := (ascii_of_nat 9).
Local Notation SPACE := " "%char.

(** Notation for whitespace: space, tab, line feed, carriage return *)
Notation "'[\s]'" := (LF || CR || SPACE || TAB)%char : item_scope.
Notation "'[\s]'" := (([\s]%item) : production _) : production_scope.
Notation "'[\s]'" := [\s]%production : productions_scope.
Notation "'[0-9a-fA-F]'" := (Terminal (fun ch => code_in_range ch "0" "9"
                                                 || code_in_range ch "a" "f"
                                                 || code_in_range ch "A" "F")%bool) : item_scope.
Notation "'[0-9a-fA-F]'" := (([0-9a-fA-F]%item::nil)%list : production _) : production_scope.
Notation "'[0-9a-fA-F]'" := [0-9a-fA-F]%production : productions_scope.
Notation "'[1-9]'" := (Terminal (fun ch => code_in_range ch "1" "9")) : item_scope.
Notation "'[1-9]'" := (([1-9]%item::nil)%list : production _) : production_scope.
Notation "'[1-9]'" := ([1-9]%production) : productions_scope.

Global Arguments Equality.ascii_beq !_ !_.
Global Arguments Equality.string_beq !_ !_.
Global Arguments ascii_of_nat !_ / .
Global Arguments ascii_of_pos !_ / .

Declare Reduction grammar_red := cbv beta iota zeta delta [ascii_of_pos production_of_string magic_juxta_append_production magic_juxta_append_productions productions_of_production list_to_productions char_test char_to_test_eq or_chars neg_chars production_of_chartest ascii_of_nat ascii_of_pos ascii_of_N BinNat.N.of_nat shift BinPos.Pos.of_succ_nat BinPos.Pos.succ one zero].

Create HintDb parser_sharpen_db discriminated.
Hint Unfold ascii_of_pos production_of_string magic_juxta_append_production magic_juxta_append_productions productions_of_production list_to_productions char_test char_to_test_eq or_chars neg_chars production_of_chartest ascii_of_nat ascii_of_pos ascii_of_N BinNat.N.of_nat shift BinPos.Pos.of_succ_nat BinPos.Pos.succ one zero : parser_sharpen_db.
