(** * Convenience Notations for Describing Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Export Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Export Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Common.Notations.

Export Coq.Strings.Ascii.
Export Coq.Strings.String.
Export Fiat.Parsers.ContextFreeGrammar.Core.

(** ** Generic setup *)
(** We have various scopes and helper-functions behind the machinery
    of CFG notations. *)
Delimit Scope item_scope with item.
Bind Scope item_scope with item.
Bind Scope item_scope with ritem.
Delimit Scope production_scope with production.
Delimit Scope production_with_action_scope with production_with_action.
Delimit Scope prod_assignment_scope with prod_assignment.
Delimit Scope prod_with_action_assignment_scope with prod_with_action_assignment.
Bind Scope production_scope with production.
Bind Scope production_scope with rproduction.
Bind Scope production_with_action_scope with rproduction_with_action.
Delimit Scope productions_scope with productions.
Delimit Scope productions_assignment_scope with productions_assignment.
Delimit Scope productions_with_actions_scope with productions_with_actions.
Delimit Scope productions_with_actions_assignment_scope with productions_with_actions_assignment.
Bind Scope productions_with_action_scope with rproductions_with_actions.
Bind Scope productions_scope with productions.
Bind Scope productions_scope with rproductions.
Delimit Scope grammar_scope with grammar.
Delimit Scope grammar_with_actions_scope with grammar_with_actions.
Bind Scope grammar_scope with pregrammar.
Bind Scope grammar_scope with grammar.
Bind Scope grammar_with_actions_scope with pregrammar_with_actions.

Module opt'.
  Definition map {A B} := Eval compute in @List.map A B.
  Definition list_of_string := Eval compute in @StringOperations.list_of_string.
  Definition pred := Eval compute in pred.
  Definition length := Eval compute in String.length.
  Definition substring := Eval compute in substring.
End opt'.

(** single characters are terminals, anything wrapped with "'" is a
    string literal, everything else is a nonterminal *)
Coercion rproduction_of_string (s : string) : rproduction Ascii.ascii
  := match s with
       | EmptyString => nil
       | String.String ch EmptyString => (RTerminal (rbeq ch))::nil
       | String.String "'" s'
         => match opt'.substring (opt'.pred (opt'.length s')) 1 s' with
            | String.String "'" EmptyString
              => opt'.map (fun ch => RTerminal (rbeq ch))
                          (opt'.list_of_string (opt'.substring 0 (opt'.pred (opt'.length s')) s'))
            | _ => (RNonTerminal s)::nil
            end
       | _ => (RNonTerminal s)::nil
     end.

Global Arguments rproduction_of_string / _.

(** juxtaposition of productions should yield concatenation *)
Definition magic_juxta_append_rproduction {Char} (p ps : rproduction Char) : rproduction Char
  := Eval compute in p ++ ps.
Coercion magic_juxta_append_rproduction : rproduction >-> Funclass.

Definition combine_rproduction_with_action {T Char} (pat : rproduction Char) (act : action_of_rproduction T pat)
  : rproduction_with_action Char T
  := existT _ pat act.

Coercion rproductions_of_rproduction {Char} (p : rproduction Char) : rproductions Char
  := p::nil.
Coercion rproductions_with_action_of_rproduction_with_action {Char T} (p : rproduction_with_action Char T) : rproductions_with_actions Char T
  := p::nil.

Definition magic_juxta_append_rproductions {Char} (p ps : rproductions Char) : rproductions Char
  := Eval compute in p ++ ps.
Definition magic_juxta_append_rproductions_with_actions {Char T} (p ps : rproductions_with_actions Char T) : rproductions_with_actions Char T
  := Eval compute in p ++ ps.

Coercion char_to_test_eq (c : Ascii.ascii) : RCharExpr Ascii.ascii
  := rbeq c.

Coercion rproduction_of_RCharExpr {Char} (c : RCharExpr Char) : rproduction Char
  := (RTerminal c :: nil)%list.

Global Arguments char_to_test_eq / _.
Global Arguments rproduction_of_RCharExpr / _ _.
Global Arguments rproduction_of_string / _.
Global Arguments magic_juxta_append_rproduction / _ _ _.
Global Arguments rproductions_of_rproduction / _ _.
Global Arguments rproductions_with_action_of_rproduction_with_action / _ _ _.
Global Arguments magic_juxta_append_rproductions / _ _ _.
Global Arguments magic_juxta_append_rproductions_with_actions / _ _ _ _.

(** ** Notations *)

(** Use [||] to mean a choice, e.g., ["a" || "b"] in [char_scope] or
    [production_scope] (not [productions_scope]) means "a character
    which is either an 'a' or a 'b'."  In [productions_scope], it means
    "either one production, or another production". *)
Notation "p || p'" := (ror p%char p'%char) : char_scope.
Notation "p || p'" := ((p || p')%char : rproduction Ascii.ascii) : production_scope.
Notation "p && p'" := (rand p%char p'%char) : char_scope.
Notation "p && p'" := ((p && p')%char : rproduction Ascii.ascii) : production_scope.
Notation "p || p'" := (magic_juxta_append_rproductions p%productions p'%productions) : productions_scope.
Notation "p || p'" := (magic_juxta_append_rproductions_with_actions p%productions_with_actions p'%productions_with_actions) : productions_with_actions_scope.
Notation "p <{< act >}>" := (combine_rproduction_with_action p%production act) : production_with_action_scope.
Notation "p <{< act >}>" := (combine_rproduction_with_action p%production act) : productions_with_actions_scope.

(** Negation of terminals.  There's not yet support for inverting the
    sense of productions. *)
Notation "~ p" := (rneg p%char) : char_scope.
Notation "¬ p" := ((~p)%char) (at level 75, right associativity) : char_scope.
Notation "~ p" := ((~p)%char : rproduction Ascii.ascii) : productions_scope.
Notation "¬ p" := ((~p)%productions) (at level 75, right associativity) : productions_scope.

Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : rproductions Ascii.ascii)%productions) (at level 100) : prod_assignment_scope.
Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : rproductions_with_actions Ascii.ascii _)%productions_with_actions) (at level 100) : prod_with_action_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_productions nil (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_productions nil (cons x%prod_with_action_assignment .. (cons y%prod_with_action_assignment nil) .. )) : productions_with_actions_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  ({| pregrammar_rproductions := (cons x%prod_assignment .. (cons y%prod_assignment nil) .. ) |}) : grammar_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  ({| pregrammar_arproductions := (cons x%prod_with_action_assignment .. (cons y%prod_with_action_assignment nil) .. ) |}) : grammar_with_actions_scope.

Local Open Scope string_scope.
Global Open Scope grammar_scope.
Global Open Scope string_scope.

Notation code_in_range ch_low ch_high := (rand (rcode_ge_than (opt.N_of_ascii ch_low)) (rcode_le_than (opt.N_of_ascii ch_high))).

Notation "'[0-9]'" := (RTerminal (code_in_range "0" "9")) : item_scope.
Notation "'[0-9]'" := (([0-9]%item::nil) : rproduction Ascii.ascii) : production_scope.
Notation "'[0-9]'" := ([0-9]%production) : productions_scope.
Notation "'[A-Z]'" := (RTerminal (code_in_range "A" "Z")) : item_scope.
Notation "'[A-Z]'" := (([A-Z]%item::nil) : rproduction Ascii.ascii) : production_scope.
Notation "'[A-Z]'" := ([A-Z]%production) : productions_scope.
Notation "'[a-z]'" := (RTerminal (code_in_range "a" "z")) : item_scope.
Notation "'[a-z]'" := (([a-z]%item::nil) : rproduction Ascii.ascii) : production_scope.
Notation "'[a-z]'" := ([a-z]%production) : productions_scope.

Local Notation LF := (ascii_of_N 10).
Local Notation CR := (ascii_of_N 13).
Local Notation TAB := (ascii_of_N 9).
Local Notation SPACE := " "%char.

(** Notation for whitespace: space, tab, line feed, carriage return *)
Notation "'\n'" := LF : char_scope.
Notation "'\n'" := (String.String \n%char EmptyString) : string_scope.
Notation "'\r'" := CR : char_scope.
Notation "'\r'" := (String.String \r%char EmptyString) : string_scope.
Notation "'\t'" := TAB : char_scope.
Notation "'\t'" := (String.String \t%char EmptyString) : string_scope.
Notation "'[\s]'" := (\n || \r || " " || \t)%char : char_scope.
Notation "'[\s]'" := ([\s])%char : item_scope.
Notation "'[\s]'" := (([\s]%item) : rproduction Ascii.ascii) : production_scope.
Notation "'[\s]'" := [\s]%production : productions_scope.
Notation "'[0-9a-fA-F]'" := (RTerminal (code_in_range "0" "9"
                                        || code_in_range "a" "f"
                                        || code_in_range "A" "F")%rchar) : item_scope.
Notation "'[0-9a-fA-F]'" := (([0-9a-fA-F]%item::nil)%list : rproduction Ascii.ascii) : production_scope.
Notation "'[0-9a-fA-F]'" := [0-9a-fA-F]%production : productions_scope.
Notation "'[1-9]'" := (RTerminal (code_in_range "1" "9")) : item_scope.
Notation "'[1-9]'" := (([1-9]%item::nil)%list : rproduction Ascii.ascii) : production_scope.
Notation "'[1-9]'" := ([1-9]%production) : productions_scope.

Global Arguments Equality.ascii_beq !_ !_.
Global Arguments Equality.string_beq !_ !_.
Global Arguments ascii_of_nat !_ / .
Global Arguments ascii_of_N !_ / .
Global Arguments ascii_of_pos !_ / .

Definition parseAscii_as_nat (v : ascii) : nat
  := Nat.modulo (1 + nat_of_ascii v - nat_of_ascii "1"%char) 10.

Declare Reduction grammar_red := cbv beta iota zeta delta [ascii_of_pos rproduction_of_string magic_juxta_append_rproduction magic_juxta_append_rproductions rproductions_of_rproduction list_to_productions char_to_test_eq rproduction_of_RCharExpr ascii_of_nat ascii_of_pos ascii_of_N BinNat.N.of_nat shift BinPos.Pos.of_succ_nat BinPos.Pos.succ one zero opt'.map opt'.list_of_string opt'.pred opt'.length opt'.substring interp_RCharExpr interp_ritem interp_rproduction interp_rproductions irbeq irN_of ascii_interp_RCharExpr_data parseAscii_as_nat magic_juxta_append_rproductions_with_actions combine_rproduction_with_action].

Create HintDb parser_sharpen_db discriminated.
Hint Unfold ascii_of_pos rproduction_of_string magic_juxta_append_rproduction magic_juxta_append_rproductions rproductions_of_rproduction list_to_productions char_to_test_eq rproduction_of_RCharExpr ascii_of_nat ascii_of_pos ascii_of_N BinNat.N.of_nat shift BinPos.Pos.of_succ_nat BinPos.Pos.succ one zero opt'.map opt'.list_of_string opt'.pred opt'.length opt'.substring interp_RCharExpr interp_ritem interp_rproduction interp_rproductions irbeq irN_of ascii_interp_RCharExpr_data parseAscii_as_nat magic_juxta_append_rproductions_with_actions combine_rproduction_with_action : parser_sharpen_db.
