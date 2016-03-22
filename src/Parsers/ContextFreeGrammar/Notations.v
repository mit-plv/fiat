(** * Convenience Notations for Describing Context Free Grammars *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.
Require Export Fiat.Parsers.ContextFreeGrammar.PreNotations.

Export Coq.Strings.Ascii.
Export Coq.Strings.String.
Export Fiat.Parsers.ContextFreeGrammar.Core.

(** ** Generic setup *)
(** We have various scopes and helper-functions behind the machinery
    of CFG notations. *)
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

Module opt'.
  Definition map {A B} := Eval compute in @List.map A B.
  Definition list_of_string := Eval compute in @StringOperations.list_of_string.
  Definition pred := Eval compute in pred.
  Definition length := Eval compute in String.length.
  Definition substring := Eval compute in substring.
End opt'.

(** single characters are terminals, anything wrapped with "'" is a
    string literal, everything else is a nonterminal *)
Coercion production_of_string (s : string) : production Ascii.ascii
  := match s with
       | EmptyString => nil
       | String.String ch EmptyString => (Terminal (ascii_beq ch))::nil
       | String.String "'" s'
         => match opt'.substring (opt'.pred (opt'.length s')) 1 s' with
            | String.String "'" EmptyString
              => opt'.map (fun ch => Terminal (ascii_beq ch))
                          (opt'.list_of_string (opt'.substring 0 (opt'.pred (opt'.length s')) s'))
            | _ => (NonTerminal s)::nil
            end
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

Definition char_test := Ascii.ascii -> bool.

Coercion char_to_test_eq (c : Ascii.ascii) : char_test
  := Equality.ascii_beq c.

Definition or_chars (c1 c2 : char_test) : char_test
  := fun c => (c1 c || c2 c)%bool.

Definition and_chars (c1 c2 : char_test) : char_test
  := fun c => (c1 c && c2 c)%bool.

Definition neg_chars (c1 : char_test) : char_test
  := fun c => negb (c1 c).

Coercion production_of_chartest (c : char_test) : production Ascii.ascii
  := (Terminal c :: nil)%list.

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

Global Arguments char_test / .
Global Arguments char_to_test_eq / .
Global Arguments or_chars / .
Global Arguments and_chars / .
Global Arguments neg_chars / .
Global Arguments production_of_chartest / .
Global Arguments production_of_string / .
Global Arguments magic_juxta_append_production / .
Global Arguments productions_of_production / .
Global Arguments magic_juxta_append_productions / .
Global Arguments opt.nat_of_ascii !_ / .

(** ** Notations *)

(** Use [||] to mean a choice, e.g., ["a" || "b"] in [char_scope] or
    [production_scope] (not [productions_scope]) means "a character
    which is either an 'a' or a 'b'."  In [productions_scope], it means
    "either one production, or another production". *)
Notation "p || p'" := (or_chars p%char p'%char) : char_scope.
Notation "p || p'" := ((p || p')%char : production _) : production_scope.
Notation "p && p'" := (and_chars p%char p'%char) : char_scope.
Notation "p && p'" := ((p && p')%char : production _) : production_scope.
Notation "p || p'" := (magic_juxta_append_productions p%productions p'%productions) : productions_scope.

(** Negation of terminals.  There's not yet support for inverting the
    sense of productions. *)
Notation "~ p" := (neg_chars p%char) : char_scope.
Notation "¬ p" := ((~p)%char) (at level 75, right associativity) : char_scope.
Notation "~ p" := ((~p)%char : production _) : productions_scope.
Notation "¬ p" := ((~p)%productions) (at level 75, right associativity) : productions_scope.

Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions _)%productions) (at level 100) : production_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_productions nil (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  ({| pregrammar_productions := (cons x%prod_assignment .. (cons y%prod_assignment nil) .. ) |}) : grammar_scope.

Local Open Scope string_scope.
Global Open Scope grammar_scope.
Global Open Scope string_scope.

Notation code_le ch ch' := (Compare_dec.leb (opt.nat_of_ascii ch) (opt.nat_of_ascii ch')).
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
Notation "'\n'" := LF : char_scope.
Notation "'\n'" := (String.String \n%char EmptyString) : string_scope.
Notation "'\r'" := CR : char_scope.
Notation "'\r'" := (String.String \r%char EmptyString) : string_scope.
Notation "'\t'" := TAB : char_scope.
Notation "'\t'" := (String.String \t%char EmptyString) : string_scope.
Notation "'[\s]'" := (\n || \r || " " || \t)%char : char_scope.
Notation "'[\s]'" := ([\s])%char : item_scope.
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

Declare Reduction grammar_red := cbv beta iota zeta delta [ascii_of_pos production_of_string magic_juxta_append_production magic_juxta_append_productions productions_of_production list_to_productions char_test char_to_test_eq or_chars and_chars neg_chars production_of_chartest ascii_of_nat ascii_of_pos ascii_of_N BinNat.N.of_nat shift BinPos.Pos.of_succ_nat BinPos.Pos.succ one zero opt'.map opt'.list_of_string opt'.pred opt'.length opt'.substring].

Create HintDb parser_sharpen_db discriminated.
Hint Unfold ascii_of_pos production_of_string magic_juxta_append_production magic_juxta_append_productions productions_of_production list_to_productions char_test char_to_test_eq or_chars and_chars neg_chars production_of_chartest ascii_of_nat ascii_of_pos ascii_of_N BinNat.N.of_nat shift BinPos.Pos.of_succ_nat BinPos.Pos.succ one zero opt.nat_of_ascii opt'.map opt'.list_of_string opt'.pred opt'.length opt'.substring : parser_sharpen_db.
