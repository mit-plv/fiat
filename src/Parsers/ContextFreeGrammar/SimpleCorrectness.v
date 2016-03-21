(** * Specification of what it means for a simple_parse_of to be correct *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.

(** We currently have two versions, one defined by [Fixpoint], and another as an inductive.  I suspect the fixpoint will be easier to reason with, but I leave both in for now in case this is not the case. *)

Section correctness.
  Context {Char} {HSLM} {HSL : @StringLike Char HSLM}.
  Context (G : grammar Char).

  (** First we write the inductive; it's simpler; we just copy [parse_of] *)
  Inductive simple_parse_of_correct_inductive (str : String) : productions Char -> simple_parse_of  Char -> Type :=
  | SimpleParseHeadCorrect : forall pat pats t, simple_parse_of_production_correct_inductive str pat t
                                              -> simple_parse_of_correct_inductive str (pat::pats) (SimpleParseHead t)
  | SimpleParseTailCorrect : forall pat pats t, simple_parse_of_correct_inductive str pats t
                                              -> simple_parse_of_correct_inductive str (pat::pats) (SimpleParseTail t)
  with simple_parse_of_production_correct_inductive (str : String) : production Char -> simple_parse_of_production Char -> Type :=
       | SimpleParseProductionNilCorrect : length str = 0 -> simple_parse_of_production_correct_inductive str nil SimpleParseProductionNil
       | SimpleParseProductionConsCorrect : forall n pat pats t t',
           simple_parse_of_item_correct_inductive (take n str) pat t
           -> simple_parse_of_production_correct_inductive (drop n str) pats t'
           -> simple_parse_of_production_correct_inductive str (pat::pats) (SimpleParseProductionCons t t')
  with simple_parse_of_item_correct_inductive (str : String) : item Char -> simple_parse_of_item Char -> Type :=
       | SimpleParseTerminalCorrect : forall ch P, is_true (P ch) -> is_true (str ~= [ ch ])%string_like -> simple_parse_of_item_correct_inductive str (Terminal P) (SimpleParseTerminal ch)
       | SimpleParseNonTerminalCorrect : forall nt t,
           List.In nt (Valid_nonterminals G)
           -> simple_parse_of_correct_inductive str (Lookup G nt) t
           -> simple_parse_of_item_correct_inductive str (NonTerminal nt) (SimpleParseNonTerminal nt t).

  Section bodies.
    Context (simple_parse_of_correct
             : forall (str : String) (pats : productions Char) (t : @simple_parse_of Char),
                Prop)
            (simple_parse_of_production_correct
             : forall (str : String) (pat : production Char) (t : @simple_parse_of_production Char),
                Prop)
            (simple_parse_of_item_correct
             : forall (str : String) (it : item Char) (t : @simple_parse_of_item Char),
                Prop).
    Definition simple_parse_of_correct_step
               (str : String) (pats : productions Char)
               (t : simple_parse_of) : Prop :=
      match t with
      | SimpleParseHead t'
        => match pats with
           | nil => False
           | pat'::pats' => simple_parse_of_production_correct str pat' t'
           end
      | SimpleParseTail t'
        => match pats with
           | nil => False
           | pat'::pats' => simple_parse_of_correct str pats' t'
           end
      end.
    Definition simple_parse_of_production_correct_step
               (str : String) (pat : production Char)
               (t : simple_parse_of_production) : Prop :=
      match t with
      | SimpleParseProductionNil
        => length str = 0 /\ pat = nil
      | SimpleParseProductionCons t' ts'
        => match pat with
           | nil => False
           | it::its
             => exists n, simple_parse_of_item_correct (take n str) it t'
                          /\ simple_parse_of_production_correct (drop n str) its ts'
           end
      end.
    Definition simple_parse_of_item_correct_step
               (str : String) (it : item Char)
               (t : simple_parse_of_item) : Prop :=
      match t with
      | SimpleParseTerminal ch
        => match it with
           | Terminal P => is_true (P ch && (str ~= [ ch ])%string_like)%bool
           | NonTerminal _ => False
           end
      | SimpleParseNonTerminal nt x
        => match it with
           | Terminal _ => False
           | NonTerminal nt' => nt = nt'
                                /\ List.In nt (Valid_nonterminals G)
                                /\ simple_parse_of_correct str (Lookup G nt) x
           end
      end.
  End bodies.

  Fixpoint simple_parse_of_correct str pats t
    := @simple_parse_of_correct_step
         simple_parse_of_correct simple_parse_of_production_correct
         str pats t
  with simple_parse_of_production_correct str pat t
       := @simple_parse_of_production_correct_step
            simple_parse_of_production_correct simple_parse_of_item_correct
            str pat t
  with simple_parse_of_item_correct str it t
       := @simple_parse_of_item_correct_step
            simple_parse_of_correct
            str it t.
End correctness.

Arguments simple_parse_of_correct_step _ _ _ _ _ _ !_ / .
Arguments simple_parse_of_production_correct_step _ _ _ _ _ _ _ !_ / .
Arguments simple_parse_of_item_correct_step _ _ _ _ _ _ _ !_ / .

Ltac unfold_simple_parse_of_correct_constr term
  := lazymatch term with
    | @simple_parse_of_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y
      => constr:(@simple_parse_of_correct_step
                   Char HSLM
                   (@simple_parse_of_correct Char HSLM HSL G)
                   (@simple_parse_of_production_correct Char HSLM HSL G)
                   str x y)
    | @simple_parse_of_production_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y
      => constr:(@simple_parse_of_production_correct_step
                   Char HSLM HSL
                   (@simple_parse_of_production_correct Char HSLM HSL G)
                   (@simple_parse_of_item_correct Char HSLM HSL G)
                   str x y)
    | @simple_parse_of_item_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y
      => constr:(@simple_parse_of_item_correct_step
                   Char HSLM HSL G
                   (@simple_parse_of_correct Char HSLM HSL G)
                   str x y)
    end.
Ltac simpl_simple_parse_of_correct :=
  repeat match goal with
         | [ |- context[@simple_parse_of_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y] ]
           => let term := constr:(@simple_parse_of_correct Char HSLM HSL G str x y) in
              let term' := unfold_simple_parse_of_correct_constr term in
              change term with term'; simpl @simple_parse_of_correct_step
         | [ |- context[@simple_parse_of_production_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y] ]
           => let term := constr:(@simple_parse_of_production_correct Char HSLM HSL G str x y) in
              let term' := unfold_simple_parse_of_correct_constr term in
              change term with term'; simpl @simple_parse_of_production_correct_step
         | [ |- context[@simple_parse_of_item_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y] ]
           => let term := constr:(@simple_parse_of_item_correct Char HSLM HSL G str x y) in
              let term' := unfold_simple_parse_of_correct_constr term in
              change term with term'; simpl @simple_parse_of_item_correct_step
         | [ H : context[@simple_parse_of_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y] |- _ ]
           => let term := constr:(@simple_parse_of_correct Char HSLM HSL G str x y) in
              let term' := unfold_simple_parse_of_correct_constr term in
              change term with term' in H; simpl @simple_parse_of_correct_step in H
         | [ H : context[@simple_parse_of_production_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y] |- _ ]
           => let term := constr:(@simple_parse_of_production_correct Char HSLM HSL G str x y) in
              let term' := unfold_simple_parse_of_correct_constr term in
              change term with term' in H; simpl @simple_parse_of_production_correct_step in H
         | [ H : context[@simple_parse_of_item_correct ?Char ?HSLM ?HSL ?G ?str ?x ?y] |- _ ]
           => let term := constr:(@simple_parse_of_item_correct Char HSLM HSL G str x y) in
              let term' := unfold_simple_parse_of_correct_constr term in
              change term with term' in H; simpl @simple_parse_of_item_correct_step in H
         end.
