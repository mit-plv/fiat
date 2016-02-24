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

  Fixpoint simple_parse_of_correct (str : String) (pats : productions Char)
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
    end
  with simple_parse_of_production_correct (str : String) (pat : production Char)
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
         end
  with simple_parse_of_item_correct (str : String) (it : item Char)
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

  (** The following lemma is probably important to connect the correctness principles, and should be straightforward, modulo some issues with Type vs Prop *)
  (* Lemma simple_parse_of_correct_correct (str : String) (pats : productions Char)
: inhabited (parse_of G str pats) <-> exists p, simple_parse_of_correct str pats p. *)
End correctness.
