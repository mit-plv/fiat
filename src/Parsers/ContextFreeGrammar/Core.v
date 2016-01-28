(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Export Fiat.Parsers.StringLike.Core.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char : Type}.

  Section definitions.
    (** An [item] is the basic building block of a context-free
        grammar; it is either a terminal (a set of [Char]-literal
        options) or a nonterminal ([string]). *)
    Inductive item :=
    | Terminal (_ : Char -> bool)
    | NonTerminal (_ : string).

    (** A [productions] is a list of possible [production]s; a
        [production] is a list of [item]s.  A string matches a
        [production] if it can be broken up into components that match
        the relevant element of the [production]. *)
    Definition production := list item.
    Definition productions := list production.

    (** A [grammar] consists of [productions] to match a string
        against, and a function mapping names to [productions]. *)
    Record grammar :=
      {
        Start_symbol :> string;
        Lookup :> string -> productions;
        Start_productions :> productions := Lookup Start_symbol;
        Valid_nonterminals : list string;
        Valid_productions : list productions := map Lookup Valid_nonterminals
      }.
  End definitions.

  Section parse.
    Context {HSLM} {HSL : @StringLike Char HSLM}.
    Variable G : grammar.
    (** A parse of a string into [productions] is a [production] in
        that list, together with a list of substrings which cover the
        original string, each of which is a parse of the relevant
        component of the [production]. *)
    Inductive parse_of (str : String) : productions -> Type :=
    | ParseHead : forall pat pats, parse_of_production str pat
                                   -> parse_of str (pat::pats)
    | ParseTail : forall pat pats, parse_of str pats
                                   -> parse_of str (pat::pats)
    with parse_of_production (str : String) : production -> Type :=
    | ParseProductionNil : length str = 0 -> parse_of_production str nil
    | ParseProductionCons : forall n pat pats,
                              parse_of_item (take n str) pat
                              -> parse_of_production (drop n str) pats
                              -> parse_of_production str (pat::pats)
    with parse_of_item (str : String) : item -> Type :=
    | ParseTerminal : forall ch P, is_true (P ch) -> is_true (str ~= [ ch ]) -> parse_of_item str (Terminal P)
    | ParseNonTerminal : forall nt,
                           List.In nt (Valid_nonterminals G)
                           -> parse_of str (Lookup G nt)
                           -> parse_of_item str (NonTerminal nt).
  End parse.

  Definition parse_of_grammar {HSLM} {HSL : @StringLike Char HSLM} (str : String) (G : grammar) :=
    parse_of G str G.
End cfg.

Arguments item _ : clear implicits.
Arguments production _ : clear implicits.
Arguments productions _ : clear implicits.
Arguments grammar _ : clear implicits.

(** A production is reachable if it is the tail of a production
    associated to a valid nonterminal. *)
Definition production_is_reachable {Char} (G : grammar Char) (p : production Char)
: Prop
  := exists nt prefix,
       List.In nt (Valid_nonterminals G)
       /\ List.In
            (prefix ++ p)
            (Lookup G nt).
