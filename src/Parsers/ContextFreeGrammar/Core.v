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

    (** A simple parse tree is a simply typed version of the above *)
    Inductive simple_parse_of :=
    | SimpleParseHead : simple_parse_of_production -> simple_parse_of
    | SimpleParseTail : simple_parse_of -> simple_parse_of
    with simple_parse_of_production :=
    | SimpleParseProductionNil : simple_parse_of_production
    | SimpleParseProductionCons
      : simple_parse_of_item
        -> simple_parse_of_production
        -> simple_parse_of_production
    with simple_parse_of_item :=
    | SimpleParseTerminal : Char -> simple_parse_of_item
    | SimpleParseNonTerminal : forall nt : string,
                                 simple_parse_of
                                 -> simple_parse_of_item.
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

Delimit Scope simple_parse_of_scope with simple_parse_of.
Delimit Scope simple_parse_of_production_scope with simple_parse_of_production.
Delimit Scope simple_parse_of_item_scope with simple_parse_of_item.
Bind Scope simple_parse_of_scope with simple_parse_of.
Bind Scope simple_parse_of_production_scope with simple_parse_of_production.
Bind Scope simple_parse_of_item_scope with simple_parse_of_item.

Arguments SimpleParseHead _%type _%simple_parse_of_production.
Arguments SimpleParseTail _%type _%simple_parse_of.
Arguments SimpleParseProductionNil _%type.
Arguments SimpleParseProductionCons _%type _%simple_parse_of_item _%simple_parse_of_production.
Arguments SimpleParseNonTerminal _%type _%string _%simple_parse_of.

Arguments simple_parse_of {_}, _.
Arguments simple_parse_of_production {_}, _.
Arguments simple_parse_of_item {_}, _.

Infix "::" := SimpleParseProductionCons : simple_parse_of_production_scope.
Notation "[ ]" := SimpleParseProductionNil : simple_parse_of_production_scope.
