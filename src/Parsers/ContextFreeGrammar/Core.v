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
        grammar; it is either a terminal ([CharType]-literal) or a
        nonterminal ([string]). *)
    Inductive item :=
    | Terminal (_ : Char)
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
    Context {HSL : StringLike Char}.
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
    | ParseTerminal : forall ch, is_true (str ~= [ ch ]) -> parse_of_item str (Terminal ch)
    | ParseNonTerminal : forall nt, parse_of str (Lookup G nt)
                                    -> parse_of_item str (NonTerminal nt).
  End parse.

  Definition parse_of_grammar {HSL : StringLike Char} (str : String) (G : grammar) :=
    parse_of G str G.
End cfg.

Arguments item _ : clear implicits.
Arguments production _ : clear implicits.
Arguments productions _ : clear implicits.
Arguments grammar _ : clear implicits.
