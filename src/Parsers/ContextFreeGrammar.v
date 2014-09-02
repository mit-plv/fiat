(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List.

Set Implicit Arguments.

Reserved Notation "[ x ]" (at level 0).

Section cfg.
  Variable CharType : Type.

  Section definitions.
    (** Something is string-like (for a given type of characters) if
        it has an associative concatenation operation and decidable
        equality. *)
    Record string_like :=
      {
        String :> Type;
        Singleton :> CharType -> String where "[ x ]" := (Singleton x);
        Empty : String;
        Concat : String -> String -> String where "x ++ y" := (Concat x y);
        dec_eq : forall x y : String, {x = y} + {x <> y};
        Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z);
        LeftId : forall x, Empty ++ x = x;
        RightId : forall x, x ++ Empty = x
      }.

    (** An [item] is the basic building block of a context-free
        grammar; it is either a terminal ([CharType]-literal) or a
        nonterminal of a given name. *)
    Inductive item :=
    | Terminal (_ : CharType)
    | NonTerminal (name : string).

    (** A [nonterminal] is a list of possible patterns; a pattern is a
        list of items.  A string matches a pattern if it can be broken
        up into components that match the relevant element of the
        pattern. *)
    Definition pattern := list item.
    Definition nonterminal := list pattern.

    (** A [grammar] consists of a [nonterminal] to match a string
        against, and a function mapping names to non-terminals. *)
    Record grammar :=
      {
        Top_name :> string;
        Lookup :> string -> nonterminal;
        Top :> nonterminal := Lookup Top_name
      }.
  End definitions.

  Local Notation "[ x ]" := (@Singleton _ x).
  Local Infix "++" := (@Concat _).

  Section parse.
    Variable String : string_like.
    Variable G : grammar.
    (** A parse of a string into a [nonterminal] is a pattern in that
        non-terminal, together with a list of substrings which cover
        the original string, each of which is a parse of the relevant
        component of the pattern. *)
    Inductive is_parse_of : String -> nonterminal -> Type :=
    | ParseHead : forall str pat pats, is_parse_of_pattern str pat
                                       -> is_parse_of str (pat::pats)
    | ParseTail : forall str pat pats, is_parse_of str pats
                                       -> is_parse_of str (pat::pats)
    with is_parse_of_pattern : String -> pattern -> Type :=
    | ParsePatternNil : is_parse_of_pattern (Empty _) nil
    | ParsePatternCons : forall str pat strs pats,
                           is_parse_of_item str pat
                           -> is_parse_of_pattern strs pats
                           -> is_parse_of_pattern (str ++ strs) (pat::pats)
    with is_parse_of_item : String -> item -> Type :=
    | ParseTerminal : forall x, is_parse_of_item [ x ] (Terminal x)
    | ParseNonTerminal : forall name str, is_parse_of str (Lookup G name)
                                          -> is_parse_of_item str (NonTerminal name).
  End parse.

  Definition is_parse_of_grammar (String : string_like) (str : String) (G : grammar) :=
    is_parse_of String G str G.
End cfg.

Definition string_stringlike : string_like Ascii.ascii.
Proof.
  refine {| String := string;
            Singleton := fun x => String.String x EmptyString;
            Empty := EmptyString;
            Concat := append;
            dec_eq := string_dec |};
  let x := fresh "x" in
  let IHx := fresh "IHx" in
  intro x; induction x as [|? ? IHx]; try reflexivity; simpl;
  intros;
  f_equal;
  auto.
Qed.

Section examples.
  Section generic.
    Variable CharType : Type.
    Variable String : string_like CharType.

    Definition trivial_grammar : grammar CharType :=
      {| Top_name := "";
         Lookup := fun _ => nil::nil |}.

    Definition trivial_grammar_parses_empty_string : is_parse_of_grammar _ (Empty String) trivial_grammar.
    Proof.
      hnf.
      simpl.
      apply ParseHead.
      constructor.
    Qed.
  End generic.
End examples.
