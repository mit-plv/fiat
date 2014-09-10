(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.

Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

Delimit Scope string_like_scope with string_like.

Section cfg.
  Variable CharType : Type.

  Section definitions.
    (** Something is string-like (for a given type of characters) if
        it has an associative concatenation operation and decidable
        equality. *)
    Record string_like :=
      {
        String :> Type;
        Singleton : CharType -> String where "[ x ]" := (Singleton x);
        Empty : String;
        Concat : String -> String -> String where "x ++ y" := (Concat x y);
        bool_eq : String -> String -> bool;
        bool_eq_correct : forall x y : String, bool_eq x y = true <-> x = y;
        Length : String -> nat;
        Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z);
        LeftId : forall x, Empty ++ x = x;
        RightId : forall x, x ++ Empty = x
      }.

    Bind Scope string_like_scope with String.

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

    Definition nonterminal_dec (CharType_eq_dec : forall x y : CharType, {x = y} + {x <> y})
               (x y : nonterminal) : {x = y} + {x <> y}.
    Proof.
      repeat (apply list_eq_dec; intros);
      decide equality.
      apply string_dec.
    Defined.

    (** A [grammar] consists of a [nonterminal] to match a string
        against, and a function mapping names to non-terminals. *)
    Record grammar :=
      {
        Top_name :> string;
        Lookup :> string -> nonterminal;
        Top :> nonterminal := Lookup Top_name
      }.
  End definitions.

  Local Notation "[[ x ]]" := (@Singleton _ x) : string_like_scope.
  Local Infix "++" := (@Concat _).

  Section parse.
    Variable String : string_like.
    Variable G : grammar.
    (** A parse of a string into a [nonterminal] is a pattern in that
        non-terminal, together with a list of substrings which cover
        the original string, each of which is a parse of the relevant
        component of the pattern. *)
    Inductive parse_of : String -> nonterminal -> Type :=
    | ParseHead : forall str pat pats, parse_of_pattern str pat
                                       -> parse_of str (pat::pats)
    | ParseTail : forall str pat pats, parse_of str pats
                                       -> parse_of str (pat::pats)
    with parse_of_pattern : String -> pattern -> Type :=
    | ParsePatternNil : parse_of_pattern (Empty _) nil
    | ParsePatternCons : forall str pat strs pats,
                           parse_of_item str pat
                           -> parse_of_pattern strs pats
                           -> parse_of_pattern (str ++ strs) (pat::pats)
    with parse_of_item : String -> item -> Type :=
    | ParseTerminal : forall x, parse_of_item [[ x ]]%string_like (Terminal x)
    | ParseNonTerminal : forall name str, parse_of str (Lookup G name)
                                          -> parse_of_item str (NonTerminal name).

    Definition ParsePatternSingleton str it (p : parse_of_item str it) : parse_of_pattern str [ it ].
    Proof.
      rewrite <- (RightId _ str).
      constructor; assumption || constructor.
    Defined.
  End parse.

  Definition parse_of_grammar (String : string_like) (str : String) (G : grammar) :=
    parse_of String G str G.
End cfg.

Arguments parse_of _%type_scope _ _ _%string_like _.
Arguments parse_of_item _%type_scope _ _ _%string_like _.
Arguments parse_of_pattern _%type_scope _ _ _%string_like _.
Arguments parse_of_grammar _%type_scope _ _%string_like _.
Arguments Concat _%type_scope _ (_ _)%string_like.
Arguments bool_eq _%type_scope _ (_ _)%string_like.

Notation "[[ x ]]" := (@Singleton _ _ x) : string_like_scope.
Infix "++" := (@Concat _ _) : string_like_scope.
Infix "=s" := (@bool_eq _ _) (at level 70, right associativity) : string_like_scope.

Definition string_stringlike : string_like Ascii.ascii.
Proof.
  refine {| String := string;
            Singleton := fun x => String.String x EmptyString;
            Empty := EmptyString;
            Concat := append;
            Length := String.length;
            bool_eq x y := if string_dec x y then true else false |};
  solve [ abstract (let x := fresh "x" in
                    let IHx := fresh "IHx" in
                    intro x; induction x as [|? ? IHx]; try reflexivity; simpl;
                    intros;
                    f_equal;
                    auto)
        | intros; edestruct string_dec; split; congruence ].
Defined.

Section examples.
  Section generic.
    Variable CharType : Type.
    Variable String : string_like CharType.

    Definition trivial_grammar : grammar CharType :=
      {| Top_name := "";
         Lookup := fun _ => nil::nil |}.

    Definition trivial_grammar_parses_empty_string : parse_of_grammar _ (Empty String) trivial_grammar.
    Proof.
      hnf.
      simpl.
      apply ParseHead.
      constructor.
    Qed.
  End generic.
End examples.
