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
        RightId : forall x, x ++ Empty = x;
        Length_correct : forall s1 s2, Length s1 + Length s2 = Length (s1 ++ s2);
        Length_Empty : Length Empty = 0;
        Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty
      }.

    Bind Scope string_like_scope with String.

    (** An [item] is the basic building block of a context-free
        grammar; it is either a terminal ([CharType]-literal) or a
        nonterminal of a given name. *)
    Inductive item :=
    | Terminal (_ : CharType)
    | NonTerminal (name : string).

    (** A [productions] is a list of possible [production]s; a
        [production] is a list of [item]s.  A string matches a
        [production] if it can be broken up into components that match
        the relevant element of the [production]. *)
    Definition production := list item.
    Definition productions := list production.

    Definition productions_dec (CharType_eq_dec : forall x y : CharType, {x = y} + {x <> y})
               (x y : productions) : {x = y} + {x <> y}.
    Proof.
      repeat (apply list_eq_dec; intros);
      decide equality.
      apply string_dec.
    Defined.

    (** A [grammar] consists of [productions] to match a string
        against, and a function mapping names to [productions]. *)
    (** TODO(jgross): also include list of valid starting non-terminals, for convenience and notation *)
    (** TODO(jgross): look up notations for specifying these nicely *)
    Record grammar :=
      {
        Top_name :> string; (** TODO: look up standard name for this (maybe initial? maybe starting?) *)
        Lookup :> string -> productions;
        Top :> productions := Lookup Top_name
      }.
  End definitions.

  Local Notation "[[ x ]]" := (@Singleton _ x) : string_like_scope.
  Local Infix "++" := (@Concat _).

  Section parse.
    Variable String : string_like.
    Variable G : grammar.
    (** A parse of a string into [productions] is a [production] in
        that list, together with a list of substrings which cover the
        original string, each of which is a parse of the relevant
        component of the [production]. *)
    Inductive parse_of : String -> productions -> Type :=
    | ParseHead : forall str pat pats, parse_of_production str pat
                                       -> parse_of str (pat::pats)
    | ParseTail : forall str pat pats, parse_of str pats
                                       -> parse_of str (pat::pats)
    with parse_of_production : String -> production -> Type :=
    | ParseProductionNil : parse_of_production (Empty _) nil
    | ParseProductionCons : forall str pat strs pats,
                           parse_of_item str pat
                           -> parse_of_production strs pats
                           -> parse_of_production (str ++ strs) (pat::pats)
    with parse_of_item : String -> item -> Type :=
    | ParseTerminal : forall x, parse_of_item [[ x ]]%string_like (Terminal x)
    | ParseNonTerminal : forall name str, parse_of str (Lookup G name)
                                          -> parse_of_item str (NonTerminal name).

    Definition ParseProductionSingleton str it (p : parse_of_item str it) : parse_of_production str [ it ].
    Proof.
      rewrite <- (RightId _ str).
      constructor; assumption || constructor.
    Defined.

    Definition ParseProductionApp str1 str2 p1 p2 (pop1 : parse_of_production str1 p1) (pop2 : parse_of_production str2 p2)
    : parse_of_production (str1 ++ str2) (p1 ++ p2)%list.
    Proof.
      induction pop1; simpl.
      { rewrite LeftId; assumption. }
      { rewrite Associativity.
        constructor; assumption. }
    Defined.

    Definition ParseApp str1 str2 p1 p2 (po1 : parse_of str1 [ p1 ]) (po2 : parse_of str2 [ p2 ])
    : parse_of (str1 ++ str2) [ (p1 ++ p2)%list ].
    Proof.
      inversion_clear po1; inversion_clear po2;
      try match goal with
            | [ H : parse_of _ [] |- _ ] => exfalso; revert H; clear; intro H; abstract inversion H
          end.
      { constructor. apply ParseProductionApp; assumption. }
    Defined.
  End parse.

  Definition parse_of_grammar (String : string_like) (str : String) (G : grammar) :=
    parse_of String G str G.
End cfg.

Arguments parse_of _%type_scope _ _ _%string_like _.
Arguments parse_of_item _%type_scope _ _ _%string_like _.
Arguments parse_of_production _%type_scope _ _ _%string_like _.
Arguments parse_of_grammar _%type_scope _ _%string_like _.
Arguments Concat _%type_scope _ (_ _)%string_like.
Arguments bool_eq _%type_scope _ (_ _)%string_like.

Notation "[[ x ]]" := (@Singleton _ _ x) : string_like_scope.
Infix "++" := (@Concat _ _) : string_like_scope.
Infix "=s" := (@bool_eq _ _) (at level 70, right associativity) : string_like_scope.

Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (NPeano.Nat.neq_succ_0 _ H) end.

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
        | intros; split; congruence
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
