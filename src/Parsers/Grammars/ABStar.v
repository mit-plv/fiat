(** * Definition of grammar for regular expression [(ab)*] *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar ADTSynthesis.Parsers.ContextFreeGrammarNotations.

Set Implicit Arguments.

Section ab_star.
  Local Open Scope string_scope.

  Definition ab_star_grammar : grammar Ascii.ascii :=
    {| Start_symbol := "(ab)*";
       Lookup := [[[ ("(ab)*" ::== << nil
                                     | $< "a"%char $ "b"%char $ "(ab)*" >$ >> ) ]]]%prods_assignment;
       Valid_nonterminals := ("(ab)*"::nil)%string |}.

  Definition ab_star_grammar' : grammar Ascii.ascii :=
    {| Start_symbol := "(ab)*";
       Lookup := fun _ => nil::(Terminal "a"%char::Terminal "b"%char::NonTerminal _ "(ab)*"%string::nil)::nil;
       Valid_nonterminals := ("(ab)*"::nil)%string |}.
End ab_star.

Create HintDb cfg discriminated.
Hint Constructors parse_of parse_of_production parse_of_item : cfg.
Hint Resolve ParseProductionSingleton ParseProductionApp ParseApp : cfg.

Section tests.
  Example ab_star_parses_empty : parse_of_grammar string_stringlike (Empty _) ab_star_grammar.
  Proof.
    hnf; simpl.
    repeat constructor.
  Defined.

  Example ab_star_parses_ab : parse_of_grammar string_stringlike "ab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    constructor (constructor); simpl.
    apply ParseProductionCons with (str := "a"%string) (strs := "b"%string).
    { refine (ParseTerminal _ _ _). }
    { apply ParseProductionCons with (str := "b"%string) (strs := ""%string).
      { refine (ParseTerminal _ _ _). }
      { apply ParseProductionCons with (str := ""%string) (strs := ""%string);
        repeat (simpl; constructor). } }
  Defined.

  Example ab_star_parses_abab : parse_of_grammar string_stringlike "abab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    constructor (constructor); simpl.
    apply ParseProductionCons with (str := "a"%string) (strs := "bab"%string).
    { refine (ParseTerminal _ _ _). }
    { apply ParseProductionCons with (str := "b"%string) (strs := "ab"%string).
      { refine (ParseTerminal _ _ _). }
      { apply ParseProductionCons with (str := "ab"%string) (strs := ""%string).
        { constructor.
          apply ab_star_parses_ab. }
        { constructor. } } }
  Defined.
End tests.
