(** * Definition of grammar for regular expression [(ab)*] *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar ADTSynthesis.Parsers.ContextFreeGrammarNotations.

Set Implicit Arguments.

Section ab_star.
  Local Open Scope string_scope.

  Definition ab_star_grammar : grammar string :=
    {| Start_symbol := "(ab)*";
       Lookup := [[[ ("(ab)*" ::== << nil
                                     | $< "a"%char $ "b"%char $ "(ab)*" >$ >> ) ]]]%prods_assignment;
       Valid_nonterminals := ("(ab)*"::nil)%string |}.

  Definition ab_star_grammar' : grammar string :=
    {| Start_symbol := "(ab)*";
       Lookup := fun _ => nil::(Terminal "a"%char::Terminal "b"%char::NonTerminal "(ab)*"%string::nil)::nil;
       Valid_nonterminals := ("(ab)*"::nil)%string |}.
End ab_star.

Create HintDb cfg discriminated.
Hint Constructors parse_of parse_of_production parse_of_item : cfg.

Section tests.
  Example ab_star_parses_empty : parse_of_grammar ""%string ab_star_grammar.
  Proof.
    hnf; simpl.
    repeat constructor.
  Defined.

  Example ab_star_parses_ab : parse_of_grammar "ab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 1); simpl.
    { refine (ParseTerminal _ _ _ _); reflexivity. }
    { apply ParseProductionCons with (n := 1); simpl.
      { refine (ParseTerminal _ _ _ _); reflexivity. }
      { apply ParseProductionCons with (n := 1); simpl;
        repeat (simpl; constructor). } }
  Defined.

  Example ab_star_parses_abab : parse_of_grammar "abab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 1); simpl.
    { refine (ParseTerminal _ _ _ _); reflexivity. }
    { apply ParseProductionCons with (n := 1); simpl.
      { refine (ParseTerminal _ _ _ _); reflexivity. }
      { apply ParseProductionCons with (n := 2); simpl;
        try solve [ repeat (simpl; constructor) ].
        constructor.
        apply ab_star_parses_ab. } }
  Defined.
End tests.
