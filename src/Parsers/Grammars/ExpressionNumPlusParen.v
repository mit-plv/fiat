(** * Definition of grammar for expressions involving parentheses and plus *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar ADTSynthesis.Parsers.ContextFreeGrammarNotations.

Set Implicit Arguments.

Section num_plus_paren.
  Local Open Scope string_scope.
  Local Open Scope grammar_scope.

  Definition plus_expr_grammar : grammar string :=
    [[[ ("expr" ::== << $< "pexpr" >$
                      | $< "pexpr" $ #"+" $ "expr" >$ >>);;
        ("pexpr" ::== << $< "number" >$
                       | $< #"(" $ "expr" $ #")" >$ >>);;
        ("digit" ::== << $< #"0" >$ | $< #"1" >$ | $< #"2" >$ | $< #"3" >$ | $< #"4" >$ | $< #"5" >$ | $< #"6" >$ | $< #"7" >$ | $< #"8" >$ | $< #"9" >$ >>);;
        ("number" ::== << $< "digit" >$ | $< "digit" $ "number" >$ >>)
    ]]].
End num_plus_paren.

Section tests.
  Local Arguments append : simpl never.

  Local Ltac fin :=
    repeat first [ idtac;
                   (lazymatch goal with
                   | [ |- parse_of_production _ ?s (Terminal _ :: _) ]
                     => apply ParseProductionCons with (n := 1)
                   | [ |- parse_of_production _ ?s (_ :: nil) ]
                     => apply ParseProductionCons with (n := length s)
                   | [ |- parse_of_production _ ?s (_ :: Terminal _ :: nil) ]
                     => apply ParseProductionCons with (n := length s - 1)
                    end)
                 | apply ParseProductionNil
                 | refine (ParseTerminal _ _ _)
                 | refine (ParseNonTerminal _ _)
                 | progress simpl
                 | solve [ constructor (solve [ fin ]) ] ].

  Example plus_expr_parses_1 : parse_of_grammar "1+(2+3)+4+5"%string plus_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    match goal with
      | [ |- parse_of_production _ ?s _ ] => set (n := s)
    end.
    change n with (((("1"))) ++ ("+" ++ (("(" ++ ((((("2"))) ++ ("+" ++ ("3"))) ++ ")")) ++ ("+" ++ ("4" ++ ("+" ++ "5"))))))%string; subst n.
    apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
    apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
    apply ParseProductionCons with (n := 9); [ | solve [ fin ] ].
    constructor; simpl.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 5); simpl.
    { constructor; simpl.
      apply ParseTail, ParseHead.
      apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
      apply ParseProductionCons with (n := 3); simpl; [ | solve [ fin ] ].
      constructor; simpl.
      apply ParseTail, ParseHead; fin.
      apply ParseProductionCons with (n := 1); fin. }
    { apply ParseProductionCons with (n := 1); simpl; [ solve [ fin ] | ].
      apply ParseProductionCons with (n := 3); simpl; [ | solve [ fin ] ].
      constructor; simpl.
      apply ParseTail, ParseHead; fin.
      apply ParseProductionCons with (n := 1); fin. }
  Defined.
End tests.
