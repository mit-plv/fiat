(** * Definition of grammar for expressions involving parentheses *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarNotations.

Set Implicit Arguments.

Section num_paren.
  Local Open Scope string_scope.
  Local Open Scope grammar_scope.

  (** TODO: Update notation so [[[ ... ]]] is the entire grammar *)
  Definition paren_expr_grammar : grammar Ascii.ascii :=
    [[[ ("expr" ::== << $< "number" >$
                      | $< #"(" $ "expr" $ #")" >$ >>);;
        ("digit" ::== << $< #"0" >$ | $< #"1" >$ | $< #"2" >$ | $< #"3" >$ | $< #"4" >$ | $< #"5" >$ | $< #"6" >$ | $< #"7" >$ | $< #"8" >$ | $< #"9" >$ >>);;
        ("number" ::== << $< "digit" >$ | $< "digit" $ "number" >$ >>)
    ]]].
End num_paren.

Section tests.
  Local Arguments append : simpl never.

  Local Ltac fin :=
    repeat first [ apply ParseProductionSingleton
                 | apply ParseProductionCons
                 | apply ParseProductionNil
                 | refine (ParseTerminal _ _ _)
                 | refine (ParseNonTerminal _ _)
                 | progress simpl
                 | solve [ constructor (solve [ fin ]) ] ].

  Example paren_expr_parses_1 : parse_of_grammar string_stringlike "(((123)))"%string paren_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    match goal with
      | [ |- parse_of_production _ _ ?s _ ] => set (n := s)
    end.
    change n with ("(" ++ ("(" ++ ("(" ++ ("1" ++ "2" ++ "3") ++ ")") ++ ")") ++ ")")%string; subst n.
    fin.
  Defined.
End tests.
