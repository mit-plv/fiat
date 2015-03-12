(** * Definition of grammar for expressions involving parentheses and plus *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarNotations.

Set Implicit Arguments.

Section num_plus_paren.
  Local Open Scope string_scope.

  Definition plus_expr_grammar : grammar Ascii.ascii :=
    {| Start_symbol := "expr";
       Lookup := [[[ ("d" ::== << $< "0"%char >$ | $< "1"%char >$ | $< "2"%char >$ | $< "3"%char >$ | $< "4"%char >$ | $< "5"%char >$ | $< "6"%char >$ | $< "7"%char >$ | $< "8"%char >$ | $< "9"%char >$ >>);;
                     ("n" ::== << $< "d" >$ | $< "d" $ "n" >$ >>);;
                     ("expr" ::== << $< "n" >$
                                   | $< "("%char $ "expr" $ ")"%char >$
                                   | $< "expr" $ "+"%char $ "expr" >$ >>)
                 ]]]%prods_assignment;
       Valid_nonterminals := ("expr"::"d"::"n"::nil)%string |}.
End num_plus_paren.

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

  Example plus_expr_parses_1 : parse_of_grammar string_stringlike "1+(2+3)+4+5"%string plus_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseTail, ParseHead.
    match goal with
      | [ |- parse_of_production _ _ ?s _ ] => set (n := s)
    end.
    change n with (((("1"))) ++ ("+" ++ (("(" ++ ((((("2"))) ++ ("+" ++ ("3"))) ++ ")")) ++ ("+" ++ ("4" ++ ("+" ++ "5"))))))%string; subst n.
    fin.
  Defined.
End tests.
