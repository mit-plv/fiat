(** * Definition of grammar for expressions involving parentheses *)
Require Import Fiat.Parsers.ContextFreeGrammarNotations.

Definition paren_expr_grammar : grammar Ascii.ascii :=
  [[[ ("expr" ::== << $< "number" >$
                    | $< #"(" $ "expr" $ #")" >$ >>);;
      ("digit" ::== << $< #"0" >$ | $< #"1" >$ | $< #"2" >$ | $< #"3" >$ | $< #"4" >$ | $< #"5" >$ | $< #"6" >$ | $< #"7" >$ | $< #"8" >$ | $< #"9" >$ >>);;
      ("number" ::== << $< "digit" >$ | $< "digit" $ "number" >$ >>)
  ]]].
