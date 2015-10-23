(** * Definition of grammar for expressions involving parentheses and plus *)
Require Import Fiat.Parsers.ContextFreeGrammarNotations.

Definition plus_expr_grammar : grammar Ascii.ascii :=
  [[[ ("expr" ::== << $< "pexpr" >$
                    | $< "pexpr" $ #"+" $ "expr" >$ >>);;
      ("pexpr" ::== << $< "number" >$
                     | $< #"(" $ "expr" $ #")" >$ >>);;
      ("digit" ::== << $< #"0" >$ | $< #"1" >$ | $< #"2" >$ | $< #"3" >$ | $< #"4" >$ | $< #"5" >$ | $< #"6" >$ | $< #"7" >$ | $< #"8" >$ | $< #"9" >$ >>);;
      ("number" ::== << $< "digit" >$ | $< "digit" $ "number" >$ >>)
  ]]].
