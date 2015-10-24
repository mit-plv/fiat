(** * Definition of grammar for expressions involving plus *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition plus_expr_grammar : grammar ascii :=
  [[[ ("expr" ::== << $< "number" >$
                   | $< "number" $ #"+" $ "expr" >$ >>);;
      ("digit" ::== << $< #"0" >$ | $< #"1" >$ | $< #"2" >$ | $< #"3" >$ | $< #"4" >$ | $< #"5" >$ | $< #"6" >$ | $< #"7" >$ | $< #"8" >$ | $< #"9" >$ >>);;
      ("number" ::== << $< "digit" >$ | $< "digit" $ "number" >$ >>)
  ]]].
