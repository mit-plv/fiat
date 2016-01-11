(** * Definition of grammar for expressions involving plus *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition plus_expr_grammar : grammar ascii :=
  [[[ ("expr" ::== << $< "number" >$
                   | $< "number" $ #"+" $ "expr" >$ >>);;
      ("number" ::== << [0-9] | $< [0-9] $ "number" >$ >>)
  ]]].
