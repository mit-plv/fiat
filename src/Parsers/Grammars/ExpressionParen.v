(** * Definition of grammar for expressions involving parentheses *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition paren_expr_grammar : grammar Ascii.ascii :=
  [[[ "expr" ::== "number" || "(" "expr" ")";;
      "number" ::== [0-9] || [0-9] "number"
  ]]].
