(** * Definition of grammar for expressions involving parentheses and plus *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition plus_expr_pregrammar : pregrammar Ascii.ascii :=
  [[[ "expr" ::== "pexpr" || "pexpr" "+" "expr";;
      "pexpr" ::== "number" || "(" "expr" ")";;
      "number" ::== [0-9] || [0-9] "number"
  ]]].

Definition plus_expr_grammar : grammar Ascii.ascii := plus_expr_pregrammar.
