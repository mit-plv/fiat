(** * Definition of grammar for JavaScript comments *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Parsers.Grammars.FlatComments.

Definition js_comment_grammar : grammar ascii :=
  [[[ ("comment" ::== "'//'" "single_line" \n || "'/*'" "inner_comment" "'*/'");;
      ("single_line" ::== "" || (¬\n) "single_line");;
      ("inner_comment" ::== ""
       || "*" (* ends the comment, e.g., /***/ *)
       || "*" (¬"/") "inner_comment"
       || (¬"*") "inner_comment")
  ]]]%grammar.
