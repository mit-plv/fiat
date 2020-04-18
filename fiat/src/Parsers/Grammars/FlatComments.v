(** * Definition of grammar for comments that don't nest, which start with two characters and end with another two characters *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition flat_comment_grammar (ch1_start ch2_start ch1_end ch2_end : ascii) : grammar ascii :=
  [[[ ("comment" ::== ch1_start ch2_start "inner_comment" ch1_end ch2_end);;
      ("inner_comment" ::== ""
       || ch1_end (¬ch2_end) "inner_comment"
       || (¬ch1_end) "inner_comment")
  ]]]%grammar.
