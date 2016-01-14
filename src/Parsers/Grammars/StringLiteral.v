(** * Definition of grammar for string literals with backslash (\) escaping double quotes ("") and backslashes *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition string_grammar : grammar ascii :=
  [[[ ("string" ::== """" "inner_string" """");;
      ("inner_string" ::== ""
       || "\" "special_character" "inner_string"
       || "unspecial_character" "inner_string");;
      ("special_character" ::== ("""" || "\")%char);;
      ("unspecial_character" ::== ¬("""" || "\"))
  ]]]%grammar.
