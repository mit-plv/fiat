(** * Definition of grammar for regular expression [(ab)*] *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition ab_star_grammar : grammar ascii :=
  [[[ "(ab)*" ::== "" || "a" "b" "(ab)*" ]]]%grammar.

Local Open Scope list_scope.

Definition ab_star_grammar' : grammar ascii :=
  {| Start_symbol := "(ab)*";
     Lookup := fun _ => nil::((Terminal (Equality.ascii_beq "a"%char))::(Terminal (Equality.ascii_beq "b"%char))::(NonTerminal "(ab)*"%string)::nil)::nil;
     Valid_nonterminals := ("(ab)*"::nil)%string |}.
