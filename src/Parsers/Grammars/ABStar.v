(** * Definition of grammar for regular expression [(ab)*] *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition ab_star_grammar : grammar ascii :=
  [[[ ("(ab)*" ::== << nil
                     | $< "a"%char $ "b"%char $ "(ab)*" >$ >> ) ]]]%grammar.

Local Open Scope list_scope.

Definition ab_star_grammar' : grammar ascii :=
  {| Start_symbol := "(ab)*";
     Lookup := fun _ => nil::((item_of_char "a")::(item_of_char "b")::(NonTerminal "(ab)*"%string)::nil)::nil;
     Valid_nonterminals := ("(ab)*"::nil)%string |}.
