(** * Definition of grammar for regular expression [(ab)*] *)
Require Import Fiat.Parsers.ContextFreeGrammarNotations.

Definition ab_star_grammar : grammar ascii :=
  [[[ ("(ab)*" ::== << nil
                     | $< "a"%char $ "b"%char $ "(ab)*" >$ >> ) ]]]%grammar.

Local Open Scope list_scope.

Definition ab_star_grammar' : grammar ascii :=
  {| Start_symbol := "(ab)*";
     Lookup := fun _ => nil::(Terminal "a"%char::Terminal "b"%char::NonTerminal "(ab)*"%string::nil)::nil;
     Valid_nonterminals := ("(ab)*"::nil)%string |}.
