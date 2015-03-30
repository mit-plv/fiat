Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.StringLike.Examples.

Fixpoint production_of_string (s : string) : production string
  := match s with
       | EmptyString => nil
       | String.String ch s' => (Terminal ch)::production_of_string s'
     end.

Coercion production_of_string : string >-> production.

Fixpoint list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
  := match ls with
       | nil => fun _ => default
       | (str, t)::ls' => fun s => if string_dec str s
                                   then t
                                   else list_to_productions default ls' s
     end.

Fixpoint list_to_grammar {T} `{StringLike T} (default : productions T) (ls : list (string * productions T)) : grammar T
  := {| Start_symbol := hd ""%string (map fst ls);
        Lookup := list_to_productions default ls;
        Valid_nonterminals := map fst ls |}.

Definition item_ascii := item string.
Coercion item_of_char (ch : Ascii.ascii) : item_ascii := Terminal ch.
Coercion item_of_string (nt : string) : item_ascii := NonTerminal nt.
Definition item_ascii_cons : item_ascii -> production string -> production string := cons.
Global Arguments item_ascii_cons / .
Global Arguments item_of_char / .
Global Arguments item_of_string / .

Delimit Scope item_scope with item.
Bind Scope item_scope with item.
Delimit Scope production_scope with production.
Delimit Scope production_assignment_scope with prod_assignment.
Bind Scope production_scope with production.
Delimit Scope productions_scope with productions.
Delimit Scope productions_assignment_scope with prods_assignment.
Bind Scope productions_scope with productions.
Delimit Scope grammar_scope with grammar.
Bind Scope grammar_scope with grammar.
Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions _)%productions) (at level 100) : production_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_productions (nil::nil) (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_grammar (nil::nil) (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : grammar_scope.

Local Open Scope string_scope.
Notation "<< x | .. | y >>" :=
  (@cons (production _) (x)%production .. (@cons (production _) (y)%production nil) .. ) : productions_scope.

Notation "$< x $ .. $ y >$" := (item_ascii_cons x .. (item_ascii_cons y nil) .. ) : production_scope.
Notation "# c" := (c%char) (at level 0, only parsing) : production_scope.
