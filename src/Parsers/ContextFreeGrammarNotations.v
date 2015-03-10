Require Import Coq.Strings.String Coq.Lists.List.
Require Import Parsers.ContextFreeGrammar.

Fixpoint production_of_string (s : string) : production Ascii.ascii
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

Definition item_ascii := item Ascii.ascii.
Coercion item_of_char (ch : Ascii.ascii) : item_ascii := Terminal ch.
Coercion item_of_string (nt : string) : item_ascii := NonTerminal _ nt.
Definition item_ascii_cons : item_ascii -> production Ascii.ascii -> production Ascii.ascii := cons.

Delimit Scope item_scope with item.
Bind Scope item_scope with item.
Delimit Scope production_scope with production.
Delimit Scope production_assignment_scope with prod_assignment.
Bind Scope production_scope with production.
Delimit Scope productions_scope with productions.
Delimit Scope productions_assignment_scope with prods_assignment.
Bind Scope productions_scope with productions.
Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions _)%productions) (at level 100) : production_assignment_scope.
Notation "[[[ x ;; .. ;; y ]]]" :=
  (list_to_productions (nil::nil) (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.

Local Open Scope string_scope.
Notation "<< x | .. | y >>" :=
  (@cons (production _) (x)%production .. (@cons (production _) (y)%production nil) .. ) : productions_scope.

Notation "$< x $ .. $ y >$" := (item_ascii_cons x .. (item_ascii_cons y nil) .. ) : production_scope.
