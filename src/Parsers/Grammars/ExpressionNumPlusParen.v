(** * Definition of grammar for expressions involving parentheses and plus *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

Definition plus_expr_pregrammar : pregrammar Ascii.ascii :=
  [[[ "expr" ::== "pexpr" || "pexpr" "+" "expr";;
      "pexpr" ::== "number" || "(" "expr" ")";;
      "number" ::== [0-9] || [0-9] "number"
  ]]].

Definition plus_expr_grammar : grammar Ascii.ascii := plus_expr_pregrammar.

Local Open Scope grammar_with_actions_scope.

Inductive digits := zero | digit (v : nat) (_ : digits).
Bind Scope digits_scope with digits.
Delimit Scope digits_scope with digits.
Fixpoint digits_to_nat' (v : digits) (cur : nat) : nat
  := match v with
     | zero => cur
     | digit v rest => digits_to_nat' rest (cur * 10 + v)
     end.
Coercion digits_to_nat (v : digits) : nat
  := digits_to_nat' v 0.
Coercion nat_as_fake_digits (n : nat) : digits
  := digit n zero.
Definition plus (x y : digits) : digits := x + y.
Infix "+" := plus : digits_scope.
Local Open Scope digits_scope.
Definition parseAscii_as_digits : ascii -> digits := parseAscii_as_nat.

Definition plus_expr_pregrammar_with_actions : pregrammar_with_actions Ascii.ascii digits
  := [[[ "expr" ::== "pexpr" <{< id >}> || "pexpr" "+" "expr" <{< fun x _ y => x + y >}>;;
         "pexpr" ::== "number" <{< id >}> || "(" "expr" ")" <{< fun _ e _ => e >}>;;
         "number" ::== [0-9] <{< parseAscii_as_digits >}> || [0-9] "number" <{< fun x y => digit (parseAscii_as_nat x) y >}>
     ]]]%grammar_with_actions.
