Require Import Fiat.Common.Tactics.Combinators.
Require Import Fiat.Common.Tactics.FreeIn.

Ltac setoid_subst''_x_on_left H R x y :=
  is_var x;
  free_in x y;
  rewrite ?H;
  repeat setoid_rewrite H;
  repeat match goal with
         | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; rewrite H in H'
         | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; setoid_rewrite H in H'
         end;
  clear H;
  clear x.

Ltac setoid_subst''_x_on_right H R x y :=
  is_var x;
  free_in x y;
  rewrite <- ?H;
  repeat setoid_rewrite <- H;
  repeat match goal with
         | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; rewrite <- H in H'
         | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; setoid_rewrite <- H in H'
         end;
  clear H;
  clear x.

Ltac setoid_subst'' R x :=
  is_var x;
  match goal with
  | [ H : R x ?y |- _ ] => setoid_subst''_x_on_left H R x y
  | [ H : is_true (R x ?y) |- _ ] => setoid_subst''_x_on_left H R x y
  | [ H : R ?y x |- _ ] => setoid_subst''_x_on_right H R x y
  | [ H : is_true (R ?y x) |- _ ] => setoid_subst''_x_on_right H R x y
  end.

Ltac setoid_subst' x :=
  is_var x;
  match goal with
  | [ H : ?R x ?y |- _ ] => setoid_subst''_x_on_left H R x y
  | [ H : is_true (?R x ?y) |- _ ] => setoid_subst''_x_on_left H R x y
  | [ H : ?R ?y x |- _ ] => setoid_subst''_x_on_right H R x y
  | [ H : is_true (?R ?y x) |- _ ] => setoid_subst''_x_on_right H R x y
  end.

Ltac setoid_subst_rel' R :=
  idtac;
  match goal with
  | [ H : R ?x ?y |- _ ]
    => first [ setoid_subst''_x_on_left H R x y
             | setoid_subst''_x_on_right H R y x ]
  | [ H : is_true (R ?x ?y) |- _ ]
    => first [ setoid_subst''_x_on_left H R x y
             | setoid_subst''_x_on_right H R y x ]
  end.

Ltac setoid_subst_rel R := repeat setoid_subst_rel' R.

Ltac setoid_subst_all :=
  repeat match goal with
         | [ H : ?R ?x ?y |- _ ]
           => first [ setoid_subst''_x_on_left H R x y
                    | setoid_subst''_x_on_right H R y x ]
         | [ H : is_true (?R ?x ?y) |- _ ]
           => first [ setoid_subst''_x_on_left H R x y
                    | setoid_subst''_x_on_right H R y x ]
         end.

Tactic Notation "setoid_subst" constr(x) := setoid_subst' x.
Tactic Notation "setoid_subst" := setoid_subst_all.
