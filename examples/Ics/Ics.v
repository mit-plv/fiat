Require Import ADTNotation.BuildADT ADTRefinement.GeneralRefinements.
Require Import ADT.ComputationalADT Core.

Require Import Bool ZArith List.

Export ADTNotation.BuildADT ADTRefinement.GeneralRefinements ADT.ComputationalADT Core.
Export Bool ZArith List.

Global Open Scope Z_scope.
Global Open Scope ADT_scope.

Ltac implement1 := intros;
  repeat match goal with
         | [ |- context[if ?b then _ else _] ] => case_eq b; intros
         | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
         | [ H : (?x <? ?y) = _ |- _ ] => let Hcases := fresh in generalize (Zlt_cases x y); intro Hcases;
                                            rewrite H in Hcases; clear H
         | [ H : (?x >? ?y) = _ |- _ ] => let Hcases := fresh in generalize (Zgt_cases x y); intro Hcases;
                                            rewrite H in Hcases; clear H
         end.

Ltac implement2 := intuition; try congruence;
  repeat match goal with
         | [ H : context[Z.abs ?N] |- _ ] =>
           generalize (Zabs_spec N); generalize dependent (Z.abs N); intuition
         end.

Ltac implement := implement1; try apply refine_pick_val; implement2.
