Require Import
        Coq.Bool.Bool
        Coq.omega.Omega
        Fiat.Common.DecideableEnsembles
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation.

(* Friendlier evar tactic *)
Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac halt_on_fail := fail.
Ltac continue_on_fail := idtac.

Ltac halt_on_fail_1 b1 := unify b1 false; fail.
Ltac continue_on_fail_1 b1 := idtac.

Ltac halt_on_fail_2 b1 b2 := unify b1 false; unify b2 false; fail.
Ltac continue_on_fail_2 b1 b2 := idtac.

Ltac sequence_two_tactics tac tac1 tac2 kfail :=
  makeEvar
    bool
    ltac:(fun b =>
            tac;
            [(* b is evar iff tac1 solves the first subgoal*)
              first [tac1; unify b true
                    | unify b false; kfail]
            (* If [tac1] solved the goal, move on to the next subgoal *)
            | first [ is_evar b; unify b true; tac2
                    | idtac ]]).

Ltac sequence_three_tactics tac tac1 tac2 tac3 kfail1 kfail2 :=
  makeEvar
    bool
    ltac:(fun b1 =>
  makeEvar
    bool
    ltac:(fun b2 =>
            tac;
            [(* b is evar iff tac1 solves the first subgoal*)
              first [tac1; unify b1 true
                    | unify b1 false; kfail1 b2]
            (* If [tac1] solved the goal, move on to the next subgoal *)
            | first [ is_evar b1; unify b1 true; tac2; unify b2 true
                    | unify b2 false; kfail2 ]
            (* If [tac2] solved the goal, move on to the next subgoal *)
            | first [ is_evar b2; unify b2 true; tac3
                    | idtac ]])).

Ltac sequence_four_tactics tac tac1 tac2 tac3 tac4 kfail1 kfail2 kfail3 :=
  makeEvar
    bool
    ltac:(fun b1 =>
  makeEvar
    bool
    ltac:(fun b2 =>
  makeEvar
    bool
    ltac:(fun b3 =>
            tac;
            [(* b is evar iff tac1 solves the first subgoal*)
              first [tac1; unify b1 true
                    | unify b1 false; kfail1 b2 b3]
            (* If [tac1] solved the goal, move on to the next subgoal *)
            | first [ is_evar b1; unify b1 true; tac2; unify b2 true
                    | unify b2 false; kfail2 b2 ]
            (* If [tac2] solved the goal, move on to the next subgoal *)
            | first [ is_evar b2; unify b2 true; tac3; unify b3 true
                    | unify b3 false; kfail3 ]
            | first [ is_evar b3; unify b3 true; tac4
                    | idtac ]]))).

Ltac build_ilist_evar :=
  match goal with
  | |- context[ith (m := ?n) (B := ?encT) (As := ?q ) ?z] =>
    is_evar z;
    match n with
    | S ?n' => let T := eval simpl in (Vector.hd q) in
                   makeEvar (encT T) ltac:(fun t' =>
                                             let H' := match (type of (@icons _ encT T n' (Vector.tl q) t')) with
                                                       | ?A -> _ => A
                                                       end in
                                             makeEvar H' ltac:(fun il' => unify z (@icons _ encT T n' (Vector.tl q) t' il')))
    | _ => idtac
    end
  | |- context[icons (n := ?n) (B := ?encT) (l := ?q) ?a ?z] =>
    is_evar z;
    match n with
    | S ?n' => let T := eval simpl in (Vector.hd q) in
                   makeEvar (encT T) ltac:(fun t' =>
                                             let H' := match (type of (@icons _ encT T n' (Vector.tl q) t')) with
                                                       | ?A -> _ => A
                                                       end in
                                             makeEvar H' ltac:(fun il' => unify z (@icons _ encT T n' (Vector.tl q) t' il')))
    | 0 => unify z (@inil _ encT)
    end
  end.

Ltac build_prim_prod_evar :=
  match goal with
  | |- context[ @ilist.prim_fst ?A unit ?z ?k] =>
    is_evar z;
    makeEvar A ltac:(fun a => unify z (Build_prim_prod a tt))
  | |- context[ @ilist.prim_fst ?A ?B ?z] =>
    is_evar z;
    makeEvar A ltac:(fun a =>
                       makeEvar B ltac:(fun b =>
                                          unify z (Build_prim_prod a b)))
  end.

Ltac ilist_of_evar B As k :=
  match As with
  | Vector.nil _ => k (@inil _ B)
  | Vector.cons _ ?a _ ?As' =>
    makeEvar (B a)
             ltac:(fun b =>
                     ilist_of_evar
                       B As'
                       ltac:(fun Bs' => k (icons (l := As') b Bs')))
  end.

Ltac Vector_of_evar n T k :=
  match n with
  | 0 => k (@Vector.nil T)
  | S ?n' => Vector_of_evar
               n' T
               ltac:(fun l =>
                       makeEvar
                         T
                         ltac:(fun a => k (@Vector.cons T a n' l)))
  end.
