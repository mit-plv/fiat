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

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

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
  | VectorDef.nil _ => k (@inil _ B)
  | VectorDef.cons _ ?a _ ?As' =>
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
