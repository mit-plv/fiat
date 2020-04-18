Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import Bedrock.Reflection.

Set Implicit Arguments.
Set Strict Implicit.

Section fold_left2_opt.
  Variable T U V : Type.
  Variable F : T -> V -> U -> option U.

  Fixpoint fold_left_2_opt (ls : list T) (ls' : list V) (acc : U) : option U :=
    match ls, ls' with
      | nil , nil => Some acc
      | x :: xs , y :: ys =>
        match F x y acc with
          | None => None
          | Some acc => fold_left_2_opt xs ys acc
        end
      | _ , _ => None
    end.
End fold_left2_opt.

Section fold_left3_opt.
  Variable T U V A : Type.
  Variable F : T -> U -> V -> A -> option A.

  Fixpoint fold_left_3_opt (ls : list T) (ls' : list U) (ls'' : list V)
    (acc : A) : option A :=
    match ls, ls', ls'' with
      | nil , nil , nil => Some acc
      | x :: xs , y :: ys , z :: zs =>
        match F x y z acc with
          | None => None
          | Some acc => fold_left_3_opt xs ys zs acc
        end
      | _ , _ , _ => None
    end.
End fold_left3_opt.

Section All2.
  Variable X Y : Type.
  Variable F : X -> Y -> bool.

  Fixpoint all2 (xs : list X) (ys : list Y) : bool :=
    match xs , ys with
      | nil , nil => true
      | x :: xs, y :: ys => if F x y then all2 xs ys else false
      | _ , _ => false
    end.

  Variable P : X -> Y -> Prop.
  Inductive Forall2 : list X -> list Y -> Prop :=
  | Forall2_nil : Forall2 nil nil
  | Forall2_cons : forall l ls r rs,
    P l r ->
    Forall2 ls rs -> Forall2 (l :: ls) (r :: rs).

  Hypothesis F_P : forall x y, F x y = true -> P x y.

  Theorem all2_Forall2 : forall a b,
    all2 a b = true -> Forall2 a b.
  Proof.
    induction a; destruct b; simpl; intros; try congruence; try solve [ econstructor ].
      specialize (@F_P a y). destruct (F a y); eauto; try congruence; econstructor; eauto.
  Qed.

  Hypothesis P_F : forall x y, P x y -> F x y = true.

  Theorem Forall2_all2 : forall a b,
    Forall2 a b -> all2 a b = true.
  Proof.
    induction 1; simpl; auto.
    rewrite P_F; auto.
  Qed.
End All2.

Lemma Forall_app : forall A (P : A -> Prop) ls1 ls2,
  Forall P ls1
  -> Forall P ls2
  -> Forall P (ls1 ++ ls2).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma all2_map_2 : forall T U V (P : T -> U -> bool) (F : V -> _) l1 l2,
  all2 P l1 (map F l2) = all2 (fun x y => P x (F y)) l1 l2.
Proof.
  clear. induction l1; destruct l2; simpl; auto.
  destruct (P a (F v)); auto.
Qed.
Lemma all2_map_1 : forall T U V (P : T -> U -> bool) (F : V -> _) l1 l2,
  all2 P (map F l1) l2 = all2 (fun x y => P (F x) y) l1 l2.
Proof.
  clear. induction l1; destruct l2; simpl; auto.
  destruct (P (F a) u); auto.
Qed.

Lemma all2_impl : forall T U (P P' : T -> U -> bool) l1 l2,
  all2 P' l1 l2 = true ->
  (forall x y, P' x y = true -> P x y = true) ->
  all2 P l1 l2 = true .
Proof.
  clear; induction l1; destruct l2; simpl; intros; auto.
  consider (P' a u); intros. rewrite H0; eauto.
Qed.

Section allb.
  Variable A : Type.
  Variable P : A -> bool.

  Fixpoint allb (ls : list A) : bool :=
    match ls with
      | nil => true
      | x :: ls' => if P x then allb ls' else false
    end.
End allb.

Lemma allb_app : forall T (P : T -> _) a b,
  allb P (a ++ b) = allb P a && allb P b.
Proof.
  induction a; simpl; intros; auto. destruct (P a); auto.
Qed.

Lemma all2_eq : forall (T U : Type) (P P' : T -> U -> bool)
  (l1 : list T) (l2 : list U),
  (forall (x : T) (y : U), P' x y = P x y) ->
  all2 P' l1 l2 = all2 P l1 l2.
Proof.
  clear. induction l1; destruct l2; simpl; intros; auto.
  rewrite H. rewrite IHl1. auto. auto.
Qed.

Lemma allb_ext : forall T (P P' : T -> _) ls,
  (forall x, P x = P' x) ->
  allb P ls = allb P' ls.
Proof.
  clear; induction ls; simpl; intros; auto.
  rewrite H. rewrite IHls; auto.
Qed.

Lemma allb_map : forall T U (F : T -> U) P ls,
  allb P (map F ls) = allb (fun x => P (F x)) ls.
Proof.
  clear. induction ls; simpl; intros; auto.
  rewrite IHls; auto.
Qed.

Lemma allb_impl : forall T (P P' : T -> _) ls,
  allb P' ls = true ->
  (forall x, P' x = true -> P x = true) ->
  allb P ls = true.
Proof.
  induction ls; simpl; intros; auto. consider (P' a); auto; intros;
  rewrite H0; auto.
Qed.
