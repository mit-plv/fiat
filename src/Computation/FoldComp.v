Require Import
  Fiat.Common
  Fiat.Computation.Core
  Fiat.Computation.SetoidMorphisms.

Open Scope comp_scope.

Fixpoint foldComp `(f : A -> B -> Comp A) (s : A) (l : list B) : Comp A :=
  match l with
    | nil => ret s
    | cons y ys => f s y >>= fun s' => foldComp f s' ys
  end.

Add Parametric Morphism A B : (@foldComp A B)
  with signature
  (eq ==> eq ==> @refine A) ++> eq ++> eq ==> (@refine A)
    as refine_foldComp_mor.
Proof.
  intros x y H z ls.
  revert z.
  revert ls.
  induction ls; intros; simpl; trivial.
    reflexivity.
  f_equiv.
    apply H; trivial.
  unfold pointwise_relation in *; intros.
  apply IHls.
Qed.

Add Parametric Morphism A B : (@foldComp A B)
  with signature
  (eq ==> eq ==> @refineEquiv A)
    ++> eq ++> eq ==> (@refineEquiv A)
    as refineEquiv_foldComp_mor.
Proof.
  intros x y H z ls.
  revert z.
  revert ls.
  induction ls; intros; simpl; trivial.
  { reflexivity. }
  { apply refineEquiv_bind.
    { apply H; trivial. }
    { unfold pointwise_relation in *; intros.
      apply IHls. } }
Qed.

Add Parametric Morphism A B : (@foldComp A B)
  with signature
  (Basics.flip eq ==> eq ==> Basics.flip (@refine A))
    ++> eq ++> (Basics.flip eq) ==> (Basics.flip (@refine A))
    as refine_foldComp_flip_mor.
Proof.
  intros x y H z ls0 ls1 Heqe.
  revert z.
  revert Heqe.
  revert ls0.
  revert ls1.
  induction ls1; intros; simpl; trivial.
    rewrite <- Heqe; simpl.
    reflexivity.
  rewrite <- Heqe; simpl.
  f_equiv.
    apply H; trivial.
  unfold pointwise_relation in *; intros.
  apply IHls1; trivial.
Qed.

Lemma refine_foldComp :
  forall (A B : Type) (s : A) (l : list B) (f g : A -> B -> Comp A),
    pointwise_relation2 refine f g
      -> refine (foldComp f s l) (foldComp g s l).
Proof.
  intros.
  subst.
  f_equiv.
  unfold pointwise_relation2 in H.
  intros st0 st1 Hst x0 x1 Hx.
  rewrite H.
  subst.
  reflexivity.
Qed.

Lemma refine_foldComp_bind :
  forall (A B : Type) (s : A) (l : list B) (f f' : A -> B -> Comp A)
         ResultT (k k' : A -> Comp ResultT),
    pointwise_relation2 refine f f'
      -> pointwise_relation _ refine k k'
      -> refine (x <- foldComp f s l; k x) (x <- foldComp f' s l; k' x).
Proof.
  intros.
  rewrite refine_foldComp.
    f_equiv.
    exact H0.
  exact H.
Qed.

Require Import Fiat.ADT.

Lemma refine_foldComp_fold :
  forall A B (st : A) (f : A -> B -> A) (xs : list B),
    refineEquiv (foldComp (fun st x => ret (f st x)) st xs)
                (ret (List.fold_left f xs st)).
Proof.
  intros.
  generalize dependent st.
  induction xs; simpl; intros.
    reflexivity.
  autorewrite with monad laws.
  apply IHxs.
Qed.

Require Import Coq.Lists.List.

Lemma refine_foldComp_fold_left_helper :
  forall A (xs : list A) S (f : S -> A -> Comp S) (z : Comp S),
    refineEquiv (x <- z; foldComp f x xs)
                (fold_left (fun acc x => s <- acc; f s x) xs z).
Proof.
  intros.
  generalize dependent z.
  induction xs; simpl; intros.
    autorewrite with monad laws.
    reflexivity.
  rewrite <- IHxs.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma refine_foldComp_fold_left :
  forall A (xs : list A) S (f : S -> A -> Comp S) (z : S),
    refineEquiv (foldComp f z xs)
                (fold_left (fun acc x => s <- acc; f s x) xs (ret z)).
Proof.
  intros.
  rewrite <- refine_foldComp_fold_left_helper.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma refine_bind_pick {A B} :
  forall (P : A -> Prop) (c : Comp B) (c' : A -> Comp B),
    (forall a', P a' -> refine c (c' a'))
      -> refine c (a <- {a | P a}; c' a).
Proof.
  unfold refine; intros.
  computes_to_inv; eauto.
Qed.

Lemma refine_foldComp_invariant' :
   forall {A S S'}
          (P : S -> S' -> Prop)
          (f : S -> A -> Comp S)
          (f' : S' -> A -> Comp S')
          (xs : list A)
          (z : S) (z' : S') ResultT
          (k : S -> Comp ResultT)
          (k' : S' -> Comp ResultT),
     (* refined function preserves invariant *)
     (forall z z',
         P z z'
         -> pointwise_relation _ refine
              (fun a => z'' <- f z a; {z' | P z'' z'})
              (fun a => f' z' a))
      -> (forall st_n st_n', P st_n st_n' -> refine (k st_n) (k' st_n'))
     -> P z z'
     -> refine (st_n  <- foldComp f  z  xs; k  st_n)
               (st_n' <- foldComp f' z' xs; k' st_n').
Proof.
  induction xs; intros;
  autorewrite with monad laws.
    eauto.
  rewrite <- (H _ _ H1 a), refineEquiv_bind_bind.
  f_equiv; intros x.
  apply refine_bind_pick; intros.
  apply IHxs; eauto.
Qed.

Corollary refine_foldComp_invariant :
  forall {A S S'} (P : S -> S' -> Prop)
         (f : S -> A -> Comp S)
         (f' : S' -> A -> Comp S')
         (z : S) (xs : list A),
    pointwise_relation2 refine (fun st_o a =>
                                  st_n <- f st_o a;
                                  {st_n' | P st_n st_n'})
                               (fun st_o a =>
                                  st_o' <- {st_o' | P st_o st_o'};
                                  f' st_o' a)
      -> refine (st_n <- foldComp f z xs;
                 {st_n' | P st_n st_n'})
                (z' <- { z' | P z z'};
                 foldComp f' z' xs).
Proof.
  intros.
  apply refine_bind_pick; intros.
  setoid_rewrite <- refineEquiv_unit_bind.
  simplify with monad laws.
  eapply refine_foldComp_invariant'; eauto; intros.
    intros ?.
    rewrite (H _ _).
    refine pick val z'; trivial.
    simplify with monad laws.
    reflexivity.
  refine pick val st_n'; trivial.
  reflexivity.
Qed.
