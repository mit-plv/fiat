Require Import String Ensembles.
Require Import Common.
Require Import Computation.Core Computation.Monad Computation.SetoidMorphisms.

(** General Lemmas about the behavior of [computes_to], [refine], and
    [refineEquiv]. *)

Local Arguments impl _ _ / .

Local Ltac t_refine :=
  repeat first [ progress simpl in *
               | progress eauto
               | eassumption
               | reflexivity
               | progress split_iff
               | progress inversion_by computes_to_inv
               | progress subst
               | intro
               | econstructor
               | erewrite is_computational_val_unique
               | progress destruct_head_hnf prod
               | progress destruct_head_hnf and
               | progress specialize_all_ways ].

Section general_refine_lemmas.
  
  Lemma refineEquiv_is_computational {A} {c} (CompC : @is_computational A c)
  : @refineEquiv _ c (ret (is_computational_val CompC)).
  Proof.
    unfold refineEquiv, refine.
    pose proof (is_computational_val_computes_to CompC).
    t_refine.
  Qed.

  Lemma refine_pick A (P : A -> Prop) c (H : forall x, c ↝ x -> P x)
  : @refine A ({x : A | P x })%comp
            c.
  Proof. t_refine. Qed.

  Lemma refine_pick_pick A (P1 P2 : A -> Prop)
        (H : forall x, P2 x -> P1 x)
  : @refine _
            { x : A | P1 x }%comp
            { x : A | P2 x }%comp.
  Proof. t_refine. Qed.

  Lemma refineEquiv_pick_pick A (P1 P2 : A -> Prop)
        (H : forall x, P1 x <-> P2 x)
  : @refineEquiv _
                 { x : A | P1 x }%comp
                 { x : A | P2 x }%comp.
  Proof. t_refine. Qed.

  Lemma refineEquiv_pick_pair A B (PA : A -> Prop) (PB : B -> Prop)
  : @refineEquiv _
                 { x : A * B | PA (fst x) /\ PB (snd x) }%comp
                 (a <- { a : A | PA a };
                  b <- { b : B | PB b };
                  ret (a, b))%comp.
  Proof. t_refine. Qed.

  Definition refineEquiv_split_ex A B
             (P : A -> Prop) (P' : A -> B -> Prop)
  : @refineEquiv _ 
                 { b | exists a, P a /\ P' a b }%comp
                 (a <- { a | P a /\ exists b, P' a b };
                  { b | P' a b })%comp.
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_contr_ret A (P : A -> Prop)
             (x : A) (H : unique P x)
  : @refineEquiv _ 
                 { y | P y }
                 (ret x).
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_eq 
             A (x : A)
  : @refineEquiv _ 
                 { y | y = x }%comp
                 (ret x).
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_eq' A (x : A)
  : @refineEquiv _ { y | x = y }%comp
                 (ret x).
  Proof. t_refine. Qed.

  Definition refineEquiv_split_func_ex
  : forall A B (P : A -> Prop) (f : A -> B),
      @refineEquiv _ { b | exists a, P a /\ b = f a}%comp
                   (a <- { a | P a};
                    ret (f a))%comp.
  Proof. t_refine. Qed.

  Definition refineEquiv_split_func_ex2 
             A A' B (P : A -> Prop) (P' : A' -> Prop)
             (f : A -> A' -> B)
  : refineEquiv { b | exists a, P a /\ exists a', P' a' /\ b = f a a'}
                (a <- { a | P a};
                 a' <- { a' | P' a'};
                 ret (f a a')).
  Proof. t_refine. Qed.

End general_refine_lemmas.
