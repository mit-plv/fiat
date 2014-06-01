Require Import String Ensembles.
Require Import Common.
Require Import Computation.Core Computation.Monad Computation.SetoidMorphisms Computation.Refinements.Tactics.

(** General Lemmas about the behavior of [computes_to], [refine], and
    [refineEquiv]. *)

Local Arguments impl _ _ / .

Section general_refine_lemmas.

  Lemma refine_under_bind X Y (f g : X -> Comp Y) x
        (eqv_f_g : forall x, refine (f x) (g x))
  : refine (Bind x f) (Bind x g).
  Proof.
    unfold refine; simpl in *; hnf; intros.
    inversion_by computes_to_inv; econstructor; eauto.
    eapply eqv_f_g; eauto.
  Qed.

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

  Lemma refine_pick_val A (P : A -> Prop) a
  : P a -> @refine A ({x | P x })%comp
                   (ret a).
  Proof.
    t_refine.
  Qed.

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

  Lemma refineEquiv_pick_pair_fst_dep A B (PA : A * B -> Prop) (PB : B -> Prop)
  : @refineEquiv _
                 {x | PA x /\ PB (snd x)}%comp
                 (b <- { b | PB b };
                  a <- { a | PA (a, b) };
                  ret (a, b))%comp.
  Proof. t_refine. Qed.

  Lemma refineEquiv_pick_pair_snd_dep A B (PA : A -> Prop) (PB : A * B -> Prop)
  : @refineEquiv _
                 { x | PA (fst x) /\ PB x }%comp
                 (a <- { a | PA a };
                  b <- { b | PB (a, b) };
                  ret (a, b))%comp.
  Proof. t_refine. Qed.

  Lemma refineEquiv_pick_pair_pair A B C
        (PA : A -> Prop) (PB : B -> Prop) (PC : C -> Prop)
  : @refineEquiv _
                 { x | (PA (fst (fst x))
                                   /\ PB (snd (fst x)))
                                   /\ PC (snd x)}%comp
                 (a <- { a | PA a };
                  b <- { b | PB b };
                  c <- { c | PC c };
                  ret (a, b, c))%comp.
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

  Definition refineEquiv_split_func_ex2'
             A A' B (P : A -> Prop) (P' : A' -> Prop)
             (f : A -> A' -> B)
  : refineEquiv { b | exists a, P a /\ exists a', P' a' /\ f a a' = b}
                (a <- { a | P a};
                 a' <- { a' | P' a'};
                 ret (f a a')).
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_computes_to A (c : Comp A)
  : refineEquiv { v | c ↝ v } c.
  Proof. t_refine. Qed.

  Definition refine_pick_computes_to A (c : Comp A)
  : refine { v | c ↝ v } c.
  Proof. t_refine. Qed.

  Lemma split_refineEquiv_fst_proj1_sig A B P Q
  : refineEquiv { x : { x : A * B | P x } | Q (fst (proj1_sig x)) }
                (x <- { x : A | Q x };
                 y <- { y : B | P (x, y) };
                 pf <- { pf : P (x, y) | True };
                 ret (exist P _ pf)).
  Proof. t_refine. Qed.

  Definition split_refine_fst_proj1_sig A B P Q
    := proj1 (@split_refineEquiv_fst_proj1_sig A B P Q).

  Lemma split_refineEquiv_snd_proj1_sig A B P Q
  : refineEquiv { x : { x : A * B | P x } | Q (snd (proj1_sig x)) }
                (x <- { x : B | Q x };
                 y <- { y : A | P (y, x) };
                 pf <- { pf : P (y, x) | True };
                 ret (exist P _ pf)).
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_computes_to_and A (c : Comp A)
             (P : Ensemble A)
  : refineEquiv { v | c ↝ v /\ P v}
                (v <- c;
                 { a | a = v /\ P a}).
  Proof. t_refine. Qed.

  Definition split_refine_snd_proj1_sig A B P Q
    := proj1 (@split_refineEquiv_snd_proj1_sig A B P Q).

  Lemma split_refineEquiv_proj1_sig A P Q
  : refineEquiv { x : { x : A | P x } | Q (proj1_sig x) }
                (x <- { x | P x /\ Q x };
                 p <- { _ : P x | True };
                 ret (exist P x p)).
  Proof. t_refine. Qed.

  Lemma refineEquiv_pick_forall_eq
        A B (a : A) (P : A -> B -> Prop)
  : @refineEquiv _
                 (Pick (fun b => forall a', a = a' -> P a' b))
                 (Pick (P a)).
  Proof. t_refine. Qed.

  Lemma refine_if_bool_eta :
    forall (u : bool),
    refine (if u then (ret true) else (ret false))
           (ret u).
  Proof. destruct u; reflexivity. Qed.

  Open Scope comp.

  Lemma refinement_step {A} (c c' : Comp A) :
    refine c c'
    -> Refinement of c'
    -> Refinement of c.
  Proof.
    intros refine_c_c' Refinement_c'.
    destruct Refinement_c' as [c'' refine_c'_c''].
    intros; econstructor.
    etransitivity; eassumption.
  Defined.

  Lemma refine_pick_forall_Prop
        A B C (a : A) (Q : C -> A -> Prop) (P : A -> C -> B -> Prop)
        b
  :
    (forall c, Q c a -> refine (Pick (P a c)) b) ->
    @refine B (Pick (fun b' => forall c, Q c a -> P a c b')) b.
  Proof.
    unfold refine; intros; econstructor; intros.
    generalize (H _ H1 _ H0); intros.
    inversion_by computes_to_inv; assumption.
  Qed.

  Lemma refine_pick_eq_ex_bind {A B : Type}
        (P : A -> B -> Prop)
        (a : A)
  : refine (a' <- {a' | a' = a /\ exists b, P a' b};
            {b | P a' b})
           {b | P a b}.
  Proof.
    unfold refine; intros; inversion_by computes_to_inv;
    econstructor; eauto.
  Qed.

  Lemma refineEquiv_if A :
    forall (f : bool -> Comp A) (b : bool) ta ea,
      refineEquiv (f true) ta
      -> refineEquiv (f false) ea
      -> refineEquiv (f b) (if b then ta else ea).
  Proof.
    destruct b; simpl; auto.
  Qed.

  Lemma refine_if A :
    forall (c : Comp A) (b : bool) ta ea,
      (b = true -> refine c ta)
      -> (b = false -> refine c ea)
      -> refine c (if b then ta else ea).
  Proof.
    destruct b; simpl; auto.
  Qed.

  Lemma refineEquiv_Pick_if {A B}
        (P : A -> B -> Prop) :
    forall (cond : bool) (ta ea : A) ta' ea',
      refineEquiv {b | P ta b} ta'
      -> refineEquiv {b | P ea b} ea'
      -> refineEquiv {b | P (if cond then ta else ea) b}
                (if cond then ta' else ea').
  Proof.
    intros; setoid_rewrite refineEquiv_if with
            (f := fun cond : bool => {b : B | P (if cond then ta else ea) b}); eauto.
    reflexivity.
  Qed.

  Lemma refineEquiv_if_ret {A}
  : forall (cond : bool) (ta ea : A),
      refineEquiv (ret (if cond then ta else ea))
                  (if cond then ret ta else ret ea).
  Proof.
    split; destruct cond; reflexivity.
  Qed.

  Definition refine_split_ex A B
             (P : A -> Prop) (P' : A -> B -> Prop)
  : @refine _
            { b | exists a, P a /\ P' a b }%comp
            (a <- { a | P a};
             { b | P' a b })%comp.
    Proof.
      t_refine.
    Qed.

  Definition refineEquiv_pick_ex_computes_to_and A B
             (c : Comp A)
             (P : A -> B -> Prop)
  : refineEquiv { b | exists a, c ↝ a /\ P a b}
                (a <- c;
                 { b | P a b}).
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_ex_computes_to_bind_and A B D
             (c : B -> Comp A)
             (cB : Comp B)
             (P : A -> D -> Prop)
  : refineEquiv { d | exists a, (b <- cB; c b) ↝ a /\ P a d}
                (b <- cB;
                 { d | exists a, c b ↝ a /\ P a d}).
  Proof. t_refine. Qed.

End general_refine_lemmas.

Tactic Notation "finalize" "refinement" :=
  eexists; solve [ reflexivity | eapply reflexivityT ].

Tactic Notation "refine" "using" constr(refinement_rule) :=
  eapply refinement_step;
  [progress setoid_rewrite refinement_rule; try reflexivity | ].
