Require Import Coq.Strings.String
        Coq.Sets.Ensembles
        Coq.Bool.Bool.
Require Import Fiat.Common
        Fiat.Common.BoolFacts
        Fiat.Common.LogicFacts
        Fiat.Computation.Core
        Fiat.Computation.Monad
        Fiat.Computation.SetoidMorphisms
        Fiat.Computation.Refinements.Tactics.

(** General Lemmas about the behavior of [computes_to], [refine], and
    [refineEquiv]. *)

Local Arguments impl _ _ / .

Section general_refine_lemmas.

  Lemma refine_under_bind {A B}
  : forall c (x y : A -> Comp B),
    (forall a, c ↝ a -> refine (x a) (y a))
    -> refine (a <- c; x a) (a <- c; y a).
  Proof. t_refine.  Qed.

  (* Combines refine_under_bind and refine_bind:
generates another subgoal for the first expression,
and gives you the computational hypothesis for the second *)
  Lemma refine_under_bind_both {A B}
    : forall c c' (x y : A -> Comp B),
      refine c c' ->
      (forall a, c ↝ a -> refine (x a) (y a))
      ->
      refine (a <- c; x a) (a <- c'; y a).
  Proof. t_refine. Qed.

  Lemma refine_pick A (P : A -> Prop) c (H : forall x, c ↝ x -> P x)
    : @refine A ({x : A | P x })%comp
              c.
  Proof. t_refine. Qed.

  Lemma refine_pick_val A a (P : A -> Prop)
    : P a -> @refine A ({x | P x })%comp
                     (ret a).
  Proof.
    t_refine.
  Qed.

  Lemma refine_bind_pick :
    forall (A B : Type) (P : Ensemble A),
    forall x y : A -> Comp B,
      (forall a, P a -> refine (x a) (y a)) ->
      refine (a <- {a | P a};
              x a)
             (a <- {a | P a};
              y a).
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

  Lemma refineEquiv_pick_pair_fst_dep A B (PA : A * B -> Prop) (PB : B -> Prop)
    : @refineEquiv _
                   {x | PA x /\ PB (snd x)}%comp
                   (b <- { b | PB b };
                    a <- { a | PA (a, b) };
                    ret (a, b))%comp.
  Proof.
    t_refine.
  Qed.

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
  Proof.
    split; intros v Comp_v; computes_to_inv;
    intuition; destruct_ex;
    repeat (computes_to_econstructor; eauto);
    intuition eauto.
  Qed.

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

  Definition refine_pick_eq
             A (x : A)
    : @refine _
              { y | y = x }%comp
              (ret x).
  Proof. apply refineEquiv_pick_eq. Qed.

  Definition refine_pick_eq' A (x : A)
    : @refine _ { y | x = y }%comp
              (ret x).
  Proof. apply refineEquiv_pick_eq'. Qed.

  Definition refineEquiv_split_func_ex
    : forall A B (P : A -> Prop) (f : A -> B),
      @refineEquiv _ { b | exists a, P a /\ b = f a}%comp
                   (a <- { a | P a};
                    ret (f a))%comp.
  Proof.
    split; intros v Comp_v; computes_to_inv;
    intuition; destruct_ex;
    repeat (computes_to_econstructor; eauto);
    intuition eauto.
    subst; eauto.
  Qed.

  Definition refineEquiv_split_func_ex2
             A A' B (P : A -> Prop) (P' : A' -> Prop)
             (f : A -> A' -> B)
    : refineEquiv { b | exists a, P a /\ exists a', P' a' /\ b = f a a'}
                  (a <- { a | P a};
                   a' <- { a' | P' a'};
                   ret (f a a')).
  Proof.
    split; intros v Comp_v; computes_to_inv;
    intuition; destruct_ex;
    computes_to_econstructor; eauto;
    intuition; destruct_ex; intuition; try subst;
    computes_to_econstructor; eauto.
  Qed.

  Definition refineEquiv_split_func_ex2'
             A A' B (P : A -> Prop) (P' : A' -> Prop)
             (f : A -> A' -> B)
    : refineEquiv { b | exists a, P a /\ exists a', P' a' /\ f a a' = b}
                  (a <- { a | P a};
                   a' <- { a' | P' a'};
                   ret (f a a')).
  Proof.
    split; intros v Comp_v; computes_to_inv;
    intuition; destruct_ex;
    computes_to_econstructor; eauto;
    intuition; destruct_ex; intuition; try subst;
    computes_to_econstructor; eauto.
  Qed.

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

  Open Scope comp_scope.

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
      (forall c : C, Q c a -> refine {x : B | P a c x} b) ->
      refine {b' : B | forall c : C, Q c a -> P a c b'} b.
  Proof.
    unfold refine; intros; computes_to_econstructor; intros.
    generalize (H _ H1 _ H0); intros.
    computes_to_inv; assumption.
  Qed.

  Lemma refine_pick_eq_ex_bind {A B : Type}
        (P : A -> B -> Prop)
        (a : A)
    : refine (a' <- {a' | a' = a /\ exists b, P a' b};
              {b | P a' b})
             {b | P a b}.
  Proof.
    t_refine.
  Qed.

  (* This helper lemma makes terms more ameneable to
     setoid_rewriting. *)
  Lemma refine_if_If {A}
    : forall (c : bool) (t e : Comp A),
      refine (if c then t else e)
             (If c Then t Else e).
  Proof.
    reflexivity.
  Qed.

  (* Nontermination with above lemma? *)
  (*
  Lemma refine_If_if {A}
  : forall (c : bool) (t e : Comp A),
      refine (If c Then t Else e)
             (if c then t else e).
  Proof.
    reflexivity.
  Qed.
   *)

  Lemma refine_if_andb {A}
    : forall (i i' : bool)
             (t e : A),
      (if i then (if i' then t else e) else e) =
      if i && i' then t else e.
  Proof.
    destruct i; destruct i'; reflexivity.
  Qed.

  Lemma refineEquiv_if A :
    forall (f : bool -> Comp A) (b : bool) ta ea,
      refineEquiv (f true) ta
      -> refineEquiv (f false) ea
      -> refineEquiv (f b) (If b Then ta Else ea).
  Proof.
    destruct b; simpl; auto.
  Qed.

  Lemma refine_if_P A :
    forall Pc (Pt Pa : Ensemble A),
      refine { a | (Pc -> Pt a) /\ Pa a}
             (b <- {b | Pc -> b = true};
              If b Then { a | Pt a /\ Pa a}
                 Else { a | Pa a}).
  Proof.
    intros * v Comp_v; computes_to_inv.
    computes_to_econstructor; intuition; subst;
    try destruct v0; simpl in *; eauto; computes_to_inv; intuition.
  Qed.

  Definition decides (b : bool) (P : Prop)
    := If b Then P Else ~ P.

  Lemma refine_iff_P A :
    forall (Pc : Prop) (Pt Pa : Ensemble A),
      refine { a | (Pc -> Pt a) /\ Pa a}
             (b <- {b | decides b Pc};
              If b Then { a | Pt a /\ Pa a}
                 Else { a | Pa a}).
  Proof.
    intros * v Comp_v; computes_to_inv.
    computes_to_econstructor; intuition; subst;
    try destruct v0; simpl in *; eauto; computes_to_inv; intuition.
  Qed.

  Lemma refine_if A :
    forall (c : Comp A) (b : bool) ta ea,
      (b = true -> refine c ta)
      -> (b = false -> refine c ea)
      -> refine c (If b Then ta Else ea).
  Proof.
    destruct b; simpl; auto.
  Qed.

  Lemma refineEquiv_Pick_if {A B}
        (P : A -> B -> Prop) :
    forall (cond : bool) (ta ea : A) ta' ea',
      refineEquiv {b | P ta b} ta'
      -> refineEquiv {b | P ea b} ea'
      -> refineEquiv {b | P (If cond Then ta Else ea) b}
                     (If cond Then ta' Else ea').
  Proof.
    intros; setoid_rewrite refineEquiv_if with
            (f := fun cond : bool => {b : B | P (If cond Then ta Else ea) b}); eauto.
    reflexivity.
  Qed.

  Lemma refineEquiv_if_ret {A}
    : forall (cond : bool) (ta ea : A),
      refineEquiv (ret (If cond Then ta Else ea))
                  (If cond Then ret ta Else ret ea).
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
  Proof.
    split; intros * v Comp_v; computes_to_inv; destruct_ex; intuition;
    t_refine. Qed.

  Lemma refine_Pick_If_Then_Opt {A B}
    : forall (P : Ensemble B) (c e : Comp A) (t : B -> Comp A),
      (forall b, P b -> refine c (t b))
      -> (refine c e)
      -> refine c
                (b <- {b | forall b',
                          (b = Some b' -> P b')};
                 Ifopt b as b' Then t b' Else e).
  Proof.
    t_refine.
    destruct v0; t_refine.
    eapply H; eauto.
  Qed.

  Lemma refine_Pick_Some_dec {A B}
    : forall (P : Ensemble B) (c e : Comp A) (t : B -> Comp A),
      (forall b, P b -> refine c (t b))
      -> ((forall b, ~ P b) -> refine c e)
      -> refine c
                (b <- {b | forall b',
                          (b = Some b' -> P b')
                          /\ (b = None -> forall b', ~ P b')};
                 Ifopt b as b' Then t b' Else e) .
  Proof.
    unfold refine; intros; computes_to_inv;
    destruct v0; simpl in *; computes_to_inv; eauto.
    eapply H; eauto.
    eapply H1; eauto.
    eapply H0; eauto; intros; eapply H1; eauto.
  Qed.

  Add Morphism
      (decides)
      with signature (eq ==> iff ==> iff)
        as decide_eq_iff_iff_morphism.
  Proof.
    unfold decides; intros b p1 p2 equiv.
    destruct b; simpl; intuition.
  Qed.

  Lemma refine_pick_decides {A}
    : forall (P : Prop) (c e : Comp A) (t : Comp A),
      (P -> refine c t)
      -> (~ P -> refine c e)
      -> refine c
                (b <- {b | decides b P};
                 If b Then t Else e).
  Proof.
    unfold refine; intros; computes_to_inv;
    destruct_ex; split_and; computes_to_inv.
    destruct v0; simpl in *; eauto.
  Qed.

  Lemma refine_pick_decides_branches {A}
        (P : Prop)
        (Q Q' : Ensemble A)
        (q q' : Comp A)
    : (P -> refine {a | Q a} q)
      -> (~ P -> refine {a | Q' a} q')
      -> refine {a | (P -> Q a) /\
                     (~ P -> Q' a)}
                (b <- {b | decides b P};
                 If b Then q Else q').
  Proof.
    intros; eapply refine_pick_decides.
    - unfold refine; intros; computes_to_inv;
      econstructor; intuition; eapply H4; eauto.
    - unfold refine; intros; computes_to_inv;
      econstructor; intuition; eapply H4; eauto.
  Qed.

  Lemma refine_pick_decides' {A}
        (P : Prop)
        (Q Q' : Ensemble A)
    : refine {a | (P -> Q a) /\
                  (~ P -> Q' a)}
             (b <- {b | decides b P};
              If b Then
                 {a | Q a}
                 Else
                 {a | Q' a}).
  Proof.
    eapply refine_pick_decides_branches; reflexivity.
  Qed.

  Global Add Parametric Morphism : decides
      with signature eq ==> iff ==> iff
        as decides_mor.
  Proof.
    repeat intro; split_iff; destruct_head bool; simpl; tauto.
  Qed.

  Lemma refineEquiv_decides_eqb (b b1 b2 : bool)
    : decides b (b1 = b2) <-> b = If b2 Then b1 Else negb b1.
  Proof.
    destruct_head bool; simpl; intuition.
  Qed.

  Lemma refine_If_Then_Else_Bind {A B}
    : forall i (t e : Comp A) (b : A -> Comp B),
      refine (a <- If i Then t Else e; b a)
             (If i Then (a <- t;
                         b a)
                 Else (a <- e;
                       b a)).
  Proof.
    intros; destruct i; simpl; reflexivity.
  Qed.

  Lemma refine_if_Then_Else_Duplicate {A}
    : forall (i : bool) (t e e' : Comp A),
      refine (if i then (if i then t else e') else e)
             (if i then t else e).
  Proof.
    destruct i; simpl; reflexivity.
  Qed.


  Lemma refine_If_Then_Else_Duplicate {A}
    : forall i (t e e' : A),
      If i Then (If i Then t Else e') Else e =
      If i Then t Else e.
  Proof.
    destruct i; simpl; reflexivity.
  Qed.

  Lemma refine_If_Opt_Then_Else_Bind {A B C}
    : forall (i : option A)
             (t : A -> Comp B)
             (e : Comp B)
             (c : B -> Comp C),
      refine (b <- If_Opt_Then_Else i t e; c b)
             (If_Opt_Then_Else i (fun a' =>
                                    b <- t a';
                                  c b)
                               (b <- e;
                                c b)).
  Proof.
    intros; destruct i; simpl; reflexivity.
  Qed.

  Lemma refine_trivial_if_then_else :
    forall x,
      refine
        (If_Then_Else x (ret true) (ret false))
        (ret x).
  Proof.
    destruct x; reflexivity.
  Qed.

  Lemma decides_True :
    refine {b | decides b True}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_True_Pre (Q : Prop) :
    refine {b | Q -> decides b True}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_2_True (A : Type) (B : A -> Type) :
    refine {b' | decides b' (forall a : A, B a -> True)}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_3_True (A B : Type) (C : B -> Type) :
    refine {b' | decides b' (A -> forall b : B, C b -> True)}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_neq (A : Type) (B : Prop) (a : A) :
    refine {b' | decides b' (a <> a -> B)}%comp
           (ret true).
  Proof.
    computes_to_econstructor;  computes_to_inv; subst; simpl; auto.
    congruence.
  Qed.

  Lemma Bind_refine_If_Then_Else {A B}
    : forall i (t e : A -> Comp B) (ca : Comp A),
      refine (a <- ca;
              If i Then t a Else e a)
             (If i Then (a <- ca;
                         t a)
                 Else (a <- ca;
                       e a)).
  Proof.
    intros; destruct i; simpl; reflexivity.
  Qed.

  Lemma Bind_refine_If_Opt_Then_Else {A B C}
    : forall i (t : A -> B -> Comp C) (e : A -> Comp C) (ca : Comp A),
      refine (a <- ca;
              Ifopt i as b Then t a b Else e a)
             (Ifopt i as b Then (a <- ca;
                                 t a b)
                           Else (a <- ca;
                                 e a)).
  Proof.
    intros; destruct i; simpl; reflexivity.
  Qed.

  Lemma refineEquiv_swap_bind {A B C} (c1 : Comp A) (c2 : Comp B) (f : A -> B -> Comp C)
    : refineEquiv (a <- c1; b <- c2; f a b) (b <- c2; a <- c1; f a b).
  Proof.
    split; repeat intro;
    computes_to_inv;
    repeat (econstructor; try eassumption).
  Qed.

  Lemma refine_bind_dedup {A B} (c1 : Comp A) (f : A -> A -> Comp B)
    : refine (a <- c1; b <- c1; f a b) (a <- c1; f a a).
  Proof.
    repeat intro;
    computes_to_inv;
    repeat (econstructor; try eassumption).
  Qed.

  Lemma comp_split_snd {A B} (x : A * B)
    : refineEquiv (ret (snd x))
                  (ab <- ret x;
                   ret (snd ab)).
  Proof.
    autorewrite with refine_monad; reflexivity.
  Qed.

  Lemma refine_skip {A B C} (c : Comp A) (f : A -> Comp B) (dummy : A -> Comp C)
    : refine (Bind c f)
             (a <- c;
              dummy a>>
                    f a).
  Proof.
    repeat first [ intro
                 | computes_to_inv
                 | computes_to_econstructor; eassumption
                 | computes_to_econstructor; try eassumption; [] ].
    computes_to_econstructor; eauto.
  Qed.

  Lemma refine_skip2 {A B} (a : Comp A) (dummy : Comp B)
    : refine a
             (dummy>>
                   a).
  Proof.
    repeat first [ intro
                 | computes_to_inv
                 | assumption
                 | econstructor; eassumption
                 | econstructor; try eassumption; [] ].
    eauto.
  Qed.

  Lemma decides_negb :
    forall b P,
      decides (negb b) P -> decides b (~ P).
  Proof.
    unfold decides; setoid_rewrite if_negb; simpl; intros.
    destruct b; simpl in *; intuition.
  Qed.


  Lemma refine_decide_not :
    forall {A} (P: A -> Prop),
      refine (Pick (fun (b : bool) =>
                      decides b (forall (x: A), ~ P x)))
             (Pick (fun (b : bool) =>
                      decides (negb b) (exists (x: A), P x))).
  Proof.
    unfold refine; intros; computes_to_inv.
    computes_to_constructor.
    rewrite <- not_exists_forall; apply decides_negb;
    assumption.
  Qed.

  Lemma refine_decide_negb :
    forall P,
      refineEquiv (Pick (fun b => decides (negb b) P))
                  (Bind (Pick (fun b => decides b P))
                        (fun b => ret (negb b))).
  Proof.
    unfold refineEquiv, refine; simpl;
    split; intros; computes_to_inv;
    subst; repeat computes_to_econstructor; eauto; rewrite Bool.negb_involutive;
    [ assumption | constructor ].
  Qed.

  Lemma refine_decide_negation :
    forall {A} (P: A -> Prop),
      refine (Pick (fun (b : bool) =>
                      decides b (forall (x: A), ~ P x)))
             (Bind (Pick (fun b => decides b (exists (x: A), P x)))
                   (fun b => ret (negb b))).
  Proof.
    intros;
    rewrite refine_decide_not, refine_decide_negb; reflexivity.
  Qed.


  Lemma eq_ret_compute :
    forall (A: Type) (x y: A), x = y -> ret x ↝ y.
  Proof.
    intros; subst; apply ReturnComputes; trivial.
  Qed.

  Lemma refine_eq_ret :
    forall {A} (a a': A),
      a = a' ->
      refineEquiv  (ret a) (ret a').
  Proof.
    intros; subst; reflexivity.
  Qed.

  Require Import Fiat.Computation.Refinements.Tactics.

  Lemma refine_snd :
    forall {A B: Type} (P: B -> Prop),
      refine
        { pair | P (snd pair) }
        (_fst <- Pick (fun (x: A) => True);
         _snd <- Pick (fun (y: B) => P y);
         ret (_fst, _snd)).
  Proof.
    t_refine.
  Qed.

  Lemma refine_let :
    forall {A B : Type} (PA : A -> Prop) (PB : B -> Prop),
      refineEquiv (Pick (fun x: A * B  =>  let (a, b) := x in PA a /\ PB b))
                  (a <- {a | PA a};
                   b <- {b | PB b};
                   ret (a, b)).
  Proof.
    t_refine.
  Qed.

  Lemma refine_ret_eq :
    forall {A: Type} (a: A) b,
      b = ret a -> refine (ret a) (b).
  Proof.
    t_refine.
  Qed.

  Lemma refine_eqA_into_ret :
    forall {A: Type} {eqA: list A -> list A -> Prop},
      Reflexive eqA ->
      forall (comp : Comp (list A)) (impl result: list A),
        comp = ret impl -> (
          comp ↝ result ->
          eqA result impl
        ).
  Proof.
    intros; subst; computes_to_inv; subst; trivial.
  Qed.

  Lemma refine_pick_val' :
    forall {A : Type} (a : A)  (P : A -> Prop),
      P a -> refine (Pick P) (ret a).
  Proof.
    intros; apply refine_pick_val; assumption.
  Qed.

  Lemma refine_If_Then_Else_ret {A} :
    forall i (t e : A),
      refine (@If_Then_Else (Comp A) i (ret t) (ret e))
             (ret (@If_Then_Else A i t e)).
  Proof.
    destruct i; reflexivity.
  Qed.

  Lemma refine_If_Opt_Then_Else_ret {A B} :
    forall i (t : A -> B) (e : B),
      refine (@If_Opt_Then_Else A (Comp B) i (fun a => ret (t a)) (ret e))
             (ret (@If_Opt_Then_Else A B i t e)).
  Proof.
    destruct i; reflexivity.
  Qed.


End general_refine_lemmas.

Tactic Notation "finalize" "refinement" :=
  eexists; solve [ reflexivity | eapply reflexivityT ].

Tactic Notation "refine" "using" constr(refinement_rule) :=
  eapply refinement_step;
  [progress setoid_rewrite refinement_rule; try reflexivity | ].

(* 'Wrapper' tactics for various refinements *)

Tactic Notation "refine" "pick" "pair" :=
  rewrite refine_pick_pick;
  [ |
    let x := fresh in
    let H := fresh in
    intros x H;
      let A := match goal with
                 |- ?A /\ ?B => constr:(A)
               end in
      let B := match goal with
                 |- ?A /\ ?B => constr:(B)
               end in
      match eval pattern (fst x) in A with
        ?A' _ =>
        match eval pattern (snd x) in B with
          ?B' _ =>
          match type of H with
          | ?C _ => unify C (fun x => A' (fst x) /\ B' (snd x));
              exact H
          end
        end
      end ]; rewrite refineEquiv_pick_pair.

Lemma refine_under_bind_both_trans {A B}
  : forall c c' c'' (x y : A -> Comp B),
    refine c c' ->
    (forall a, c ↝ a -> refine (x a) (y a))
    -> refine (a <- c'; y a) c''
    -> refine (a <- c; x a) c''.
Proof. intros; etransitivity; eauto using refine_under_bind_both. Qed.

Lemma refine_If_Then_Else_trans {A}
  : forall (c : bool) (x y z : Comp A),
    refine x y ->
    forall x0 y0 : Comp A,
      refine x0 y0
      -> refine (If c Then y Else y0) z
      -> refine (If c Then x Else x0) z.
Proof. intros; etransitivity; eauto using refine_If_Then_Else. Qed.

Lemma refine_If_Opt_Then_Else_trans {A B}
  : forall (c : option B) (e e' z: Comp A) (t t' : B -> Comp A),
    (forall b, refine (t b) (t' b))
    -> (refine e e')
    -> refine (Ifopt c as b' Then t' b' Else e') z
    -> refine (Ifopt c as b' Then t b' Else e) z.
Proof.
  intros; etransitivity; eauto using refine_If_Opt_Then_Else.
Qed.


Local Ltac t2 p := intros; destruct p; intuition.

Lemma refine_sumbool_match :
  forall `(P : {A} + {~A}) B
         (f f' : A -> Comp B) (g g' : ~A -> Comp B),
       pointwise_relation A    refine f f'
    -> pointwise_relation (~A) refine g g'
    -> refine (match P with
               | left  H => f H
               | right H => g H
               end)
              (match P with
               | left  H => f' H
               | right H => g' H
               end).
Proof. t2 P. Qed.

Lemma refine_sumbool_ret :
  forall `(P : {A} + {~A}) `(f : A -> B) (g : ~A -> B),
    refine (match P with
            | left  H => ret (f H)
            | right H => ret (g H)
            end)
           (ret (match P with
                 | left  H => f H
                 | right H => g H
                 end)).
Proof. t2 P. Qed.

Lemma refine_sumbool_bind :
  forall `(P : {A} + {~A})
         `(f : A -> Comp B) (g : ~A -> Comp B)
         `(h : B -> Comp C),
    refine (x <- match P with
                 | left  H => f H
                 | right H => g H
                 end;
            h x)
           (match P with
            | left  H => x <- f H; h x
            | right H => x <- g H; h x
            end).
Proof. t2 P. Qed.

Lemma refine_bind_sumbool :
  forall `(P : {A} + {~A})
         `(f : C -> A -> Comp B) (g : C -> ~A -> Comp B)
         `(c : Comp C),
    refine (x <- c;
            match P with
            | left  H => f x H
            | right H => g x H
            end)
           (match P with
            | left  H => x <- c; f x H
            | right H => x <- c; g x H
            end).
Proof. t2 P. Qed.

Tactic Notation "refine" "pick" "val" open_constr(v) :=
  let T := type of v in
  rewrite refine_pick_val with
  (A := T)
    (a := v) at 1.

Tactic Notation "refine" "pick" "eq" :=
  match goal with
  | |- context[Pick (fun x => x = _)] =>
    setoid_rewrite refine_pick_eq || setoid_rewrite refineEquiv_pick_eq
  | |- context[Pick (fun x => _ = x)] =>
    setoid_rewrite refine_pick_eq' || setoid_rewrite refineEquiv_pick_eq'
  end.
