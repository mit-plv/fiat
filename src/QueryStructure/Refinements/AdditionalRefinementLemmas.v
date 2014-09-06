Require Import Ensembles List Program Common Computation.Core
        GeneralBuildADTRefinements QueryQSSpecs QueryStructure.
Require Import AdditionalLemmas InsertQSSpecs AdditionalMorphisms.

Unset Implicit Arguments.

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

Require Import Computation.Refinements.Tactics.

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
  intros; subst; inversion_by computes_to_inv; subst; trivial.
Qed.

Require Import Computation.Refinements.General.

Lemma refine_pick_val' :
  forall {A : Type} (a : A)  (P : A -> Prop),
    P a -> refine (Pick P) (ret a).
Proof.
  intros; apply refine_pick_val; assumption.
Qed.

Require Import Heading Schema.

Lemma tupleAgree_sym :
  forall (heading: Heading) tup1 tup2 attrs,
    @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
Proof.
  intros; unfold tupleAgree;
  split; intro; setoid_rewrite eq_sym_iff; assumption.
Qed.

Require Import Bool.

Lemma refine_decide_not :
  forall {A} (P: A -> Prop),
    refine (Pick (fun (b : bool) =>
                    decides b (forall (x: A), ~ P x)))
           (Pick (fun (b : bool) =>
                    decides (negb b) (exists (x: A), P x))).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  constructor.
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
  split; intros; inversion_by computes_to_inv;
  subst; repeat econstructor; eauto; rewrite negb_involutive;
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
