Require Import Ensembles List Coq.Lists.SetoidList Program
        Common Computation.Core
        ADTNotation.BuildADTSig ADTNotation.BuildADT
        GeneralBuildADTRefinements QueryQSSpecs QueryStructure
        SetEq Omega.
Require Export EnsembleListEquivalence.

Unset Implicit Arguments.

Ltac generalize_all :=
  repeat match goal with
             [ H : _ |- _ ] => generalize H; clear H
         end.

Section AdditionalDefinitions.
  Open Scope list_scope.

End AdditionalDefinitions.

Section AdditionalNatLemmas.
  Lemma le_r_le_max :
    forall x y z,
      x <= z -> x <= max y z.
  Proof.
    intros x y z;
    destruct (Max.max_spec y z) as [ (comp, eq) | (comp, eq) ];
    rewrite eq;
    omega.
  Qed.

  Lemma le_l_le_max :
    forall x y z,
      x <= y -> x <= max y z.
  Proof.
    intros x y z.
    rewrite Max.max_comm.
    apply le_r_le_max.
  Qed.

  Lemma le_neq_impl :
    forall m n, m < n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma gt_neq_impl :
    forall m n, m > n -> m <> n.
  Proof.
    intros; omega.
  Qed.
End AdditionalNatLemmas.

Section AdditionalLogicLemmas.
  Lemma or_false :
    forall (P: Prop), P \/ False <-> P.
  Proof.
    tauto.
  Qed.

  Lemma false_or :
    forall (P Q: Prop),
      (False <-> P \/ Q) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma false_or' :
    forall (P Q: Prop),
      (P \/ Q <-> False) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false :
    forall P,
      (False <-> P) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false' :
    forall P,
      (P <-> False) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma eq_sym_iff :
    forall {A} x y, @eq A x y <-> @eq A y x.
  Proof.
    split; intros; symmetry; assumption.
  Qed.
End AdditionalLogicLemmas.

Section AdditionalBoolLemmas.
  Lemma collapse_ifs_dec :
    forall P (b: {P} + {~P}),
      (if (if b then true else false) then true else false) =
      (if b then true else false).
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma collapse_ifs_bool :
    forall (b: bool),
      (if (if b then true else false) then true else false) =
      (if b then true else false).
  Proof.
    destruct b; reflexivity.
  Qed.
End AdditionalBoolLemmas.

Section AdditionalComputationLemmas.
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

  Lemma ret_computes_to :
    forall {A: Type} (a1 a2: A),
      ret a1 ↝ a2 <-> a1 = a2.
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
End AdditionalComputationLemmas.

Ltac refine_eq_into_ret :=
  match goal with
    | [ H : _ _ _ ↝ _ |- ?eq _ _ ] =>
      generalize H;
        clear H;
        apply (refine_eqA_into_ret _)
  end.

Ltac prove_observational_eq :=
  lazy; intuition (eauto using collapse_ifs_bool, collapse_ifs_dec; eauto with *).

Section AdditionalQueryLemmas.

  Require Import Computation.Refinements.General.

  Lemma refine_pick_val' :
    forall {A : Type} (a : A)  (P : A -> Prop),
      P a -> refine (Pick P) (ret a).
  Proof.
    intros; apply refine_pick_val; assumption.
  Qed.

  Require Import InsertQSSpecs StringBound.
  Lemma get_update_unconstr_iff {db_schema qs table new_contents} :
    forall x,
      Ensembles.In _ (GetUnConstrRelation (UpdateUnConstrRelation db_schema qs table new_contents) table) x <->
      Ensembles.In _ new_contents x.
  Proof.
    unfold GetUnConstrRelation, UpdateUnConstrRelation, RelationInsert;
    intros; rewrite ith_replace_BoundIndex_eq;
    reflexivity.
  Qed.

  Require Import Heading Schema.
  Lemma tupleAgree_sym :
    forall (heading: Heading) tup1 tup2 attrs,
      @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
  Proof.
    intros; unfold tupleAgree;
    split; intro; setoid_rewrite eq_sym_iff; assumption.
  Qed.
End AdditionalQueryLemmas.
