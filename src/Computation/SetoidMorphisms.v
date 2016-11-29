Require Import Coq.Lists.List.
Require Import Fiat.Common.
Require Import Fiat.Computation.Core.
Require Import Fiat.Computation.Monad.

(** General Lemmas about the parametric morphism behavior of
    [computes_to], [refine], and [refineEquiv]. *)

Local Ltac t := unfold impl; intros; repeat (eapply_hyp || etransitivity).

Add Parametric Morphism A
: (@refine A)
  with signature
  (@refine A) --> (@refine A) ++> impl
    as refine_refine.
Proof. t. Qed.

Add Parametric Morphism A
: (@refine A)
  with signature
  (@refineEquiv A) --> (@refineEquiv A) ++> impl
    as refine_refineEquiv.
Proof. t. Qed.

Add Parametric Morphism A
: (@refine A)
    with signature
    (refineEquiv --> refineEquiv --> Basics.flip impl)
      as refine_refineEquiv'.
Proof. t. Qed.


Add Parametric Morphism A B
: (@Bind A B)
    with signature
    (@refine A)
      ==> (pointwise_relation _ (@refine B))
      ==> (@refine B)
      as refine_bind.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine in *; simpl in *.
  intros.
  computes_to_inv.
  computes_to_econstructor; eauto.
Qed.

Add Parametric Morphism A B
: (@Bind A B)
    with signature
    (Basics.flip (@refine A))
      ==> (pointwise_relation _ (Basics.flip (@refine B)))
      ==> (Basics.flip (@refine B))
      as refine_bind_flip.
Proof.
  simpl; intros.
  unfold flip, pointwise_relation, refine in *; simpl in *.
  intros.
  computes_to_inv.
  computes_to_econstructor; eauto.
Qed.

Add Parametric Morphism A B
: (@Bind A B)
    with signature
    (@refineEquiv A)
      ==> (pointwise_relation _ (@refineEquiv B))
      ==> (@refineEquiv B)
      as refineEquiv_bind.
Proof.
  idtac.
  simpl; intros.
  unfold pointwise_relation, refineEquiv, refine in *.
  split_and; simpl in *.
  split; intros;
  computes_to_inv;
  computes_to_econstructor; eauto.
Qed.

Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ (flip impl))
      ==> (@refine A)
      as refine_flip_impl_Pick.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine, impl in *; simpl in *.
  intros.
  computes_to_inv.
  computes_to_econstructor; eauto.
Qed.

Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ impl)
      ==> (flip (@refine A))
      as refine_impl_flip_Pick.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine, impl in *; simpl in *.
  intros.
  computes_to_inv.
  computes_to_econstructor; eauto.
Qed.

Add Parametric Morphism A (c : bool)
: (If_Then_Else c)
    with signature
      (@refine A ==> @refine A ==> @refine A )
      as refine_If_Then_Else.
Proof.
  unfold If_Then_Else; intros.
  destruct c; eassumption.
Qed.

Add Parametric Morphism A B (c : option A)
: (@If_Opt_Then_Else A (Comp B) c)
    with signature
    ((pointwise_relation A (@refine B))
       ==> @refine B
       ==> @refine B )
      as refine_If_Opt_Then_Else.
Proof.
  unfold If_Opt_Then_Else; intros.
  destruct c; eauto.
Qed.

Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ iff)
      ==> (@refineEquiv A)
      as refineEquiv_iff_Pick.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine in *; simpl in *.
  split_iff.
  change (pointwise_relation A impl y x) in H1.
  change (pointwise_relation A impl x y) in H0.
  split;
    intros;
    setoid_rewrite_hyp';
    reflexivity.
Qed.

Add Parametric Morphism A : (@computes_to A)
    with signature
    @refine A --> @eq A ==> impl
      as refine_computes_to_mor.
Proof.
  unfold refine, impl in *; intros; auto.
Qed.

Add Parametric Morphism A B
: (fun P => refine { x : A | exists y : B x, P x y })
    with signature
    forall_relation (fun _ => pointwise_relation _ impl) ==> @refine A ==> impl
      as refine_exists_mor.
Proof.
  unfold pointwise_relation, impl, refine in *.
  intros.
  specialize_all_ways.
  repeat match goal with
           | [ H : computes_to _ _ |- _ ] => apply computes_to_inv in H
         end.
  computes_to_econstructor.
  apply_in_hyp_no_cbv_match @Pick_inv.
  destruct_ex; eauto.
Qed.

Instance refine_refineEquiv_subrelation A
: subrelation (@refineEquiv A) (@refine A).
Proof.
  intros ? ? [? ?]; assumption.
Qed.

Add Parametric Morphism A B
: (@fold_right (Comp A) B)
  with signature
  (pointwise_relation _ (@refine A ==> @refine A)) ++> (@refine A) ++> eq ==> (@refine A)
    as refine_fold_right.
Proof.
  intros ?? H0 x0 y0 H1 ls; intros; subst.
  revert x0 y0 H1.
  induction ls; simpl; trivial; [].
  intros ?? H1.
  unfold pointwise_relation in *.
  apply H0, IHls; assumption.
Qed.

Add Parametric Morphism A B
: (@fold_right (Comp A) B)
  with signature
  (pointwise_relation _ (@refineEquiv A ==> @refineEquiv A)) ++> (@refineEquiv A) ++> eq ==> (@refineEquiv A)
    as refineEquiv_fold_right.
Proof.
  intros ?? H0 x0 y0 H1 ls; intros; subst.
  revert x0 y0 H1.
  induction ls; simpl; trivial; [].
  intros ?? H1.
  unfold pointwise_relation in *.
  apply H0, IHls; assumption.
Qed.

Add Parametric Morphism A B
: (@fold_right (Comp A) B)
  with signature
  (pointwise_relation _ (Basics.flip (@refine A) ==> Basics.flip (@refine A))) ++> (Basics.flip (@refine A)) ++> eq ==> (Basics.flip (@refine A))
    as refine_fold_right_flip.
Proof.
  intros ?? H0 x0 y0 H1 ls; intros; subst.
  revert x0 y0 H1.
  induction ls; simpl; trivial; [].
  intros ?? H1.
  unfold pointwise_relation in *.
  apply H0, IHls; assumption.
Qed.

Add Parametric Morphism A B
: (@fold_left (Comp A) B)
  with signature
  (@refine A ==> eq ==> @refine A) ++> eq ++> (@refine A) ==> (@refine A)
    as refine_fold_left.
Proof.
  intros ?? H0 ls x0 y0 H1; intros; subst.
  revert x0 y0 H1.
  induction ls; simpl; trivial; [].
  intros ?? H1.
  unfold pointwise_relation in *.
  unfold respectful in H0.
  exact (IHls _ _ (H0 _ _ H1 a _ eq_refl)).
Qed.

Add Parametric Morphism A B
: (@fold_left (Comp A) B)
  with signature
  (@refineEquiv A ==> eq ==> @refineEquiv A)
    ++> eq ++> (@refineEquiv A) ==> (@refineEquiv A)
    as refineEquiv_fold_left.
Proof.
  intros ?? H0 ls x0 y0 H1; intros; subst.
  revert x0 y0 H1.
  induction ls; simpl; trivial; [].
  intros ?? H1.
  unfold pointwise_relation in *.
  exact (IHls _ _ (H0 _ _ H1 a _ eq_refl)).
Qed.

Add Parametric Morphism A B
: (@fold_left (Comp A) B)
  with signature
  (Basics.flip (@refine A) ==> eq ==> Basics.flip (@refine A))
    ++> eq ++> (Basics.flip (@refine A)) ==> (Basics.flip (@refine A))
    as refine_fold_left_flip.
Proof.
  intros ?? H0 ls x0 y0 H1; intros; subst.
  revert x0 y0 H1.
  induction ls; simpl; trivial; [].
  intros ?? H1.
  unfold pointwise_relation in *.
  exact (IHls _ _ (H0 _ _ H1 a _ eq_refl)).
Qed.

Lemma equiv_refl {A} :
  Reflexive (@Monad.equiv A).
Proof.
  firstorder.
Qed.

Lemma equiv_sym {A} :
  Symmetric (@Monad.equiv A).
Proof.
  firstorder.
Qed.

Lemma equiv_trans {A} :
  Transitive (@Monad.equiv A).
Proof.
  firstorder.
Qed.

Add Parametric Relation {A} : _ (@Monad.equiv A)
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as MonadEquivRel.

Typeclasses Opaque If_Then_Else.

Global Instance computes_to_to_refine_Proper_fun {T} {A B RA RB f} {v : T}
       {H0 : Proper (RA ==> RB ==> refine) f}
: Proper (RA ==> RB ==> flip impl) (fun (a : A) (b : B) => computes_to (f a b) v).
Proof.
  unfold Proper, impl, flip, respectful, refine in *; eauto with nocore.
Qed.

Local Ltac refine_refineEquiv_t A :=
  unfold flip, Proper, respectful, impl; intros;
  setoid_subst_rel (@refineEquiv A);
  setoid_subst_rel (@refine A);
  reflexivity.

Global Instance refine_refineEquiv000_Proper {A}
  : Proper (refineEquiv ==> refineEquiv ==> impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv001_Proper {A}
  : Proper (refineEquiv ==> refineEquiv ==> flip impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv010_Proper {A}
  : Proper (refineEquiv ==> flip refineEquiv ==> impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv011_Proper {A}
  : Proper (refineEquiv ==> flip refineEquiv ==> flip impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv100_Proper {A}
  : Proper (flip refineEquiv ==> refineEquiv ==> impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv101_Proper {A}
  : Proper (flip refineEquiv ==> refineEquiv ==> flip impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv110_Proper {A}
  : Proper (flip refineEquiv ==> flip refineEquiv ==> impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.
Global Instance refine_refineEquiv111_Proper {A}
  : Proper (flip refineEquiv ==> flip refineEquiv ==> flip impl) (@refine A) | 5.
Proof. refine_refineEquiv_t A. Qed.

Global Instance Bind_eq_Proper {A B}
  : Proper (eq ==> pointwise_relation _ eq ==> refineEquiv) (@Bind A B).
Proof.
  intros ????? H; subst; hnf in H.
  apply refineEquiv_bind; try reflexivity.
  intro; rewrite H; reflexivity.
Qed.

Global Instance ret_Proper_eq {A}
  : Proper (eq ==> eq) (ret (A:=A)).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance refine_Proper_eq_iff {A}
  : Proper (eq ==> eq ==> iff) (@refine A).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance refine_Proper_eq_impl {A}
  : Proper (eq ==> eq ==> impl) (@refine A) | 1.
Proof. repeat (assumption || subst || intro). Qed.
Global Instance refine_Proper_eq_flip_impl {A}
  : Proper (eq ==> eq ==> flip impl) (@refine A) | 1.
Proof. repeat (assumption || subst || intro). Qed.
