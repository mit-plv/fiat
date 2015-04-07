Require Import Coq.Lists.List.
Require Import ADTSynthesis.Common.
Require Import ADTSynthesis.Computation.Core.

(** General Lemmas about the parametric morphism behavior of
    [computes_to], [refine], and [refineEquiv]. *)

Add Parametric Relation A
: (Comp A) (@refine A)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refine_rel.

Add Parametric Relation A
: (Comp A) (@refineEquiv A)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineEquiv_rel.

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

(* We have to define a wrapper for if then else in
 order for it to play nicely with setoid_rewriting. *)
Definition If_Then_Else {A}
           (c : bool)
           (t e : A) :=
  if c then t else e.

Add Parametric Morphism A (c : bool)
: (If_Then_Else c)
    with signature
      (@refine A ==> @refine A ==> @refine A )
      as refine_If_Then_Else.
Proof.
  unfold If_Then_Else; intros.
  destruct c; eassumption.
Qed.

Notation "'If' c 'Then' t 'Else' e" :=
  (If_Then_Else c t e)
    (at level 70).

Definition If_Opt_Then_Else {A B}
           (c : option A)
           (t : A -> B)
           (e : B) :=
  match c with
    | Some a => t a
    | None => e
  end.

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

Notation "'Ifopt' c 'as' c' 'Then' t 'Else' e" :=
  (If_Opt_Then_Else c (fun c' => t) e)
    (at level 70).

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
