Require Import Common.
Require Import Computation.Core.

(** General Lemmas about the parametric morphism behavior of
    [computes_to], [refine], and [refineEquiv]. *)

Add Parametric Relation A `{LookupContext}
: (Comp A) (@refine A _ _)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refine_rel.

Add Parametric Relation A
: (BundledComp A) (@refineBundled A)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refineBundled_rel.

Add Parametric Relation A `{LookupContext}
: (Comp A) (@refineEquiv A _ _)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineEquiv_rel.

Add Parametric Relation A
: (BundledComp A) (@refineBundledEquiv A)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineBundledEquiv_rel.

Local Ltac t := unfold impl; intros; repeat (eapply_hyp || etransitivity).

Add Parametric Morphism A `{LookupContext}
: (@refine A _ _)
  with signature
  (@refine A _ _) --> (@refine A _ _) ++> impl
    as refine_refine.
Proof. t. Qed.

(*Add Parametric Morphism A names dom cod lookup
: (@refine A names dom cod names dom cod lookup lookup)
  with signature
  (@refineEquiv A names dom cod names dom cod lookup lookup) --> (@refineEquiv A names dom cod names dom cod lookup lookup) ++> impl
    as refine_refineEquiv.
Proof. t. Qed.*)


Add Parametric Morphism A
: (@refineBundled A)
  with signature
  (@refineBundled A) --> (@refineBundled A) ++> impl
    as refineBundled_refineBundled.
Proof. t. Qed.

(*Add Parametric Morphism A
: (@refineBundled A)
  with signature
  (@refineBundledEquiv A) --> (@refineBundledEquiv A) ++> impl
    as refineBundled_refineBundledEquiv.
Proof. t. Qed.*)

Hint Constructors computes_to.

Add Parametric Morphism `{LookupContext} A B
: (@Bind _ A B)
    with signature
    (@refine A _ _)
      ==> (pointwise_relation _ (@refine B _ _))
      ==> (@refine B _ _)
      as refine_bind.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine in *; simpl in *.
  intros.
  inversion_by computes_to_inv.
  eauto.
Qed.

Add Parametric Morphism `{LookupContext} A B
: (@Bind _ A B)
    with signature
    (@refineEquiv A _ _)
      ==> (pointwise_relation _ (@refineEquiv B _ _))
      ==> (@refineEquiv B _ _)
      as refineEquiv_bind.
Proof.
  simpl; intros.
  unfold pointwise_relation, refineEquiv, refine in *.
  split_and; simpl in *.
  split; intros;
  inversion_by computes_to_inv;
  eauto.
Qed.

(*Add Parametric Morphism `{LookupContext} A B
: (@Bind names dom cod A B)
    with signature
    (@refineEquiv A names dom cod names dom cod lookup lookup)
      ==> (pointwise_relation _ (@refineEquiv B names dom cod names dom cod lookup lookup))
      ==> (@refine B names dom cod names dom cod lookup lookup)
      as refineEquiv_refine_bind.
Proof.
  intros.
  refine (proj1 (_ : refineEquiv _ _ _ _)).
  simpl in *.
  setoid_rewrite <- H.
  setoid_rewrite_hyp.
  reflexivity.
Qed.*)
