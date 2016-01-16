Require Import Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms.

Export Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Export Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms.

Ltac pick := erewrite refine_pick_val by eauto.
Ltac pick_by H := erewrite refine_pick_val by (eapply H; eauto).

Hint Resolve refine_pick_val.
Hint Rewrite <- app_nil_end.

Definition testnil A B (ls : list A) (cnil ccons : B) : B :=
  match ls with
  | nil => cnil
  | _ :: _ => ccons
  end.

Lemma refine_testnil : forall A (ls : list A) B (c1 cnil ccons : Comp B),
  (ls = nil -> refine c1 cnil)
  -> (ls <> nil -> refine c1 ccons)
  -> refine c1 (testnil ls cnil ccons).
Proof.
  destruct ls; intuition congruence.
Qed.

Add Parametric Morphism A B
: (@testnil A (Comp B))
    with signature
    @eq (list A)
      ==> @refine B
      ==> @refine B
      ==> @refine B
      as refine_testnil_morphism.
Proof.
  destruct y; auto.
Qed.

Lemma refine_testnil_ret : forall A B (ls : list A) (cnil ccons : B),
  refine (testnil ls (ret cnil) (ret ccons)) (ret (testnil ls cnil ccons)).
Proof.
  destruct ls; reflexivity.
Qed.

Ltac refine_testnil ls' := etransitivity; [ apply refine_testnil with (ls := ls'); intro | ].

Definition let_ A B (v : A) (f : A -> B) := let x := v in f v.

Add Parametric Morphism A B
: (@let_ A (Comp B))
    with signature
    @eq A
      ==> pointwise_relation _ (@refine B)
      ==> @refine B
      as refine_let_morphism.
Proof.
  unfold pointwise_relation, let_; auto.
Qed.

Lemma refine_let : forall A B (v : A) c1 (c2 : A -> Comp B),
  (forall x, x = v -> refine c1 (c2 x))
  -> refine c1 (let_ v c2).
Proof.
  unfold let_; auto.
Qed.

Ltac refine_let x := apply (refine_let (v := x)); intros.

Lemma refine_let_ret : forall A B (v : A) (f : A -> B),
  let_ v (fun x => ret (f x)) =  ret (let_ v f).
Proof.
  reflexivity.
Qed.

Ltac monad_simpl := autosetoid_rewrite with refine_monad; simpl.

Hint Rewrite refine_let_ret refine_testnil_ret : cleanup.

Global Opaque let_.

Ltac done := try match goal with
                 | [ |- refine ?a ?b ] => is_evar b; instantiate (1 := a)
                 end; finish honing.
Ltac cleanup := autorewrite with cleanup.
Ltac finalize := finish_SharpeningADT_WithoutDelegation.

Lemma tl_cons : forall A (x : A) ls1 ls2,
  x :: ls1 = ls2
  -> ls1 = tl ls2.
Proof.
  destruct ls2; simpl; congruence.
Qed.

Hint Resolve tl_cons.

Lemma appendone_contra : forall A (ls : list A) x, ls ++ x :: nil = nil
  -> False.
Proof.
  intros.
  apply (f_equal (@length _)) in H.
  rewrite app_length in H.
  simpl in *; omega.
Qed.

Hint Immediate appendone_contra.
  