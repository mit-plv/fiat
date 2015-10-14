Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Import Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.Common.List.ListFacts
        Fiat.Common.List.PermutationFacts.

Require Import Fiat.Common.List.FlattenList.

Unset Implicit Arguments.

Add Parametric Morphism {A B: Type} :
  (fun comp seq => List.map comp seq)
    with signature (pointwise_relation A (@eq B) ==> eq ==> (@eq (list B)))
      as map_eq_morphism.
Proof.
  unfold pointwise_relation;
  intros * equiv seq;
  induction seq as [ | ? ? IH ]; simpl; [ | rewrite IH, equiv ]; trivial.
Qed.

Add Parametric Morphism {A B: Type} (seq: list A) :
  (fun comp => List.map comp seq)
    with signature (pointwise_relation A (@eq B) ==> (@eq (list B)))
      as map_eq_restricted_morphism.
Proof.
  intros.
  setoid_rewrite H; trivial.
Qed.

Add Parametric Morphism {A: Type} :
  (@List.filter A)
    with signature (pointwise_relation A (@eq bool) ==> @eq (list A) ==> @eq (list A))
      as filter_eq_morphism.
Proof.
  intros * equiv seq;
  unfold pointwise_relation in equiv;
  induction seq as [ | h t IH ];
  simpl;
  [ | rewrite equiv, IH ];
  trivial.
Qed.

Add Parametric Morphism {A: Type} (seq: list A) :
  (fun pred => @List.filter A pred seq)
    with signature (pointwise_relation A (@eq bool) ==> @eq (list A))
      as filter_eq_restricted_morphism.
Proof.
  intros * equiv;
  erewrite filter_eq_morphism; eauto.
Qed.

Add Parametric Morphism {A} :
  (@List.length A)
    with signature (@Permutation A ==> eq)
      as list_length_permutation_eq_morphism.
Proof.
  apply Permutation_length.
Qed.

Add Parametric Morphism {A B: Type} :
  (@List.map A B)
    with signature (pointwise_relation A (@eq B) ==> @Permutation A ==> @Permutation B)
      as map_permutation_morphism.
Proof.
  unfold pointwise_relation;
  intros * equiv seq1 seq2 is_perm.

  induction is_perm; simpl; rewrite ?equiv.

  constructor.
  constructor; eauto.
  erewrite map_eq_restricted_morphism; eauto; constructor.
  econstructor; eauto; cbv beta; erewrite map_eq_restricted_morphism; eauto; symmetry; eassumption.
Qed.

Ltac destruct_ifs :=
  repeat match goal with
           | [ |- context [ if ?A then _ else _ ] ] => destruct A
         end.

Add Parametric Morphism {A: Type} :
  (@List.filter A)
    with signature (pointwise_relation A (@eq bool) ==> @Permutation A ==> @Permutation A)
      as filter_permutation_morphism.
Proof.
  intros * equiv * is_perm.

  induction is_perm; simpl; rewrite ?equiv.

  constructor.
  destruct_ifs; try constructor;
  erewrite filter_eq_restricted_morphism; eauto; symmetry; eassumption.
  destruct_ifs; try constructor;
  erewrite filter_eq_restricted_morphism; eauto; symmetry; eassumption.
  econstructor. erewrite filter_eq_restricted_morphism; try (symmetry; eassumption).
  eauto. erewrite filter_eq_restricted_morphism; try (symmetry; eassumption).
  eassumption.
Qed.

Add Parametric Morphism {A: Type} :
  (@List.In A)
    with signature (@eq A ==> @Permutation A ==> iff)
      as in_permutation_morphism.
Proof.
  intros * is_perm.
  split; apply Permutation_in; intuition.
Qed.

Add Parametric Morphism {A: Type} :
  (@flatten A)
    with signature (@Permutation (list A) ==> @Permutation A)
      as flatten_permutation_morphism.
Proof.
  intros * is_perm.

  induction is_perm; simpl.

  constructor.
  apply Permutation_app_head; trivial.
  rewrite ?List.app_assoc; apply Permutation_app_tail; apply Permutation_app_comm.
  econstructor; eauto.
Qed.

Add Parametric Morphism {A B : Type} :
  (fun comp seq => @flatten B (@List.map A (list B) comp seq))
    with signature (pointwise_relation A (@Permutation B) ==> @eq (list A) ==> @Permutation B)
      as flatten_map_permutation_eq_permutation_morphism.
Proof.
  intros * equiv seq.

  induction seq; simpl.
  constructor.
  apply Permutation_app; eauto.
Qed.

Add Parametric Morphism {A B : Type} :
  (@flat_map A B)
    with signature (pointwise_relation A (@Permutation B) ==> @eq (list A) ==> @Permutation B)
      as flatmap_permutation_eq_permutation_morphism.
Proof.
  intros.
  rewrite ?flat_map_flatten.
  apply flatten_map_permutation_eq_permutation_morphism; eauto.
Qed.

Add Parametric Morphism {A B: Type} :
  (fun comp seq => @flatten B (@List.map A (list B) comp seq))
    with signature (pointwise_relation A (@Permutation B) ==> @Permutation A ==> @Permutation B)
      as flatten_map_permutation_permutation_permutation_morphism.
Proof.
  unfold pointwise_relation;
  intros * equiv seq1 seq2 is_perm.

  induction is_perm; simpl.

  constructor.
  apply Permutation_app; eauto.

  rewrite ?List.app_assoc.
  apply Permutation_app.
  rewrite Permutation_app_comm;
    apply Permutation_app; apply equiv.

  apply flatten_map_permutation_eq_permutation_morphism; eauto.

  etransitivity;
    [ etransitivity; [ eauto | ] | eauto ].

  apply flatten_map_permutation_eq_permutation_morphism; try (symmetry; eauto).
Qed.

Add Parametric Morphism {A B : Type} :
  (@flat_map A B)
    with signature (pointwise_relation A (@Permutation B) ==> @Permutation A ==> @Permutation B)
      as flatmap_permutation_permutation_permutation_morphism.
Proof.
  intros.
  rewrite ?flat_map_flatten.
  apply flatten_map_permutation_permutation_permutation_morphism; eauto.
Qed.

Add Parametric Morphism {A B} :
  (@flat_map A B)
    with signature (pointwise_relation A eq ==> eq ==> eq)
      as flat_map_pointwiseeq_eq_eq_morphism_Proper.
Proof.
  intros * equiv seq.
  induction seq; simpl; [ | rewrite equiv, IHseq ]; reflexivity.
Qed.

Add Parametric Morphism {A B} :
  (flat_map (B := A * B))
    with signature (pointwise_relation A eq ==> eq ==> eq)
      as flat_map_pair_pointwiseeq_eq_eq_morphism.
Proof.
  intros * equiv seq.
  induction seq; simpl; [ | rewrite IHseq, equiv ]; reflexivity.
Qed.

Add Parametric Morphism {A: Type} :
  (@app A)
    with signature (@Permutation A ==> @Permutation A ==> @Permutation A)
      as app_permutation_permutation_permutation_morphism.
Proof.
  intros; apply Permutation_app; assumption.
Qed.

Add Parametric Morphism {A: Type} :
  (@rev A)
    with signature (@Permutation A ==> @Permutation A)
      as rev_permutation_permutation_morphism.
Proof.
  intros; rewrite <- !Permutation_rev; eassumption.
Qed.

Definition pointwise2_relation :=
  fun (A A': Type) {B : Type} (R : relation B) (f g : A -> A' -> B) =>
    forall a a', R (f a a') (g a a').

Add Parametric Morphism {A B: Type} :
  (@List.fold_right A B)
    with signature (@pointwise2_relation B A _ eq ==> eq ==> eq ==> eq)
      as fold_right_pointwise2eq_eq_eq_morphism.
Proof.
  intros * equiv default seq.
  induction seq; simpl.

  reflexivity.
  rewrite IHseq; apply equiv.
Qed.

Add Parametric Morphism {A B: Type} :
  (@List.fold_left A B)
    with signature (pointwise2_relation A B eq ==> eq ==> eq ==> eq)
      as fold_left_pointwise2eq_eq_eq_morphism.
Proof.
  intros.
  rewrite <- !fold_left_rev_right.
  setoid_rewrite H; reflexivity.
Qed.

Add Parametric Morphism {A: Type} (ens: A -> Prop) :
  (EnsembleListEquivalence ens)
    with signature (@Permutation A ==> @iff)
      as ensemble_list_equivalence_morphism.
Proof.
  intros.
  unfold EnsembleListEquivalence in *. intuition.
  - eauto using NoDup_Permutation_rewrite.
  - eapply Permutation_in. apply H. apply H2. auto.
  - apply H2. eapply Permutation_in. eapply Permutation_sym. apply H. auto.
  - eapply NoDup_Permutation_rewrite; [symmetry | ]; eauto.
  - eapply Permutation_in. eapply Permutation_sym. apply H. apply H2. auto.
  - apply H2. eapply Permutation_in. apply H. auto.
Qed.

Global Instance list_rect_Proper {A P}
: Proper (eq ==> (forall_relation (fun _ => forall_relation (fun _ => pointwise_relation _ eq))) ==> forall_relation (fun _ => eq))
         (@list_rect A P).
Proof.
  intros ????? H ls.
  subst.
  induction ls; simpl; [ reflexivity | rewrite H, IHls; reflexivity ].
Qed.

Lemma list_rect_ext
      {A P}
      P0 P0'
      Pc Pc'
      ls
      (H0 : P0 = P0')
      (Hc : forall a l Pl, Pc a l Pl = Pc' a l Pl)
: @list_rect A P P0 Pc ls = @list_rect A P P0' Pc' ls.
Proof.
  apply list_rect_Proper; lazy; assumption.
Qed.


Global Instance list_rect_Proper_forall_nondep
       {A T}
: Proper (eq
            ==> forall_relation (fun a => forall_relation (fun l => pointwise_relation _ eq))
            ==> eq
            ==> eq)
         (@list_rect A (fun _ => T)).
Proof.
  intros ? x ??? H ? ls' ?; subst.
  revert x; induction ls' as [|l' ls' IHls']; intros; simpl.
  { reflexivity. }
  { rewrite IHls'.
    apply H. }
Qed.
