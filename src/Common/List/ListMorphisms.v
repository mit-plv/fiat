Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Import Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.Common.List.ListFacts
        Fiat.Common.List.Operations
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

Global Add Parametric Morphism {A B} : (@List.fold_right A B)
    with signature pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq
      as fold_right_f_eq_mor.
Proof.
  intros ?? H k ls; revert k; lazy in H.
  induction ls; intros; simpl; trivial.
  rewrite IHls, H; reflexivity.
Defined.

Global Add Parametric Morphism {A B} : (@List.fold_left A B)
    with signature pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq
      as fold_left_f_eq_mor.
Proof.
  intros ?? H ls k; revert k; lazy in H.
  induction ls; intros; simpl; trivial.
  rewrite IHls, H; reflexivity.
Defined.

Global Instance filter_Proper {A}
: Proper (pointwise_relation _ eq ==> eq ==> eq)
         (@filter A).
Proof.
  intros ?? H ? ls ?; subst.
  induction ls; trivial; simpl; rewrite IHls, H; reflexivity.
Qed.

Global Instance filter_out_Proper {A}
: Proper (pointwise_relation _ eq ==> eq ==> eq)
         (@filter_out A).
Proof.
  intros ?? H ? ls ?; subst.
  induction ls; trivial; simpl; rewrite IHls, H; reflexivity.
Qed.

Global Instance cons_eqlistA_Proper {T} {R : relation T}
: Proper (R ==> SetoidList.eqlistA R ==> SetoidList.eqlistA R) cons.
Proof.
  repeat intro.
  apply SetoidList.eqlistA_cons; assumption.
Qed.

Global Instance eqlistA_length_Proper {A eqA}
: Proper (@SetoidList.eqlistA A eqA ==> eq) (@List.length _).
Proof.
  intros x y H; induction H; simpl; f_equal; trivial.
Qed.

Global Instance eqlistA_eq_Proper {A B f}
: Proper (@SetoidList.eqlistA A eq ==> @eq B) f | 100.
Proof.
  intros ?? H; apply eqlistA_eq in H; subst; reflexivity.
Qed.

Global Instance flat_map_Proper {A B}
: Proper (pointwise_relation _ eq ==> eq ==> eq) (@flat_map A B).
Proof.
  unfold pointwise_relation.
  intros ?? H ? ls ?; subst.
  induction ls as [|?? IHls]; simpl.
  { reflexivity. }
  { rewrite IHls, H; reflexivity. }
Qed.

(** Increase priority of [eq] instance for [cons] *)
Global Instance : forall T, Proper (eq ==> eq ==> eq) (@cons T) := _.

Global Instance list_caset_Proper_forall {A P}
: Proper (eq ==> forall_relation (fun _ => forall_relation (fun _ => eq)) ==> forall_relation (fun _ => eq))
         (@list_caset A P).
Proof.
  lazy.
  intros ??? ?? H [|? ?]; subst; eauto.
Qed.
Global Instance list_caset_Proper {A P}
: Proper (eq
            ==> pointwise_relation _ (pointwise_relation _ eq)
            ==> pointwise_relation _ eq)
         (@list_caset A (fun _ => P)).
Proof.
  lazy.
  intros ??? ?? H [|? ?]; subst; eauto.
Qed.

Global Instance list_caset_Proper' {A P}
: Proper (eq
            ==> pointwise_relation _ (pointwise_relation _ eq)
            ==> eq
            ==> eq)
         (@list_caset A (fun _ => P)).
Proof.
  lazy.
  intros ??? ?? H [|? ?] ??; subst; eauto.
Qed.

Global Instance list_caset_Proper_forall' {A P}
: Proper (eq
            ==> pointwise_relation _ (pointwise_relation _ eq)
            ==> forall_relation (fun _ => eq))
         (@list_caset A (fun _ => P)).
Proof.
  lazy.
  intros ??? ?? H [|? ?]; subst; eauto.
Qed.

Global Instance eqlistA_Reflexive {A R} {_ : @Reflexive A R}
  : Reflexive (SetoidList.eqlistA R).
Proof.
  intro x; induction x as [|x xs IHxs]; constructor;
    first [ assumption
          | reflexivity ].
Qed.
Lemma map_eqlistA_Proper {A B R}
  : Proper (pointwise_relation _ R ==> eq ==> SetoidList.eqlistA R) (@List.map A B).
Proof.
  unfold pointwise_relation.
  intros f g H ? ls ?; subst.
  induction ls as [|l ls IHls]; constructor;
    trivial.
Qed.

Hint Extern 0 (Proper (_ ==> _ ==> SetoidList.eqlistA _) (@List.map _ _))
=> refine map_eqlistA_Proper : typeclass_instances.

Global Instance list_caset_Proper_forall_R {A B} {R : relation B}
  : Proper
      (R
         ==> (pointwise_relation _ (pointwise_relation _ R))
         ==> forall_relation (fun _ => R))
      (@list_caset A (fun _ => B)).
Proof.
  lazy; intros ?????? [|??]; trivial.
Qed.
Hint Extern 0 (Proper (_ ==> pointwise_relation _ (pointwise_relation _ _) ==> forall_relation _) (list_caset _))
=> refine list_caset_Proper_forall_R : typeclass_instances.

Lemma fold_left_eqlistA_Proper {A B} {RA : relation A} {RB : relation B}
  : Proper ((RA ==> RB ==> RA) ==> SetoidList.eqlistA RB ==> RA ==> RA) (@fold_left A B).
Proof.
  unfold respectful.
  intros ?? H ls1 ls2 H'.
  induction H'; simpl; eauto with nocore.
Qed.
Hint Extern 0 (Proper (_ ==> SetoidList.eqlistA _ ==> _ ==> _) (@fold_left _ _))
=> refine fold_left_eqlistA_Proper : typeclass_instances.

Global Instance first_index_helper_Proper_pointwise {A B}
  : Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> pointwise_relation _ eq ==> eq) (@first_index_helper A B).
Proof.
  unfold pointwise_relation, respectful.
  intros f g H f' g' H' ? ls ?; subst.
  induction ls as [|l ls IHls]; simpl; intros ?? H''; trivial.
  rewrite H, H', H''.
  erewrite IHls; [ reflexivity | ].
  congruence.
Qed.

Global Instance first_index_default_Proper_pointwise {A}
  : Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq) (@first_index_default A).
Proof.
  unfold first_index_default.
  repeat intro; subst; apply first_index_helper_Proper_pointwise; try assumption; repeat intro; trivial.
Qed.

Global Instance NoDupA_compat {A eqA} {_ : @Equivalence A eqA}
  : Proper (SetoidList.eqlistA eqA ==> iff) (SetoidList.NoDupA eqA).
Proof.
  intros ls ls' H'.
  induction H' as [|???? H0 H1 IH]; [ reflexivity | ].
  split; intro H'; inversion H'; clear H'; subst; constructor;
    try apply IH;
    try rewrite <- H0, <- H1;
    try assumption;
    try rewrite H0, H1;
    try assumption.
Qed.

Global Instance InA_Proper_iff_iff {A}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@SetoidList.InA A) | 5.
Proof.
  unfold pointwise_relation.
  intros eqA eqA' HeqA a a' ? ls ls' ?; subst a' ls'; split;
    split_iff;
    induction ls as [|x xs IHxs];
    intro H'; inversion H'; intuition eauto.
Qed.

Global Instance InA_Proper_iff_impl {A}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> impl) (@SetoidList.InA A) | 5.
Proof. repeat intro; eapply InA_Proper_iff_iff; first [ eassumption | symmetry; eassumption ]. Qed.
Global Instance InA_Proper_iff_flip_impl {A}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> flip impl) (@SetoidList.InA A) | 5.
Proof. repeat intro; eapply InA_Proper_iff_iff; first [ eassumption | symmetry; eassumption ]. Qed.

Global Instance NoDupA_Proper_iff_iff {A}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> iff) (@SetoidList.NoDupA A) | 5.
Proof.
  intros eqA eqA' HeqA ls ls' ?; subst ls'; split;
    induction ls as [|x xs IHxs];
    intro H'; inversion H'; clear H'; subst; constructor;
      try solve [ auto
                | setoid_rewrite <- HeqA; auto
                | setoid_rewrite HeqA; auto ].
Qed.
Global Instance NoDupA_Proper_iff_impl {A}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> impl) (@SetoidList.NoDupA A) | 5.
Proof. repeat intro; eapply NoDupA_Proper_iff_iff; first [ eassumption | symmetry; eassumption ]. Qed.
Global Instance NoDupA_Proper_iff_flip_impl {A}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> flip impl) (@SetoidList.NoDupA A) | 5.
Proof. repeat intro; eapply NoDupA_Proper_iff_iff; first [ eassumption | symmetry; eassumption ]. Qed.

Global Instance Proper_fold_right_Prop_iff
  : Proper ((iff ==> iff ==> iff) ==> iff ==> eq ==> iff) (fold_right (B:=Prop)) | 5.
Proof.
  unfold respectful; intros ?? H0 ?? H1 xs ys ?; subst ys.
  induction xs; [ assumption | simpl; rewrite H0 by (eassumption || reflexivity); reflexivity ].
Qed.

Global Instance fold_right_Proper_rel {A B R}
  : Proper (pointwise_relation _ (R ==> R) ==> R ==> eq ==> R) (@List.fold_right A B) | 10.
Proof.
  intros f g H a b H0 ls y ?; subst y.
  induction ls as [|x xs IHxs]; [ exact H0 | ].
  simpl; apply H, IHxs.
Qed.

Global Instance fold_right_Proper_rel_eqlistA {A B RA RB}
  : Proper ((RB ==> RA ==> RA) ==> RA ==> SetoidList.eqlistA RB ==> RA) (@List.fold_right A B) | 10.
Proof.
  intros f g H a b H0 ls.
  induction ls as [|x xs IHxs]; intros [|y ys] Hls;
    inversion Hls; subst; simpl;
      [ assumption
      | apply H, IHxs; assumption ].
Qed.
