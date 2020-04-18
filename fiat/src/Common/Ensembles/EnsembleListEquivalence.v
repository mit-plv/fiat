Require Import Coq.Lists.List.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Sorting.Permutation.
Require Import Fiat.Common.
Require Import Fiat.Common.List.PermutationFacts.

Definition EnsembleListEquivalence
           {A}
           (ensemble : Ensemble A)
           (seq : list A) :=
  NoDup seq /\
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.

Local Ltac perm_t :=
  repeat match goal with
           | _ => intro
           | _ => progress destruct_head_hnf and
           | _ => progress destruct_head_hnf or
           | _ => progress destruct_head_hnf Singleton
           | _ => progress split_iff
           | _ => split
           | [ H : NoDup (_::_) |- _ ] => inversion H; clear H; subst
           | [ H : ~Ensembles.In _ (Singleton _ ?a) ?x |- _ ]
             => assert (a <> x) by (intro; subst; apply H; constructor);
               clear H
           | _ => solve [ eauto ]
           | _ => congruence
         end.

Lemma Permutation_pull_to_front {T} (a : T) ls
      (H : List.In a ls)
: exists ls' : _, Permutation ls (a::ls').
Proof.
  induction ls; simpl in *; destruct_head False.
  destruct_head_hnf or; subst.
  { exists ls; reflexivity. }
  { specialize (IHls H).
    destruct IHls as [ls' H'].
    eexists (_::ls').
    etransitivity; [ apply perm_skip; exact H' | ].
    apply perm_swap. }
Qed.

Lemma EnsembleListEquivalence_Same_set U (A B : Ensemble U)
      ls
      (H : EnsembleListEquivalence A ls)
: EnsembleListEquivalence B ls <-> Same_set _ A B.
Proof.
  induction ls;
  repeat match goal with
           | _ => split
           | _ => intro
           | _ => progress destruct_head_hnf and
           | _ => progress split_iff
           | _ => progress simpl in *
           | _ => solve [ eauto ]
         end.
  Grab Existential Variables.
  assumption.
Qed.

Lemma EnsembleListEquivalence_Permutation U (A : Ensemble U)
      ls ls'
      (H : EnsembleListEquivalence A ls) (H' : EnsembleListEquivalence A ls')
: Permutation ls ls'.
Proof.
  revert A ls' H H'.
  induction ls; intros A ls' H H'.
  { destruct_head_hnf and; split_iff.
    destruct ls'; simpl in *; auto.
    specialize_all_ways.
    intuition. }
  { let H := fresh in
    let H' := fresh in
    let t := destruct_head_hnf and; split_iff; intuition in
    lazymatch goal with
      | [ |- Permutation (?a::?ls) ?ls' ]
        => assert (H : List.In a ls') by t;
          assert (H' : ~List.In a ls)
             by (intro; t; instantiate;
                 match goal with
                   | [ H'' : NoDup (_::_) |- _ ]
                     => solve [ inversion H''; subst; intuition ]
                 end)
    end;
      hnf in H.
    destruct (Permutation_pull_to_front _ _ H0) as [ls'' H''].
    symmetry in H''.
    etransitivity; [ | exact H'' ].
    apply perm_skip.
    apply (IHls (Subtract _ A a)).
    { perm_t;
      specialize_all_ways;
      perm_t. }
    { pose proof (fun x => @Permutation_in _ _ _ x H'').
      symmetry in H''.
      pose proof (fun x => @Permutation_in _ _ _ x H'').
      let H := fresh in
      assert (H : NoDup (a::ls'')) by
          (eapply PermutationFacts.NoDup_Permutation_rewrite;
           try solve [ destruct_head_hnf and; eassumption ]);
        inversion H; subst; clear H.
      perm_t; specialize_all_ways; perm_t. } }
Qed.

Lemma EnsembleListEquivalence_slice :
  forall {A} a b c (ens: Ensemble A),
    EnsembleListEquivalence ens (a ++ b ++ c) ->
    EnsembleListEquivalence (fun x => ens x /\ ~ List.In x b) (a ++ c).
Proof.
  unfold EnsembleListEquivalence, Ensembles.In; simpl;
  repeat setoid_rewrite in_app_iff; intros *.
  split.
  - intros. intuition.
    eauto using NoDup_slice.
  - intros; intuition.
    + rewrite H1 in H2; intuition.
    + rewrite H1; intuition.
    + eapply NoDup_app_inv'; eauto.
    + rewrite H1; intuition.
    + eapply NoDup_app_inv'; eauto.
Qed.


Lemma ensemble_list_equivalence_set_eq_morphism {A : Type} {ens1 ens2 : A -> Prop} :
  (forall x, Ensembles.In _ ens1 x <-> Ensembles.In _ ens2 x) ->
  forall (seq : list A),
    (EnsembleListEquivalence ens1 seq <-> EnsembleListEquivalence ens2 seq).
Proof.
  intros * equiv *;
  unfold EnsembleListEquivalence, In in *;
  setoid_rewrite equiv; reflexivity.
Qed.

Lemma EnsembleListEquivalence_lift_property {TItem: Type} {P: TItem -> Prop} :
  forall (sequence: list TItem) (ensemble: TItem -> Prop),
    EnsembleListEquivalence ensemble sequence ->
    ((forall item,
        List.In item sequence -> P item) <->
     (forall item,
        Ensembles.In _ ensemble item -> P item)).
Proof.
  intros * equiv;
  destruct equiv as [NoDup_l equiv];
  setoid_rewrite equiv;
  reflexivity.
Qed.
