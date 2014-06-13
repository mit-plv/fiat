Require Import SetEq Setoid AdditionalLemmas List Sorting.Permutation.

Definition IsSetEqSafe {A B: Type} (proc: list A -> list B) :=
  forall (seq1 seq2: list A),
    SetEq seq1 seq2 ->
    SetEq (proc seq1) (proc seq2).

Lemma SetEq_modulo_SetEqSafe_fun :
  forall {A B: Type},
  forall (seq1: list B) (seq2 seq3: list A),
  forall (proc: list A -> list B),
    SetEq seq2 seq3 ->
    IsSetEqSafe proc ->
    (SetEq seq1 (proc seq2) <-> SetEq seq1 (proc seq3)).
Proof.
  intros; eauto using SetEq_trans_iff_2.
Qed.

Lemma SetEq_after_map :
  forall {A B: Type} (seq1 seq2: list A),
  forall (proc: A -> B),
    SetEq seq1 seq2 -> SetEq (map proc seq1) (map proc seq2).
Proof.
  intros ? ? ? ? ? set_eq;
  unfold SetEq in *;
  intro x;
  split;
  intros in_map;
  rewrite in_map_iff in in_map;
  destruct in_map as [pred (is_pred, pred_in_list)];
  specialize (set_eq pred);
  subst;
  intuition;
  eauto using in_map.
Qed.

Lemma map_modulo_SetEq :
  forall {A B: Type} (seq1 seq1': list A) (seq2: list B),
  forall (proc: A -> B),
    SetEq seq1 seq1' ->
    (SetEq (map proc seq1) (seq2) <-> SetEq (map proc seq1') (seq2)).
Proof.
  intros;
  simpl;
  apply SetEq_trans_iff;
  apply SetEq_after_map;
  trivial.
Qed.

Lemma IsSetEqSafe_map :
  forall {A B: Type} (proc: A -> B),
    IsSetEqSafe (fun x => List.map proc x).
Proof.
  unfold IsSetEqSafe;
  eauto using SetEq_after_map.
Qed.

Lemma IsSetEqSafe_filter :
  forall {A: Type} (pred: A -> bool),
    IsSetEqSafe (fun x => List.filter pred x).
Proof.
  unfold IsSetEqSafe, SetEq;
  intros;
  repeat rewrite filter_In;
  specialize (H x);
  intuition.
Qed.

Add Parametric Relation (A: Type) : (list A) (@SetEq A)
    reflexivity proved by SetEq_Reflexive
    symmetry proved by SetEq_Symmetric
    transitivity proved by SetEq_Transitive
      as set_eq.

Add Parametric Morphism {A: Type} (x: A) :
  (List.In x)
    with signature (@SetEq A ==> iff)
      as in_morphism.
Proof.
  intros s1 s2;
  unfold SetEq;
  intros;
  eauto.
Qed.

Add Parametric Morphism {A B: Type} (proc: A -> B) :
  (List.map proc)
    with signature (@SetEq A ==> @SetEq B)
      as map_morphism.
Proof.
  apply IsSetEqSafe_map.
Qed.

Add Parametric Morphism {A: Type} (pred: A -> bool) :
  (List.filter pred)
    with signature (@SetEq A ==> @SetEq A)
      as filter_morphism.
Proof.
  apply IsSetEqSafe_filter.
Qed.

Require Import EnsembleListEquivalence.
Hint Resolve Permutation_in.

Lemma NoDup_Permutation {A} :
  forall (l l' : list A),
    Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  intros; induction H.
  + econstructor.
  + inversion H0; subst; econstructor; eauto.
    unfold not; intros; apply H3; apply Permutation_sym in H;
    eapply Permutation_in; eauto.
  + inversion H0; subst; inversion H3; subst; repeat econstructor; eauto.
    * unfold not; intros; destruct H; eauto.
      apply H2; econstructor; eauto.
    * unfold not; intros; apply H2; econstructor 2; eauto.
  + eauto.
Qed.

Add Parametric Morphism {A: Type} (ens: A -> Prop) :
  (EnsembleListEquivalence ens)
    with signature (@Permutation A ==> @iff)
      as ensemble_list_equivalence_morphism.
Proof.
  firstorder; try eauto using NoDup_Permutation.
  eapply Permutation_in; eauto; eapply H1; eauto.
  eapply Permutation_sym in H; eapply H1; eapply Permutation_in; eauto.
  apply Permutation_sym in H; try eauto using NoDup_Permutation.
  apply Permutation_sym in H; eapply Permutation_in; eauto; eapply H1; eauto.
  eapply H1; eapply Permutation_in; eauto.
Qed.

Add Parametric Morphism {A: Type} :
  flatten
    with signature (@SetEq (list A) ==> @SetEq A)
      as concat_right_morphism.
Proof.
  unfold SetEq;
  setoid_rewrite in_flatten_iff;
  firstorder.
Qed.

Add Parametric Morphism {A: Type} : (@SetUnion A)
    with signature (@SetEq A ==> @SetEq A ==> @SetEq A)
      as union_morphism.
Proof.
  unfold SetEq, SetUnion;
  intros;
  rewrite ! in_app_iff;
  intuition;
  repeat match goal with
           | [ H: List.In ?x _, H': forall _, _ |- _ ] => try specialize (H' x)
         end;
  tauto.
Qed.

Lemma SetEq_append : (* TODO: Rename to cons *)
  forall {A: Type} (seq1 seq2: list A) (x: A),
    SetEq seq1 seq2 -> SetEq (x :: seq1) (x :: seq2).
Proof.
  intros A s1 s2 x s_eq;
  unfold SetEq;
  split; intro H;
  simpl in *;
  [rewrite s_eq in H | rewrite <- s_eq in H];
  intuition.
Qed.

Lemma seteq_nil_nil :
  forall {A} seq,
    @SetEq A seq nil <-> seq = nil.
Proof.
  unfold SetEq.
  intros; destruct seq.

  tauto.
  split; [ | discriminate ].
  intro H; specialize (H a).
  exfalso; simpl in H; rewrite <- H; eauto.
Qed.

Lemma seteq_nil_nil' :
  forall {A} seq,
    @SetEq A nil seq <-> seq = nil.
Proof.
  setoid_rewrite SetEq_Symmetric_iff.
  intro; exact seteq_nil_nil.
Qed.
