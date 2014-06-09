Require Import List Bool OrderedType Morphisms Setoid.

Definition SetEq {A: Type} (seq1: list A) (seq2: list A) :=
  forall x,
    List.In x seq1 <-> List.In x seq2.

Lemma SetEq_rewrite :
  forall {A: Type} (seq1 seq2: list A),
    SetEq seq1 seq2 <-> forall a, List.In a seq1 <-> List.In a seq2.
  unfold SetEq; tauto.
Qed.

Ltac autospecialize :=
  repeat match goal with
           | [ H: forall _, _ |- List.In ?x _ ] => try specialize (H x)
         end.

Lemma SetEq_Reflexive :
  forall {A: Type}, forall (x: list A), SetEq x x.
Proof.
  unfold Reflexive, SetEq;
  intuition;
  autospecialize;
  intuition.
Qed.

Lemma SetEq_Symmetric :
  forall {A: Type}, forall (x y: list A), SetEq x y -> SetEq y x.
Proof.
  unfold Symmetric, SetEq;
  intuition; autospecialize; intuition.
Qed.

Lemma SetEq_Transitive :
  forall {A: Type}, forall (x y z: list A), SetEq x y -> SetEq y z -> SetEq x z.
Proof.
  unfold Transitive, SetEq;
  intuition; autospecialize; intuition.
Qed.

Lemma SetEq_Equivalence:
  forall {A: Type}, Equivalence (SetEq (A:=A)).
Proof.
  intros; constructor; eauto using SetEq_Transitive, SetEq_Symmetric, SetEq_Reflexive.
Qed.

Require Import Setoid.

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

Ltac seteq_equivalence :=
  eauto using SetEq_Transitive, SetEq_Symmetric, SetEq_Reflexive.

Lemma SetEq_Symmetric_iff:
  forall {A: Type}, forall (x y: list A), SetEq x y <-> SetEq y x.
Proof.
  split; seteq_equivalence.
Qed.

Lemma SetEq_trans_iff:
  forall {A: Type} (seq1 seq1' seq2: list A),
    SetEq seq1 seq1' ->
    (SetEq seq1 seq2 <-> SetEq seq1' seq2).
Proof.
  intuition; seteq_equivalence.
Qed.

Lemma SetEq_trans_iff_2:
  forall {A: Type} (seq1 seq2 seq2': list A),
    SetEq seq2 seq2' ->
    (SetEq seq1 seq2 <-> SetEq seq1 seq2').
Proof.
  intuition; seteq_equivalence.
Qed.

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

Definition SetUnion {A: Type} (x y: list A) := (x ++ y)%list.

Lemma union_left :
  forall {A: Type} (x: A) (seq1 seq2: list A),
    SetEq (SetUnion (x::seq1) seq2) (x :: (SetUnion seq1 seq2)).
Proof.
  intros; unfold SetEq, SetUnion; intuition.
Qed.

Lemma union_right :
  forall {A: Type} (x: A) (seq1 seq2: list A),
    SetEq (SetUnion seq1 (x::seq2)) (x :: (SetUnion seq1 seq2)).
Proof.
  intros; unfold SetEq, SetUnion; intuition;
  repeat (rewrite in_app_iff in *; simpl in *);
  intuition.
Qed.

Lemma filter_union :
  forall {A: Type} (seq1 seq2: list A),
  forall (pred: A -> bool),
    SetEq (List.filter pred (SetUnion seq1 seq2))
          (SetUnion (List.filter pred seq1) (List.filter pred seq2)).
Proof.
  unfold SetEq, SetUnion;
  split;
  intros;
  rewrite filter_In, in_app_iff in *;
  rewrite ! filter_In in *;
  tauto.
Qed.

Lemma SetEq_append :
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

Add Parametric Morphism {A: Type} (ens: A -> Prop) :
  (EnsembleListEquivalence ens)
    with signature (@SetEq A ==> @iff)
      as ensemble_list_equivalence_morphism.
Proof.
  firstorder.
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

Definition flatten {A} := List.fold_right (@app A) nil.

Lemma in_flatten_iff :
  forall {A} y,
    forall x, @List.In A x (flatten y) <->
              exists y0, @List.In A x y0 /\ @List.In (list A) y0 y.
Proof.
  intros A bag.
  induction bag as [ | sublist bag' IH ]; simpl.

  firstorder.

  intros elem; rewrite in_app_iff.
  split; [intro in_flattened | intro in_sublist].

  firstorder.
  destruct in_sublist as [sublist' (elem_in_sublist' & H)].

  destruct H;
    subst;
    firstorder.
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

  Lemma SetUnion_Or :
    forall {A: Type}
           {ens1 ens2: A -> Prop}
           {seq1 seq2: list A},
      EnsembleListEquivalence ens1 seq1 ->
      EnsembleListEquivalence ens2 seq2 ->
      EnsembleListEquivalence (fun x => ens1 x \/ ens2 x) (SetUnion seq1 seq2).
  Proof.
    unfold EnsembleListEquivalence, SetUnion, Ensembles.In;
    intros A ens1 ens2 seq1 seq2 eq1 eq2 x;
    specialize (eq1 x);
    specialize (eq2 x);
    rewrite in_app_iff;
    tauto.
  Qed.

  Lemma equiv_EnsembleListEquivalence:
    forall {A: Type} {seq ens1 ens2},
      (forall (x: A), ens1 x <-> ens2 x) ->
      EnsembleListEquivalence ens1 seq ->
      EnsembleListEquivalence ens2 seq.
  Proof.
    intros A ? ? ? equiv;
    unfold EnsembleListEquivalence;
    intros same_1 x;
    specialize (equiv x);
    specialize (same_1 x);
    intuition.
  Qed.
