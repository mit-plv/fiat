Require Import Coq.Lists.List Coq.Bool.Bool Coq.Structures.OrderedType Coq.Classes.Morphisms Coq.Setoids.Setoid.

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

Ltac seteq_equivalence :=
  eauto using SetEq_Transitive, SetEq_Symmetric, SetEq_Reflexive.

Lemma SetEq_Equivalence:
  forall {A: Type}, Equivalence (SetEq (A:=A)).
Proof.
  intros; constructor; seteq_equivalence.
Qed.

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
