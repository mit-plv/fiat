Require Import Coq.Lists.List Coq.Lists.SetoidList Fiat.Common.

Unset Implicit Arguments.

Section FlattenList.
  Definition flatten {A} seq := List.fold_right (@app A) [] seq.

  Lemma flat_map_flatten :
    forall {A B: Type},
    forall comp seq,
      @flat_map A B comp seq = flatten (map comp seq).
  Proof.
    intros; induction seq; simpl; try rewrite IHseq; reflexivity.
  Qed.

  Lemma in_flatten_iff :
    forall {A} x seqs,
      @List.In A x (flatten seqs) <->
      exists seq, List.In x seq /\ List.In seq seqs.
  Proof.
    intros; unfold flatten.
    induction seqs; simpl.

    firstorder.
    rewrite in_app_iff.
    rewrite IHseqs.

    split.
    intros [ in_head | [seq (in_seqs & in_seq) ] ]; eauto.
    intros [ seq ( in_seq & [ eq_head | in_seqs ] ) ]; subst; eauto.
  Qed.

  Lemma flatten_filter :
    forall {A} (seq: list (list A)) pred,
      List.filter pred (flatten seq) =
      flatten (List.map (List.filter pred) seq).
  Proof.
    intros; induction seq; trivial.
    unfold flatten; simpl.
    induction a; trivial.
    simpl;
      destruct (pred a); simpl; rewrite IHa; trivial.
  Qed.

  Lemma map_flatten :
    forall {B C} (f: B -> C) (xs: list (list B)),
      map f (flatten xs) = flatten (map (fun x => map f x) xs).
  Proof.
    induction xs; simpl;
    [ | rewrite map_app, IHxs ]; reflexivity.
  Qed.

  Lemma map_flat_map :
    forall {A B C} (f: B -> C) (g: A -> list B) (xs: list A),
      map f (flat_map g xs) = flat_map (fun x : A => map f (g x)) xs.
  Proof.
    intros;
    rewrite flat_map_flatten, map_flatten, map_map, <- flat_map_flatten;
    reflexivity.
  Qed.

  Lemma flatten_nils :
    forall {A} (seq: list (list A)),
      flatten (List.map (fun _ => []) seq) = @nil A.
  Proof.
    induction seq; intuition.
  Qed.

  Lemma flatten_app :
    forall {A} (seq1 seq2: list (list A)),
      flatten (seq1 ++ seq2) = flatten seq1 ++ flatten seq2.
  Proof.
    unfold flatten; induction seq1; simpl; trivial.
    intros; rewrite IHseq1; rewrite app_assoc; trivial.
  Qed.

  Lemma flatten_head :
    forall {A} head tail,
      @flatten A (head :: tail) = head ++ flatten tail.
  Proof.
    intuition.
  Qed.

  Require Import Coq.Arith.Arith.

  Lemma length_flatten_aux :
    forall {A} seq,
    forall n,
      n + List.length (flatten seq) = List.fold_right (compose plus (@List.length A)) n seq.
  Proof.
    induction seq; simpl; intros.

    - auto with arith.
    - unfold compose;
      rewrite app_length, <- IHseq.
      rewrite plus_comm, <- plus_assoc; auto with arith.
  Qed.

  Lemma length_flatten :
    forall {A} seq,
      List.length (flatten seq) = List.fold_right (compose plus (@List.length A)) 0 seq.
  Proof.
    intros.
    pose proof (length_flatten_aux seq 0) as H; simpl in H; eauto.
  Qed.

  Lemma filter_flat_map :
    forall {A B} g (f: B -> bool) xs,
      filter f (flat_map g xs) =
      flat_map (fun x : A => filter f (g x)) xs.
  Proof.
    intros; rewrite !flat_map_flatten.
    rewrite flatten_filter, map_map; reflexivity.
  Qed.

End FlattenList.
