Require Import Ensembles List Coq.Lists.SetoidList.

Definition EnsembleListEquivalence {A: Type} (ensemble: A -> Prop) (seq: list A) :=
  NoDup seq /\
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.

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

Definition NonNil {A: Type} (l: list A) :=
  match l with
    | nil => false
    | _  => true
  end.

Definition dec2bool {A: Type} {P: A -> Prop} (pred: forall (a: A), sumbool (P a) (~ (P a))) :=
  fun (a: A) =>
    match pred a with
      | left _  => true
      | right _ => false
    end. (* TODO: Use this *)

Definition Box {A: Type} (x: A) := cons x nil.

Definition Option2Box {A: Type} (xo: option A) :=
  match xo with
    | Some x => Box x
    | None   => nil
  end.

  Definition FilteredSet {A B} ensemble projection (value: B) :=
    fun (p: A) => ensemble p /\ projection p = value.

  Definition ObservationalEq {A B} f g :=
    forall (a: A), @eq B (f a) (g a).

Section EnsembleLemmas.
  Lemma weaken :
    forall {A: Type} ensemble condition,
    forall (x: A),
      Ensembles.In _ (fun x => Ensembles.In _ ensemble x /\ condition x) x
      -> Ensembles.In _ ensemble x.
  Proof.
    unfold Ensembles.In; intros; intuition.
  Qed.
End EnsembleLemmas.

Section ListLemmas.
  Lemma map_id :
    forall {A: Type} (seq: list A),
      (map (fun x => x) seq) = seq.
  Proof.
    intros A seq; induction seq; simpl; congruence.
  Qed.

  Lemma in_nil_iff :
    forall {A} (item: A),
      List.In item nil <-> False.
  Proof.
    intuition.
  Qed.

  Lemma in_not_nil :
    forall {A} x seq,
      @List.In A x seq -> seq <> nil.
  Proof.
    intros A x seq in_seq eq_nil.
    apply (@in_nil _ x).
    subst seq; assumption.
  Qed.

  Lemma in_seq_false_nil_iff :
    forall {A} (seq: list A),
      (forall (item: A), (List.In item seq <-> False)) <->
      (seq = nil).
  Proof.
    intros.
    destruct seq; simpl in *; try tauto.
    split; intro H.
    exfalso; specialize (H a); rewrite <- H; eauto.
    discriminate.
  Qed.

  Lemma filter_comm :
    forall {A: Type} (pred1 pred2: A -> bool),
    forall (seq: list A),
      List.filter pred1 (List.filter pred2 seq) =
      List.filter pred2 (List.filter pred1 seq).
  Proof.
    intros A pred1 pred2 seq;
    induction seq as [ | hd tl];
    [ simpl
    | destruct (pred1 hd) eqn:eq1;
      destruct (pred2 hd) eqn:eq2;
      repeat progress (simpl;
                       try rewrite eq1;
                       try rewrite eq2)
    ]; congruence.
  Qed.

  Lemma InA_In:
    forall (A : Type) (x : A) (l : list A),
      InA eq x l -> List.In x l.
  Proof.
    intros ? ? ? H;
    induction H;
    simpl;
    intuition.
  Qed.

  Lemma not_InA_not_In :
    forall {A: Type} l eqA (x: A),
      Equivalence eqA ->
      not (InA eqA x l) -> not (List.In x l).
  Proof.
    intros A l;
    induction l;
    intros ? ? equiv not_inA in_l;
    simpl in *;

    [ trivial
    | destruct in_l as [eq | in_l];
      subst;
      apply not_inA;
      pose proof equiv as (?,?,?);
      eauto using InA_cons_hd, InA_cons_tl, (In_InA equiv)
    ].
  Qed.

  Lemma NoDupA_stronger_than_NoDup :
    forall {A: Type} (seq: list A) eqA,
      Equivalence eqA ->
      NoDupA eqA seq -> NoDup seq.
  Proof.
    intros ? ? ? ? nodupA;
    induction nodupA;
    constructor ;
    [ apply (not_InA_not_In _ _ _ _ H0)
    | trivial].
  (* Alternative proof: red; intros; apply (In_InA (eqA:=eqA)) in H2; intuition. *)
  Qed.

  Lemma add_filter_nonnil_under_app :
    forall {A: Type} (seq: list (list A)),
      fold_right (app (A := A)) nil seq =
      fold_right (app (A := A)) nil (List.filter NonNil seq).
  Proof.
    intros; induction seq; simpl;
    [ | destruct a; simpl; rewrite IHseq];
    trivial.
  Qed.

  Lemma box_plus_app_is_identity :
    forall {A: Type} (seq: list A),
      fold_right (app (A := A)) nil (map Box seq) = seq.
  Proof.
    intros A seq; induction seq; simpl; congruence.
  Qed.

  Lemma in_Option2Box :
    forall {A: Type} (xo: option A) (x: A),
      List.In x (Option2Box xo) <-> xo = Some x.
  Proof.
    intros A xo x; destruct xo; simpl; try rewrite or_false; intuition; try congruence.
    injection H; intuition.
  Qed.

  Lemma filter_by_equiv :
    forall {A} f g,
      ObservationalEq f g ->
      forall seq, @List.filter A f seq = @List.filter A g seq.
  Proof.
    intros A f g obs seq; unfold ObservationalEq in obs; induction seq; simpl; try rewrite obs; try rewrite IHseq; trivial.
  Qed.

  Lemma filter_and :
    forall {A} pred1 pred2,
    forall (seq: list A),
      List.filter (fun x => andb (pred1 x) (pred2 x)) seq =
      List.filter pred1 (List.filter pred2 seq).
  Proof.
    intros;
    induction seq;
    simpl;
    [ | destruct (pred1 a) eqn:eq1;
        destruct (pred2 a) eqn:eq2];
    simpl;
    try rewrite eq1;
    try rewrite eq2;
    trivial;
    f_equal;
    trivial.
  Qed.

  Lemma filter_and' :
    forall {A} pred1 pred2,
    forall (seq: list A),
      List.filter (fun x => andb (pred1 x) (pred2 x)) seq =
      List.filter pred2 (List.filter pred1 seq).
  Proof.
    intros;
    induction seq;
    simpl;
    [ | destruct (pred1 a) eqn:eq1;
        destruct (pred2 a) eqn:eq2];
    simpl;
    try rewrite eq1;
    try rewrite eq2;
    trivial;
    f_equal;
    trivial.
  Qed.

  Definition flatten {A} seq := List.fold_right (@app A) nil seq.

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

  Lemma map_map :
    forall { A B C } (proc1: A -> B) (proc2: B -> C),
    forall seq,
      List.map proc2 (List.map proc1 seq) = List.map (fun x => proc2 (proc1 x)) seq.
  Proof.
    intros; induction seq; simpl; f_equal; trivial.
  Qed.

  Lemma filter_all_true :
    forall {A} pred (seq: list A),
      (forall x, List.In x seq -> pred x = true) ->
      List.filter pred seq = seq.
  Proof.
    induction seq as [ | head tail IH ]; simpl; trivial.
    intros all_true.
    rewrite all_true by eauto.
    f_equal; intuition.
  Qed.

  Lemma filter_all_false :
    forall {A} seq pred,
      (forall item : A, List.In item seq -> pred item = false) ->
      List.filter pred seq = nil.
  Proof.
    intros A seq pred all_false; induction seq as [ | head tail IH ]; simpl; trivial.
    rewrite (all_false head) by (simpl; eauto).
    intuition.
  Qed.

  Lemma map_filter_all_false :
    forall {A} pred seq,
      (forall subseq, List.In subseq seq ->
                      forall (item: A), List.In item subseq ->
                                        pred item = false) ->
      (List.map (List.filter pred) seq) = (List.map (fun x => nil) seq).
  Proof.
    intros A pred seq all_false;
    induction seq as [ | subseq subseqs IH ] ; simpl; trivial.

    f_equal.

    specialize (all_false subseq (or_introl eq_refl)).
    apply filter_all_false; assumption.

    apply IH; firstorder.
  Qed.

  Lemma foldright_compose :
    forall {TInf TOutf TAcc}
           (g : TOutf -> TAcc -> TAcc) (f : TInf -> TOutf)
           (seq : list TInf) (init : TAcc),
      List.fold_right (compose g f) init seq =
      List.fold_right g init (List.map f seq).
  Proof.
    intros;
    induction seq;
    simpl;
    [  | rewrite IHseq ];
    reflexivity.
  Qed.

  Lemma flatten_nils :
    forall {A} (seq: list (list A)),
      flatten (List.map (fun _ => nil) seq) = @nil A.
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

  Lemma in_map_unproject :
    forall {A B} projection seq,
    forall item,
      @List.In A item seq ->
      @List.In B (projection item) (List.map projection seq).
  Proof.
    intros ? ? ? seq;
    induction seq; simpl; intros item in_seq.

    trivial.
    destruct in_seq;
      [ left; f_equal | right ]; intuition.
  Qed.
End ListLemmas.
