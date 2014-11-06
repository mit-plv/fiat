Require Import Coq.Sets.Ensembles Coq.Lists.List Coq.Lists.SetoidList Coq.Program.Program
        ADTSynthesis.Common ADTSynthesis.Computation.Core
        ADTSynthesis.QueryStructure.SetEq Coq.omega.Omega Coq.Strings.String Coq.Arith.Arith.

Unset Implicit Arguments.

Ltac generalize_all :=
  repeat match goal with
             [ H : _ |- _ ] => generalize H; clear H
         end.

Section AdditionalDefinitions.
  Open Scope list_scope.

End AdditionalDefinitions.

Section AdditionalNatLemmas.
  Lemma le_r_le_max :
    forall x y z,
      x <= z -> x <= max y z.
  Proof.
    intros x y z;
    destruct (Max.max_spec y z) as [ (comp, eq) | (comp, eq) ];
    rewrite eq;
    omega.
  Qed.

  Lemma le_l_le_max :
    forall x y z,
      x <= y -> x <= max y z.
  Proof.
    intros x y z.
    rewrite Max.max_comm.
    apply le_r_le_max.
  Qed.

  Lemma le_neq_impl :
    forall m n, m < n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma gt_neq_impl :
    forall m n, m > n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma lt_refl_False :
    forall x,
      lt x x -> False.
  Proof.
    intros; omega.
  Qed.

  Lemma beq_nat_eq_nat_dec :
    forall x y,
      beq_nat x y = if eq_nat_dec x y then true else false.
  Proof.
    intros; destruct (eq_nat_dec _ _); [ apply beq_nat_true_iff | apply beq_nat_false_iff ]; assumption.
  Qed.
End AdditionalNatLemmas.

Section AdditionalLogicLemmas.
  Lemma or_false :
    forall (P: Prop), P \/ False <-> P.
  Proof.
    tauto.
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

  Lemma and_True :
    forall P,
      (P /\ True) <-> P.
  Proof.
    tauto.
  Qed.

  Lemma not_exists_forall :
    forall {A} (P: A -> Prop),
      (~ (exists a, P a)) <-> (forall a, ~ P a).
  Proof.
    firstorder.
  Qed.

  Lemma not_and_implication :
    forall (P Q: Prop),
      ( ~ (P /\ Q) ) <-> (P -> ~ Q).
  Proof.
    firstorder.
  Qed.

  Lemma eq_sym_iff :
    forall {A} x y, @eq A x y <-> @eq A y x.
  Proof.
    split; intros; symmetry; assumption.
  Qed.
End AdditionalLogicLemmas.

Section AdditionalBoolLemmas.
  Lemma collapse_ifs_dec :
    forall P (b: {P} + {~P}),
      (if (if b then true else false) then true else false) =
      (if b then true else false).
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma collapse_ifs_bool :
    forall (b: bool),
      (if (if b then true else false) then true else false) =
      (if b then true else false).
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma string_dec_bool_true_iff :
    forall s1 s2,
      (if string_dec s1 s2 then true else false) = true <-> s1 = s2.
  Proof.
    intros s1 s2; destruct (string_dec s1 s2); simpl; intuition.
  Qed.

  Lemma eq_nat_dec_bool_true_iff :
    forall n1 n2,
      (if eq_nat_dec n1 n2 then true else false) = true <-> n1 = n2.
  Proof.
    intros n1 n2; destruct (eq_nat_dec n1 n2); simpl; intuition.
  Qed.

  Lemma eq_N_dec_bool_true_iff :
    forall n1 n2 : N, (if N.eq_dec n1 n2 then true else false) = true <-> n1 = n2.
  Proof.
    intros; destruct (N.eq_dec _ _); intuition.
  Qed.

  Lemma eq_Z_dec_bool_true_iff :
    forall n1 n2 : Z, (if Z.eq_dec n1 n2 then true else false) = true <-> n1 = n2.
  Proof.
    intros; destruct (Z.eq_dec _ _); intuition.
  Qed.

  Lemma bool_equiv_true:
    forall (f g: bool),
      (f = true <-> g = true) <-> (f = g).
  Proof.
    intros f g; destruct f, g; intuition.
  Qed.

  Lemma if_negb :
    forall {A} (b: bool) (x y: A), (if negb b then x else y) = (if b then y else x).
  Proof.
    intros; destruct b; simpl; reflexivity.
  Qed.
End AdditionalBoolLemmas.

Section AdditionalEnsembleLemmas.
  Lemma weaken :
    forall {A: Type} ensemble condition,
    forall (x: A),
      Ensembles.In _ (fun x => Ensembles.In _ ensemble x /\ condition x) x
      -> Ensembles.In _ ensemble x.
  Proof.
    unfold Ensembles.In; intros; intuition.
  Qed.
End AdditionalEnsembleLemmas.

Section AdditionalListLemmas.
  Lemma map_id :
    forall {A: Type} (seq: list A),
      (map (fun x => x) seq) = seq.
  Proof.
    intros A seq; induction seq; simpl; congruence.
  Qed.

  Lemma app_singleton :
    forall {A} (x: A) s,
      [x] ++ s = x :: s.
  Proof.
    reflexivity.
  Qed.

  Lemma app_eq_nil_iff :
    forall {A} s1 s2,
      @nil A = s1 ++ s2 <-> ([] = s1 /\ [] = s2).
  Proof.
    intros; split; intro H.
    - symmetry in H; apply app_eq_nil in H; intuition.
    - intuition; subst; intuition.
  Qed.

  Lemma singleton_neq_nil :
    forall {A} (a: A),
      [a] = [] <-> False.
  Proof.
    intuition discriminate.
  Qed.

  Lemma in_nil_iff :
    forall {A} (item: A),
      List.In item [] <-> False.
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
      (seq = []).
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

  Lemma NoDupFilter {A}
  : forall (f : A -> bool) (l : list A),
      NoDup l -> NoDup (filter f l).
  Proof.
    induction l; simpl; intros; eauto.
    inversion H; subst; find_if_inside; try constructor; eauto.
    unfold not; intros H'; apply H2; revert H'; clear; induction l;
    simpl; eauto; find_if_inside; simpl; intuition.
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

  Definition ExtensionalEq {A B} f g :=
    forall (a: A), @eq B (f a) (g a).

  Lemma filter_by_equiv :
    forall {A} f g,
      ExtensionalEq f g ->
      forall seq, @List.filter A f seq = @List.filter A g seq.
  Proof.
    intros A f g obs seq; unfold ExtensionalEq in obs; induction seq; simpl; try rewrite obs; try rewrite IHseq; trivial.
  Qed.

  Lemma filter_by_equiv_meta :
    forall {A B : Type} (f g : A -> B -> bool),
      (forall (a: A), ExtensionalEq (f a) (g a)) ->
      (forall (a: A) (seq : list B), filter (f a) seq = filter (g a) seq).
  Proof.
    intros * equiv *;
    rewrite (filter_by_equiv _ _ (equiv _));
    reflexivity.
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

  Lemma map_map :
    forall { A B C } (f: A -> B) (g: B -> C),
    forall seq,
      List.map g (List.map f seq) = List.map (fun x => g (f x)) seq.
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
      List.filter pred seq = [].
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
      (List.map (List.filter pred) seq) = (List.map (fun x => []) seq).
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

  Require Import Coq.Sorting.Permutation.

  Lemma flat_map_rev_permutation :
    forall {A B} seq (f: A -> list B),
      Permutation (flat_map f seq) (flat_map f (rev seq)).
  Proof.
    induction seq; simpl; intros.

    - reflexivity.
    - rewrite !flat_map_flatten, map_app.
      rewrite flatten_app, <- !flat_map_flatten.
      simpl; rewrite app_nil_r.
      rewrite Permutation_app_comm.
      apply Permutation_app; eauto.
  Qed.

  Lemma length_flatten_aux :
    forall {A} seq,
    forall n,
      n + List.length (flatten seq) = List.fold_right (compose plus (@List.length A)) n seq.
  Proof.
    induction seq; simpl; intros.

    - auto with arith.
    - unfold compose;
      rewrite app_length, <- IHseq;
      omega.
  Qed.

  Lemma length_flatten :
    forall {A} seq,
      List.length (flatten seq) = List.fold_right (compose plus (@List.length A)) 0 seq.
  Proof.
    intros.
    pose proof (length_flatten_aux seq 0) as H; simpl in H; eauto.
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

  Lemma refold_map :
    forall {A B} (f: A -> B) x seq,
      f x :: map f seq = map f (x :: seq).
  Proof.
    simpl; reflexivity.
  Qed.

  Lemma refold_in :
    forall {A} a b l,
      @List.In A a (b :: l) <-> List.In a l \/ a = b.
  Proof.
    intros; simpl; intuition.
  Qed.

  Lemma app_map_inv :
    forall {A B} seq l1 l2 (f: A -> B),
      l1 ++ l2 = map f seq ->
      exists l1' l2',
        seq = l1' ++ l2' /\ l1 = map f l1' /\ l2 = map f l2'.
  Proof.
    induction seq; simpl; intros.

    exists (@nil A) (@nil A); simpl.
    apply app_eq_nil in H; intuition.

    destruct l1.
    rewrite app_nil_l in H.
    exists (@nil A) (a :: seq); simpl; intuition.

    rewrite <- app_comm_cons in H.
    inversion H.
    specialize (IHseq _ _ _ H2).
    destruct IHseq as [l1' [l2' (seq_eq_app & l1l1' & l2l2') ] ].
    exists (a :: l1') (l2'); subst; intuition.
  Qed.

  Lemma cons_map_inv :
    forall {A B} seq x1 l2 (f: A -> B),
      x1 :: l2 = map f seq ->
      exists x1' l2',
        seq = x1' :: l2' /\ x1 = f x1' /\ l2 = map f l2'.
  Proof.
    intros * _eq.
    destruct seq as [ | x1' l2' ]; simpl in *; try discriminate.
    inversion _eq.
    exists x1' l2'; subst; intuition.
  Qed.

  Lemma map_eq_nil_inv :
    forall {A B} (f: A -> B) seq,
      map f seq = [] -> seq = [].
  Proof.
    intros; destruct seq; simpl in *; try discriminate; trivial.
  Qed.


  Lemma filter_app :
    forall {A} (f: A -> _) s1 s2,
      List.filter f (s1 ++ s2) =
      List.filter f s1 ++ List.filter f s2.
  Proof.
    induction s1; simpl; intros.

    - reflexivity.
    - destruct (f a); simpl; congruence.
  Qed.

  Lemma filter_map :
    forall {A B} f g seq,
      List.filter f (@List.map A B g seq) =
      List.map g (List.filter (fun x => f (g x)) seq).
  Proof.
    induction seq; simpl; intros.

    - reflexivity.
    - destruct (f (g a)); simpl; [ f_equal | ]; assumption.
  Qed.

  Lemma filter_true :
    forall {A} s,
      @filter A (fun _ => true) s = s.
  Proof.
    induction s; simpl; try rewrite IHs; reflexivity.
  Qed.

  Lemma filter_false :
    forall {A} s,
      @filter A (fun _ => false) s = [].
  Proof.
    induction s; simpl; try rewrite IHs; reflexivity.
  Qed.

  Lemma filter_flat_map :
    forall {A B} g (f: B -> bool) xs,
      filter f (flat_map g xs) =
      flat_map (fun x : A => filter f (g x)) xs.
  Proof.
    intros; rewrite !flat_map_flatten.
    rewrite flatten_filter, map_map; reflexivity.
  Qed.

  Lemma filter_flat_map_join_snd :
    forall {A B} f s1 s2,
      flat_map (filter (fun x : A * B => f (snd x)))
               (map (fun a1 : A => map (fun b : B => (a1, b)) s2) s1) =
      flat_map (fun a1 : A => map (fun b : B => (a1, b)) (filter f s2)) s1.
  Proof.
    induction s1; simpl; intros; trivial.
    rewrite IHs1; f_equiv.
    rewrite filter_map; simpl; reflexivity.
  Qed.

  Lemma flat_map_empty :
    forall {A B} s,
      @flat_map A B (fun _ => []) s = [].
  Proof.
    induction s; firstorder.
  Qed.

  Lemma filter_commute :
    forall {A} f g seq,
      @filter A f (filter g seq) = filter g (filter f seq).
  Proof.
    induction seq; simpl; intros; trivial.
    destruct (f a) eqn:eqf; destruct (g a) eqn:eqg;
    simpl; rewrite ?eqf, ?eqg, ?IHseq; trivial.
  Qed.

  Lemma fold_right_id {A} :
    forall seq,
      @List.fold_right (list A) A (fun elem acc => elem :: acc) [] seq = seq.
  Proof.
    induction seq; simpl; try rewrite IHseq; congruence.
  Qed.

  Lemma fold_left_id {A} :
    forall seq,
      @List.fold_left (list A) A (fun acc elem => elem :: acc) seq [] = rev seq.
  Proof.
    intros.
    rewrite <- fold_left_rev_right.
    apply fold_right_id.
  Qed.

  Lemma In_partition {A}
  : forall f (l : list A) a,
      List.In a l <-> (List.In a (fst (List.partition f l))
                       \/ List.In a (snd (List.partition f l))).
  Proof.
    split; induction l; simpl; intros; intuition; simpl; subst;
    first [destruct (f a0); destruct (List.partition f l); simpl in *; intuition
          | destruct (f a); destruct (List.partition f l); simpl; intuition].
  Qed.

  Lemma In_partition_matched {A}
  : forall f (l : list A) a,
      List.In a (fst (List.partition f l)) ->
      f a = true.
  Proof.
    induction l; simpl; intros; intuition; simpl; subst; eauto.
    case_eq (f a); destruct (List.partition f l); simpl; intuition;
    rewrite H0 in H; eauto; inversion H; subst; eauto.
  Qed.

  Lemma In_partition_unmatched {A}
  : forall f (l : list A) a,
      List.In a (snd (List.partition f l)) ->
      f a = false.
  Proof.
    induction l; simpl; intros; intuition; simpl; subst; eauto.
    case_eq (f a); destruct (List.partition f l); simpl; intuition;
    rewrite H0 in H; eauto; inversion H; subst; eauto.
  Qed.

  Lemma nil_in_false :
    forall {A} seq,
      seq = nil <-> ~ exists (x: A), List.In x seq.
  Proof.
    split; intro H.
    intros [ x in_seq ]; subst; eauto using in_nil.
    destruct seq as [ | a ]; trivial.
    exfalso; apply H; exists a; simpl; intuition.
  Qed.

  Lemma In_InA :
    forall (A : Type) (l : list A) (eqA : relation A) (x : A),
      Equivalence eqA -> List.In x l -> InA eqA x l.
  Proof.
    induction l; intros; simpl in *.
    exfalso; eauto using in_nil.
    destruct H0.
    apply InA_cons_hd; subst; reflexivity.
    apply InA_cons_tl, IHl; trivial.
  Qed.

  Lemma fold_map :
      forall {A B C} seq f g init,
        @List.fold_left C A (fun acc x => f acc (g x)) seq init =
        @List.fold_left C B (fun acc x => f acc (  x)) (@List.map A B g seq) init.
  Proof.
    induction seq; simpl; intros; trivial; try rewrite IHseq; intuition.
  Qed.

  Lemma fold_plus_sym :
    forall (seq: list nat) (default: nat),
      List.fold_right plus default seq =
      List.fold_left plus seq default.
  Proof.
    intros; rewrite <- fold_left_rev_right.
    revert default; induction seq; simpl; eauto; intros.
    rewrite fold_right_app; simpl; rewrite <- IHseq.
    clear IHseq; revert a default; induction seq;
    simpl; intros; auto with arith.
    rewrite <- IHseq; omega.
  Qed.

  Lemma map_snd {A B C} :
    forall (f : A -> B) (l : list (C * A)),
      List.map f (List.map snd l) =
      List.map snd (List.map (fun ca => (fst ca, f (snd ca))) l).
  Proof.
    intros; repeat rewrite List.map_map; induction l; simpl; eauto.
  Qed.

  Lemma partition_app {A} :
    forall f (l1 l2 : list A),
      List.partition f (l1 ++ l2) =
      (fst (List.partition f l1) ++ fst (List.partition f l2),
       snd (List.partition f l1) ++ snd (List.partition f l2)).
  Proof.
    induction l1; simpl.
    - intros; destruct (List.partition f l2); reflexivity.
    - intros; rewrite IHl1; destruct (f a); destruct (List.partition f l1);
      simpl; f_equal.
  Qed.


  Lemma partition_filter_eq {A} :
    forall (f : A -> bool) l,
      fst (List.partition f l) = List.filter f l.
  Proof.
    induction l; simpl; eauto.
    destruct (List.partition f l); destruct (f a); simpl in *; congruence.
  Qed.

  Lemma partition_filter_neq {A} :
    forall (f : A -> bool) l,
      snd (List.partition f l) = List.filter (fun a => negb (f a)) l.
  Proof.
    induction l; simpl; eauto.
    destruct (List.partition f l); destruct (f a); simpl in *; congruence.
  Qed.


  Lemma filter_app_inv {A}
  : forall pred (l l1 l2 : list A),
      filter pred l = app l1 l2
      -> exists l1' l2', l = app l1' l2'
                         /\ l1 = filter pred l1'
                         /\ l2 = filter pred l2'.
  Proof.
    induction l; simpl; intros.
    - destruct l1; simpl in *;
      [ destruct l2;
        [ eexists nil; eexists nil; intuition
        | discriminate]
      | discriminate ].
    - revert H; case_eq (pred a); intros.
      + destruct l1; simpl in *.
        * destruct l2; [ discriminate | ].
          injection H0; intros.
          apply (IHl [] l2) in H1; destruct_ex; intuition; subst.
          eexists []; eexists (_ :: _); intuition; simpl.
          rewrite H, H0; reflexivity.
        * injection H0; intros.
          apply IHl in H1; destruct_ex; subst.
          eexists (a0 :: x); eexists x0; intuition.
          rewrite H2; reflexivity.
          simpl; rewrite H, H1; reflexivity.
      + apply IHl in H0; destruct_ex; subst.
        eexists (a :: x); eexists x0; intuition.
        rewrite H1; reflexivity.
        simpl; rewrite H, H0; reflexivity.
  Qed.

End AdditionalListLemmas.

Section AdditionalComputeationLemmas.
  Require Import ADTSynthesis.Computation.Refinements.Tactics.

  Lemma ret_computes_to :
    forall {A: Type} (a1 a2: A),
      ret a1 ↝ a2 <-> a1 = a2.
  Proof.
    t_refine.
  Qed.
End AdditionalComputeationLemmas.
