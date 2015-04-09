Require Import Coq.Lists.List Coq.Lists.SetoidList Coq.Bool.Bool
        ADTSynthesis.Common ADTSynthesis.Common.List.Operations.

Unset Implicit Arguments.

Section ListFacts.

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
    pose proof (H a); intuition.
    discriminate.
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
    rewrite <- IHseq.
    rewrite Plus.plus_comm, <- Plus.plus_assoc; f_equal.
    rewrite Plus.plus_comm; reflexivity.
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

  Lemma fold_left_sum_acc :
    forall {A B} seq m n (f: A -> list B),
      m +
      fold_left (fun (count : nat) (x : A) => count + length (f x)) seq n =
      fold_left (fun (count : nat) (x : A) => count + length (f x)) seq
                (n + m).
  Proof.
    induction seq; simpl; intros; eauto with arith.
    rewrite IHseq; f_equal; eauto with arith.
    repeat rewrite <- Plus.plus_assoc; f_equal; auto with arith.
  Qed.

  Lemma length_flat_map :
    forall {A B} seq (f: A -> list B),
      List.length (flat_map f seq) =
      fold_left (fun count (x : A) => count + List.length (f x)) seq 0.
  Proof.
    simpl; induction seq; simpl; intros; eauto.
    rewrite app_length, IHseq; clear.
    apply fold_left_sum_acc.
  Qed.

  Lemma filter_and {A}
  : forall (pred1 pred2 : A -> bool) (l : List.list A),
      List.filter (fun a => pred1 a && pred2 a) l =
      List.filter pred2 (List.filter pred1 l).
  Proof.
    induction l; simpl; eauto.
    case_eq (pred1 a); simpl; intros H; eauto;
    case_eq (pred2 a); simpl; intros; rewrite IHl; eauto.
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

  Lemma filter_and' :
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

  Local Ltac drop_take_t' :=
    idtac;
    match goal with
      | _ => reflexivity
      | _ => intro
      | _ => progress simpl in *
      | [ |- context[drop ?n []] ] => atomic n; destruct n
      | [ |- context[take ?n []] ] => atomic n; destruct n
      | [ |- context[drop ?n (_::_)] ] => atomic n; destruct n
      | [ |- context[take ?n (_::_)] ] => atomic n; destruct n
      | [ H : _ |- _ ] => rewrite H
      | _ => solve [ eauto with arith ]
      | _ => exfalso; omega
    end.

  Local Ltac drop_take_t := repeat drop_take_t'.

  Lemma drop_map {A B n} (f : A -> B) ls
  : drop n (map f ls) = map f (drop n ls).
  Proof.
    revert n; induction ls; drop_take_t.
  Qed.

  Lemma take_map {A B n} (f : A -> B) ls
  : take n (map f ls) = map f (take n ls).
  Proof.
    revert n; induction ls; drop_take_t.
  Qed.

  Lemma take_all {A n} {ls : list A} (H : List.length ls <= n) : take n ls = ls.
  Proof.
    revert n H; induction ls; drop_take_t.
  Qed.

  Lemma drop_all {A n} {ls : list A} (H : List.length ls <= n) : drop n ls = nil.
  Proof.
    revert n H; induction ls; drop_take_t.
  Qed.

  Lemma take_append {A n} {ls ls' : list A}
  : take n (ls ++ ls') = take n ls ++ take (n - List.length ls) ls'.
  Proof.
    revert n ls'; induction ls; drop_take_t.
  Qed.

  Lemma drop_append {A n} {ls ls' : list A}
  : drop n (ls ++ ls') = drop n ls ++ drop (n - List.length ls) ls'.
  Proof.
    revert n ls'; induction ls; drop_take_t.
  Qed.

  Lemma fold_right_and_map_impl {A} {init1 init2 : Prop} (H : init1 -> init2) (ls : list A) (f g : A -> Prop) (H' : forall x, f x -> g x)
  : fold_right and init1 (map f ls) -> fold_right and init2 (map g ls).
  Proof.
    induction ls; simpl; trivial; intuition.
  Qed.

End ListFacts.
