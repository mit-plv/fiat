Require Import Coq.omega.Omega.
Require Import Coq.Lists.List Coq.Lists.SetoidList Coq.Bool.Bool
        Fiat.Common Fiat.Common.List.Operations Fiat.Common.Equality.

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

  Lemma f_fold_right_bool_rect {A B T} (f : T -> B) init (ls : list A) a b
  : f (fold_right (fun x acc => bool_rect (fun _ => T) (a x) acc (b x)) init ls)
    = fold_right (fun x acc => bool_rect (fun _ => B) (f (a x)) acc (b x)) (f init) ls.
  Proof.
    revert init; induction ls; simpl; trivial; intros.
    edestruct b; simpl; trivial.
  Qed.

  Lemma fold_right_fun {A B C} (f : A -> C -> (B -> C)) (init : B -> C) (x : B) (ls : list A)
  : fold_right (fun (a : A) (b : B -> C) x => f a (b x) x) init ls x
    = fold_right (B := A) (A := C) (fun a b => f a b x) (init x) ls.
  Proof.
    induction ls; simpl; trivial.
    rewrite IHls; reflexivity.
  Qed.

  Lemma nth_tl {A} n (ls : list A) a
  : nth n (tl ls) a = nth (S n) ls a.
  Proof.
    destruct ls, n; simpl; reflexivity.
  Qed.

  Lemma nth_drop {A} x y (ls : list A) a
  : nth x (drop y ls) a = nth (x + y) ls a.
  Proof.
    revert x y; induction ls; simpl; intros.
    { destruct x, y; reflexivity. }
    { destruct y; simpl.
      { destruct x; simpl; repeat (f_equal; []); try reflexivity; omega. }
      { rewrite IHls; destruct x; simpl; repeat (f_equal; []); try reflexivity; omega. } }
  Qed.

  Local Notation iffT A B := ((A -> B) * (B -> A))%type.

  Lemma Exists_exists_dec {A} Q (ls : list A) (dec : forall y, In y ls -> {Q y} + {~Q y})
  : iffT (Exists Q ls) { x : A & In x ls /\ Q x }.
  Proof.
    induction ls;
    repeat match goal with
             | [ |- (_ * _)%type ] => split
             | _ => progress simpl in *
             | _ => intro
             | _ => congruence
             | _ => discriminate
             | _ => tauto
             | _ => progress specialize_by assumption
             | [ H : Exists _ nil |- _ ] => exfalso; solve [ inversion H ]
             | _ => progress destruct_head sigT
             | _ => progress destruct_head prod
             | _ => progress destruct_head and
             | [ H : forall x, _ \/ _ -> _ |- _ ]
               => pose proof (fun x k => H x (or_introl k));
                 pose proof (fun x k => H x (or_intror k));
                 clear H
             | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
             | [ H : forall x, _ = x -> _ |- _ ] => specialize (H _ eq_refl)
             | [ H : Exists ?Q (?x :: ?xs), H' : ~?Q ?x |- _ ]
               => assert (Exists Q xs) by (inversion_clear H; trivial; exfalso; auto);
                 clear H
             | _ => progress destruct_head sumbool
             | _ => progress destruct_head or
             | _ => solve [ eauto ]
           end.
  Qed.

  Lemma fold_right_fun_bool_rect {A B C} (f : A -> (B -> C)) (g : A -> bool) (init : B -> C) (x : B) (ls : list A)
  : fold_right (fun (a : A) (b : B -> C) => bool_rect (fun _ => B -> C) (f a) b (g a)) init ls x
    = fold_right (B := A) (A := C) (fun a b => bool_rect (fun _ => C) (f a x) b (g a)) (init x) ls.
  Proof.
    induction ls; simpl; trivial.
    edestruct g; simpl; trivial.
  Qed.

  Lemma nth_error_length_plus_app n {T} (ls1 ls2 : list T)
  : List.nth_error (ls1 ++ ls2) (n + Datatypes.length ls1) = List.nth_error ls2 n.
  Proof.
    rewrite Plus.plus_comm.
    induction ls1; trivial.
  Qed.

  Lemma nth_error_length_app {T} (ls1 ls2 : list T)
  : List.nth_error (ls1 ++ ls2) (Datatypes.length ls1) = List.nth_error ls2 0.
  Proof.
    exact (nth_error_length_plus_app 0 _ _).
  Qed.

  Lemma lt_nth_iff :
    forall A n As,
      (exists a : A, nth_error As n = Some a)
      <-> n < List.length As.
  Proof.
    induction n; destruct As; simpl; intros;
    try auto with arith; split; intro; destruct_head ex; try (discriminate || omega);
    try (eexists; reflexivity);
    split_iff.
    { apply lt_n_S; eauto. }
    { eauto with arith. }
  Qed.

  Lemma lt_nth_T :
    forall A n As (a : A),
      nth_error As n = Some a
      -> n < List.length As.
  Proof.
    intros;
    apply lt_nth_iff.
    eexists; eassumption.
  Qed.

  Lemma in_prefix_app {T} {xs y ys ys'} (H : (xs ++ (y::ys) = ys')%list)
  : @List.In T y ys'.
  Proof.
    subst.
    induction xs; simpl; auto.
  Qed.

  Lemma nth_error_enumerate {T} {ls : list T} {k n}
  : nth_error (enumerate ls k) n = option_map (fun v => (k + n, v)) (nth_error ls n).
  Proof.
    revert k n; induction ls; intros k n; simpl.
    { destruct n; simpl; reflexivity. }
    { destruct n; simpl.
      { rewrite Plus.plus_0_r; reflexivity. }
      { rewrite IHls, <- plus_n_Sm; simpl.
        reflexivity. } }
  Qed.

  Lemma not_in_S_enumerate {T} {ls : list T} {k k' v} (H : k < k')
  : ~In (k, v) (enumerate ls k').
  Proof.
    revert k k' H; induction ls; simpl; intuition;
    repeat match goal with
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             | _ => progress subst
             | _ => congruence
             | _ => discriminate
             | _ => omega
             | [ H : S ?k = ?k |- _ ] => apply NPeano.Nat.neq_succ_diag_l in H
           end.
    eapply IHls; [ .. | eassumption ]; omega.
  Qed.

  Lemma nth_error_in_enumerate {T} {ls : list T} {k n v}
  : In (k + n, v) (enumerate ls k) <-> nth_error ls n = Some v.
  Proof.
    revert k n; induction ls; simpl.
    { intros; destruct n; split; intros; simpl in *; intuition discriminate. }
    { intros k [|n]; simpl.
      { rewrite Plus.plus_0_r.
        split.
        { intros [H|H]; [ | apply not_in_S_enumerate in H; [ | omega ] ].
          { inversion H; subst; reflexivity. }
          { destruct H. } }
        { intro H; inversion H; subst; left; reflexivity. } }
      { specialize (IHls (S k) n).
        rewrite NPeano.Nat.add_succ_r; simpl in *.
        rewrite IHls.
        split.
        { intros [H|H]; [ | assumption ].
          inversion H; omega. }
        { intro; right; assumption. } } }
  Qed.

  Lemma some_disjoint {T} {ls : list (list T)} {a a0 n its}
        (beq : T -> T -> bool)
        (lb : forall x y, x = y -> beq x y) (bl : forall x y, beq x y -> x = y)
        (Hdisjoint : fold_right andb true (map (disjoint beq a0) ls))
        (Hin : list_bin beq a a0)
        (Hindex : nth_error ls n = Some its)
        (Hin' : list_bin beq a its)
  : False.
  Proof.
    generalize dependent ls.
    induction n; simpl; intros.
    { destruct ls; simpl in *; try discriminate.
      inversion Hindex; clear Hindex; subst.
      apply Bool.andb_true_iff in Hdisjoint.
      destruct Hdisjoint as [H0 H1].
      apply (list_in_bl bl) in Hin.
      apply (list_in_bl bl) in Hin'.
      eapply (disjoint_bl lb) in H0; eassumption. }
    { destruct ls as [|? ls]; try discriminate.
      simpl in *.
      apply Bool.andb_true_iff in Hdisjoint.
      destruct Hdisjoint as [H0 H1].
      specialize (IHn ls).
      auto. }
  Qed.

  Lemma fold_right_orb_false_map_false {T f} {ls : list T}
  : fold_right orb false (map f ls) = false <-> Forall (fun k => negb (f k)) ls.
  Proof.
    induction ls; simpl; split; try setoid_rewrite Bool.orb_false_iff; intuition.
    { econstructor; try apply Bool.negb_true_iff; intuition. }
    { inversion_one_head @Forall.
      apply Bool.negb_true_iff; assumption. }
    { inversion_one_head @Forall.
      auto. }
  Qed.

  Lemma nth_error_in {T} {ls : list T} {n v}
  : nth_error ls n = Some v -> List.In v ls.
  Proof.
    revert n; induction ls; intro n; destruct n; simpl; intros H; try discriminate;
    inversion H; subst; eauto.
  Qed.

  Lemma all_disjoint_eq_in {T} (beq : T -> T -> bool)
        (bl : forall x y, beq x y = true -> x = y)
        (lb : forall x y, x = y -> beq x y = true)
        {x x' xs a n}
        (Hdisjoint : fold_right andb true (map (disjoint beq x) xs))
        (Hin1 : list_bin beq a x)
        (Hin2 : list_bin beq a x')
        (Hnth : nth_error (x::xs) n = Some x')
  : n = 0.
  Proof.
    destruct n; simpl in *; trivial; [].
    exfalso.
    generalize dependent n.
    induction xs; simpl in *; [ destruct n; simpl; intros; discriminate | ].
    apply Bool.andb_true_iff in Hdisjoint.
    destruct Hdisjoint as [H0 H1].
    specialize_by assumption.
    intros [|n] H; simpl in *; [ inversion H; subst | ].
    { apply (list_in_bl bl) in Hin1.
      apply (list_in_bl bl) in Hin2.
      eapply disjoint_bl; try eassumption. }
    { eauto. }
  Qed.
End ListFacts.
