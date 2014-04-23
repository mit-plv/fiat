Generalizable All Variables.
Set Implicit Arguments.

Require Import List String.
Require Import Common.

Section ilist.

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The type of indexed elements. *)

  Inductive ilist : list A -> Type :=
  | icons : forall a As, B a -> ilist As -> ilist (a :: As)
  | inil : ilist nil.

  Lemma ilist_invert (As : list A) (il : ilist As) :
    match As as As' return ilist As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons b il'
      | nil => fun il => il = inil
    end il.
  Proof.
    destruct il; eauto.
  Qed.

  Definition ilist_hd (As : list A) (il : ilist As) :
    match As as As' return ilist As' -> Type with
      | a :: As' => fun il => B a
      | nil => fun _ => unit
    end il :=
    match il with
      | icons a As b As' => b
      | inil => tt
    end.

  Definition ilist_tail (As : list A) (il : ilist As) :
    match As as As' return ilist As' -> Type with
      | a :: As' => fun il => ilist As'
      | nil => fun _ => unit
    end il :=
    match il with
      | icons a As b As' => As'
      | inil => tt
    end.

  Fixpoint siglist2ilist (sigList : list (sigT B))
  : ilist (map (@projT1 _ B) sigList) :=
    match sigList as sigList'
          return ilist (map (@projT1 _ B) sigList') with
      | nil => inil
      | cons (existT a b) sigList' => icons b (siglist2ilist sigList')
    end.

    Variable C : Type. (* The type of comparators. *)

    Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Fixpoint findIndex (As : list A) (c : C)
  : nat :=
    match As with
      | a :: As' => if AC_eq a c then 0 else S (findIndex As' c)
      | _ => 0
    end.

  Lemma findIndex_In
  : forall (As : list A) (c : C) (a : A),
      In a As -> AC_eq a c = true ->
      findIndex As c < List.length As.
  Proof.
    induction As; intros; simpl in *; intuition; subst.
    - rewrite H0; auto with arith.
    - find_if_inside; auto with arith.
      generalize (@IHAs c _ H1 H0); auto with arith.
  Qed.

  Local Hint Resolve findIndex_In.

  Lemma findIndex_NIn
  : forall (As : list A) (c : C),
      (forall a, In a As -> AC_eq a c = false) ->
      findIndex As c = List.length As.
  Proof.
    clear B; induction As; intros; simpl in *; intuition; subst.
    rewrite H; auto.
  Qed.

  Local Hint Resolve findIndex_NIn.

  Lemma findIndex_In_dec
  : forall (c : C) (As : list A),
      (forall a, In a As -> AC_eq a c = false)
      \/ (exists a, In a As /\ AC_eq a c = true).
  Proof.
    clear B; induction As; intros; simpl in *; intuition.
    caseEq (AC_eq a c); eauto.
    left; intros; intuition; subst; eauto.
    destruct_ex; intuition.
    eauto.
  Qed.

  Lemma nth_findIndex_In
  : forall (As : list A) (c : C) (a : A),
      In a As -> AC_eq a c = true ->
      forall a a',
        nth (findIndex As c) As a = nth (findIndex As c) As a'.
  Proof.
    clear B; intros; apply nth_indep; eauto.
  Qed.

  Lemma AC_eq_nth_In
  : forall (As : list A) (c : C) (a default_A : A),
      In a As -> AC_eq a c = true ->
      AC_eq (nth (findIndex As c) As default_A) c = true.
  Proof.
    clear B; induction As; simpl; intros; intuition;
    caseEq (AC_eq a c); eauto; subst; congruence.
  Qed.

  Lemma AC_eq_nth_NIn
  : forall (As : list A) (c c' : C) (a default_A : A),
      c <> c' ->
      In a As -> AC_eq a c = true ->
      (forall a, AC_eq a c = true -> AC_eq a c' = false) ->
      AC_eq (nth (findIndex As c) As default_A) c' = false.
  Proof.
    clear B; induction As; simpl; intros; intuition;
    caseEq (AC_eq a c); eauto; subst; try congruence.
  Qed.

  Lemma nth_findIndex_NIn
  : forall (As : list A) (c : C),
      (forall a, In a As -> AC_eq a c = false) ->
      forall a, nth (findIndex As c) As a = a.
  Proof.
    clear B; intros; apply nth_overflow; rewrite findIndex_NIn;
    auto with arith.
  Qed.

  Lemma In_As
        (As : list A)
        (default_A : A)
  : forall (a : A) (c : C),
      List.In a As -> AC_eq a c = true ->
      List.In (nth (findIndex As c) As default_A) As.
  Proof.
    clear B; induction As; simpl; intros; destruct H; subst.
    - rewrite H0; auto.
    - caseEq (AC_eq a c); eauto.
  Qed.

  Lemma In_AC_eq
        (AC_eq_c_c' :
           forall a c c',
             AC_eq a c = true
             -> AC_eq a c' = true
             -> c = c')
        (As : list A)
        (default_A : A)
  : forall (a : A) (c c' : C),
      List.In a As
      -> AC_eq a c' = true
      -> AC_eq (nth (findIndex As c') As default_A) c = true
      -> c = c'.
  Proof.
    induction As; simpl; intros; destruct H; subst.
    - caseEq (AC_eq a0 c'); rewrite H in H1; eauto.
      congruence.
    - caseEq (AC_eq a c'); rewrite H2 in H1; eauto.
  Qed.

  (* Looking up the ith value, returning None for
     indices not in the list*)

  Definition Dep_Option 
             (opt_A : option A) :=
    match opt_A with 
        | Some a => B a
        | None => True
    end.

  Fixpoint ith_error
          (n : nat)
          (As : list A)
          (il : ilist As)
          {struct n}
  : Dep_Option (nth_error As n) :=
    match n as n' return
          ilist As
          -> Dep_Option (nth_error As n')
    with
      | 0 => match As as As' return
                   ilist As'
                   -> Dep_Option (nth_error As' 0) with
               | nil => fun il => I
               | cons a As' => fun il => ilist_hd il
             end
      | S n => match As as As' return
                     ilist As'
                     -> Dep_Option (nth_error As' (S n)) with
                 | nil => fun il => I
                 | cons a As' =>
                   fun il =>
                     ith_error n (ilist_tail il)
             end
    end il.

  (* Looking up the ith value, returning a default value
     for indices not in the list. *)
  Program Fixpoint ith_default 
          (As : list A) 
          (il : ilist As) 
          (c : C) 
          (default_A : A)
          (default_B : B default_A)
  {struct As} : B (nth (findIndex As c) As default_A) :=
    match As as As' return ilist As' -> B (nth (findIndex As' c) As' default_A) with
        | a :: As' => (fun H il => _) (@ith_default As')
        | _ => fun il => _
    end il.
  Next Obligation.
    destruct (AC_eq a c).
    exact (ilist_hd il0).
    exact (H (ilist_tail il0) _ _ default_B).
  Defined.

  (*Program Fixpoint ith_default 
          (As : list A) 
          (n : nat)
          (il : ilist As) 
          (default_A : A)
          (default_B : B default_A)
  {struct As} : B (nth n As default_A) :=
    match n as n', As as As' return 
          ilist As' -> B (nth n' As' default_A) with
        | 0, a :: _ => @ilist_hd _
        | S n', a :: As' => fun il => 
                              (@ith_default As' n' (ilist_tail il) 
                                            default_A default_B)
        | _, _ => fun il => default_B
    end il. *)

  Lemma In_ith_default :
    forall (a : A)
           (As : list A)
           (il : ilist As)
           (c : C)
           (default_A : A)
           (default_B : B default_A),
      In a As -> AC_eq a c = true ->
      forall default_B',
        ith_default il c default_B' = ith_default il c default_B.
  Proof.
    induction As; simpl; intros; intuition; subst;
    unfold ith_default_obligation_2; simpl.
    - rewrite H0; auto.
    - find_if_inside; eauto.
  Qed.

  Variable P : forall a, B a -> Prop.

  Lemma ith_default_default :
    forall (As : list A)
           (il : ilist As)
           (c : C)
           (default_A : A)
           (default_B default_B' : B default_A),
      (P default_B' -> P default_B)
      -> P (ith_default il c default_B')
      -> P (ith_default il c default_B).
  Proof.
    induction As; intros; generalize (ilist_invert il); intros;
    destruct_ex; subst; simpl in *.
    - unfold ith_default_obligation_1 in *; eauto.
    - unfold ith_default_obligation_2 in *; destruct (AC_eq a c); eauto.
  Qed.

End ilist.

Section ilist_imap.

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the list. *)

  Fixpoint imap (As : list A)
           (il : ilist B As)
  : ilist B' As :=
    match il in ilist _ As return ilist _ As with
      | icons a As b il' => icons a (f b) (imap il')
      | inil => inil B'
    end.

  Variable C : Type. (* The type of comparators. *)
  Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Lemma ith_default_imap :
    forall (As : list A)
           (il : ilist _ As)
           (c : C)
           (default_A : A)
           (default_B : B default_A),
      f (ith_default AC_eq il c default_A default_B) =
      ith_default AC_eq (imap il) c default_A (f (default_B)).
  Proof.
    induction As; intros; generalize (ilist_invert il);
    intros; destruct_ex; subst; simpl.
    unfold ith_default_obligation_1; auto.
    unfold ith_default_obligation_2; auto.
    find_if_inside; simpl; eauto.
  Qed.

End ilist_imap.

Section ilist_izip.

  Variable A : Type. (* The indexing type. *)
  Variable B B' D : A -> Type. (* The three types of indexed elements. *)
  Variable f : forall a, B a -> B' a -> D a.
  (* The function which combines the two sets of elements. *)

  Fixpoint izip (As : list A)
           (il : ilist B As) (il' : ilist B' As)
  : ilist D As :=
    match As as As' return ilist B As' -> ilist B' As' -> ilist D As' with
      | a :: As' =>
        fun il il' =>
          icons a (f (ilist_hd il) (ilist_hd il'))
                (izip (ilist_tail il) (ilist_tail il'))
      | [] => fun il il' => inil D
    end il il'.

  Variable C : Type. (* The type of comparators. *)
  Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Lemma ith_default_izip :
    forall (As : list A)
           (il : ilist B As)
           (il' : ilist B' As)
           (c : C)
           (default_A : A)
           (default_B : B default_A)
           (default_B' : B' default_A),
      ith_default AC_eq (izip il il') c default_A (f default_B default_B') =
      f (ith_default AC_eq il c default_A default_B)
        (ith_default AC_eq il' c default_A default_B').
  Proof.
    induction As; intros; generalize (ilist_invert il);
    intros; destruct_ex; subst; simpl.
    unfold ith_default_obligation_1; auto.
    unfold ith_default_obligation_2; auto.
    find_if_inside; simpl; eauto.
  Qed.

End ilist_izip.

Section ilist_replace.

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)

  Variable C : Type. (* The type of comparators. *)
  Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Fixpoint replace_index
          (As : list A)
          (il : ilist B As)
          (c : C)
          (default_A : A)
          (new_b : B (nth (findIndex AC_eq As c) As default_A))
  {struct As} : ilist B As.
  Proof.
    refine (match As as As' return
                  ilist B As'
                  -> B (nth (findIndex AC_eq As' c) As' default_A)
                  -> ilist B As' with
              | a :: As' => (fun il' new_b' => _)
              | _ => fun il' new_b' => inil _
            end il new_b).
    simpl in *.
    destruct (AC_eq a c).
    exact (icons _ new_b' (ilist_tail il')).
    exact (icons _ (ilist_hd il') (replace_index _ (ilist_tail il') c default_A new_b')).
  Defined.

  Lemma replace_index_NIn
  : forall (As : list A)
           (il : ilist _ As)
           (c : C)
           (default_A : A)
           (new_b : B (nth (findIndex AC_eq As c) As default_A)),
      (forall a, In a As -> AC_eq a c = false) ->
      replace_index il c default_A new_b = il.
  Proof.
    induction As; intros; subst.
    - unfold ith_default_obligation_1; simpl; auto.
      rewrite (ilist_invert il); auto.
    - simpl in *.
      revert new_b.
      caseEq (AC_eq a c); unfold ith_default_obligation_2; simpl.
      rewrite H in H0; auto; try congruence.
      rewrite IHAs; eauto.
      destruct (ilist_invert il) as [a' [b' il']]; subst; simpl; auto.
  Qed.

  Lemma ith_default_replace :
    forall (As : list A)
           (il : ilist _ As)
           (c : C)
           (default_A : A)

           (new_b : B (nth (findIndex AC_eq As c) As default_A))
           (default_B : B default_A)
           (c' : C),
      AC_eq (nth (findIndex AC_eq As c) As default_A) c' = false ->
      ith_default AC_eq (replace_index il c default_A new_b) c' default_A default_B =
      ith_default AC_eq il c' default_A default_B.
  Proof.
    induction As; intros; subst.
    - unfold ith_default_obligation_1; simpl; auto.
    - simpl in *.
      revert new_b.
      caseEq (AC_eq a c); unfold ith_default_obligation_2; simpl;
      rewrite H0 in H.
      + rewrite H; eauto.
      + caseEq (AC_eq a c'); eauto.
  Qed.

  Lemma ith_default_replace' :
    forall (As : list A)
           (il : ilist _ As)
           (c : C)
           (default_A : A)
           (new_b : B (nth (findIndex AC_eq As c) As default_A))
           (default_B : B default_A),
      forall a, In a As -> AC_eq a c = true ->
      AC_eq (nth (findIndex AC_eq As c) As default_A) c = true ->
      ith_default AC_eq (replace_index il c default_A new_b) c default_A default_B =
      new_b.
  Proof.
    induction As; intros; destruct H; subst;
    simpl in *; unfold ith_default_obligation_2; simpl; auto.
    - revert new_b H1; rewrite H0; intros; simpl; auto.
    - revert new_b H1; caseEq (AC_eq a c); simpl; eauto.
  Qed.

End ilist_replace.
