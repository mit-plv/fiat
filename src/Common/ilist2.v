Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith.
Require Import ADTSynthesis.Common.ilist.
Require Import ADTSynthesis.Common.

Section ilist2.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The type of indexed elements. *)

  Inductive ilist2 : list A -> Type :=
  | icons2 : forall a As, B a -> ilist2 As -> ilist2 (a :: As)
  | inil2 : ilist2 nil.

  (* Get the car of an ilist2. *)

  Definition ilist2_hd (As : list A) (il : ilist2 As) :
    match As return ilist2 As -> Type with
      | a :: As' => fun il => B a
      | nil => fun _ => unit
    end il :=
    match il with
      | icons2 a As b As' => b
      | inil2 => tt
    end.

  (* Get the cdr of an ilist2. *)

  Definition ilist2_tl (As : list A) (il : ilist2 As) :
    match As return ilist2 As -> Type with
      | a :: As' => fun il => ilist2 As'
      | nil => fun _ => unit
    end il :=
    match il with
      | icons2 a As b As' => As'
      | inil2 => tt
    end.

  (* Membership in an indexed list. *)

  Inductive ilist2_In {a : A} (b : B a)
  : forall (As : list A) (il : ilist2 As), Prop :=
  | In_hd : forall As' (il : ilist2 As'),
              ilist2_In b (icons2 b il)
  | In_tl : forall a' (b' : B a') As' (il : ilist2 As'),
              ilist2_In b il ->
              ilist2_In b (icons2 b' il).

  (* ilist2s can be built from standard lists of sigma types *)

  Fixpoint siglist2ilist2 (sigList : list (sigT B))
  : ilist2 (map (@projT1 _ B) sigList) :=
    match sigList
          return ilist2 (map (@projT1 _ B) sigList) with
      | [] => inil2
      | (existT a b) :: sigList' => icons2 b (siglist2ilist2 sigList')
    end.

  (* and vice versa. *)

  Fixpoint ilist22siglist {As : list A} (il : ilist2 As) : list (sigT B) :=
    match il with
      | inil2 => []
      | icons2 a As b il' => (existT B a b) :: (ilist22siglist il')
    end.

  (* ilist22siglist is the inverse of siglist2ilist2 *)
  Lemma siglist2ilist2_id
  : forall (sigList : list (sigT B)),
      ilist22siglist (siglist2ilist2 sigList) = sigList.
  Proof.
    induction sigList; simpl; auto.
    destruct a; simpl; congruence.
  Qed.

  (* and vice-versa. *)

  Fixpoint ilist22siglist_map
          As (il : ilist2 As)
  : map (@projT1 _ B) (ilist22siglist il) = As :=
    match il as il' in ilist2 As' return
          map (@projT1 _ B) (ilist22siglist il') = As' with
      | inil2 => eq_refl
      | icons2 a As' b il' => f_equal (fun b' => cons a b') (ilist22siglist_map il')
    end.

  Lemma ilist22sislist_map_cons
  : forall a b As (il il' : ilist2 As),
      match ilist22siglist_map il in (_ = y) return (ilist2 y -> Prop) with
        | eq_refl =>
          fun il' => siglist2ilist2 (ilist22siglist il) = il'
      end il'
      ->
      match
        f_equal (fun b' : list A => a :: b') (ilist22siglist_map il) in (_ = y)
        return (ilist2 y -> Prop)
      with
        | eq_refl =>
          fun il' : ilist2 (a :: map (projT1 (P:=B)) (ilist22siglist il)) =>
            icons2 b (siglist2ilist2 (ilist22siglist il)) = il'
      end (icons2 b il').
  Proof.
    intros until il; destruct (ilist22siglist_map il); congruence.
  Qed.

  Lemma ilist22siglist_id
  : forall As (il : ilist2 As),
      match (ilist22siglist_map il) in (_ = y) return
            forall (il' : ilist2 y), Prop
      with
        | eq_refl => fun il' => siglist2ilist2 (ilist22siglist il) = il'
      end il.
  Proof.
    induction il; simpl; auto.
    apply ilist22sislist_map_cons; auto.
  Qed.

  (* Looking up the ith value, returning None for indices not in the list *)

  Fixpoint ith2_error
          (As : list A)
          (il : ilist2 As)
          (n : nat)
          {struct n}
  : Dep_Option B (nth_error As n) :=
    match n as n' return
          ilist2 As
          -> Dep_Option B (nth_error As n')
    with
      | 0 => match As as As' return
                   ilist2 As'
                   -> Dep_Option B (nth_error As' 0) with
               | nil => fun il => Dep_None B
               | cons a As' => fun il => Dep_Some B a (ilist2_hd il)
             end
      | S n => match As as As' return
                     ilist2 As'
                     -> Dep_Option B (nth_error As' (S n)) with
                 | nil => fun il => Dep_None B
                 | cons a As' =>
                   fun il =>
                     ith2_error (ilist2_tl il) n
             end
    end il.

  (* Looking up the ith value, returning a default value
     for indices not in the list. *)
  Fixpoint ith2_default
          (default_A : A)
          (default_B : B default_A)
          (As : list A)
          (il : ilist2 As)
          (n : nat)
  {struct As} : B (nth n As default_A) :=
    match As as As', n as n' return ilist2 As' -> B (nth n' As' default_A) with
        | a :: As', 0    => @ilist2_hd _
        | a :: As', S n' => fun il => ith2_default default_B (ilist2_tl il) n'
        | []      , 0    => fun il => default_B
        | []      , S n' => fun il => default_B
    end il.

  Lemma ilist2_invert (As : list A) (il : ilist2 As) :
    match As as As' return ilist2 As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons2 b il'
      | nil => fun il => il = inil2
    end il.
  Proof.
    destruct il; eauto.
  Qed.

  (* The [ith_induction] tactic is for working with lookups of bounded indices.
     It first inducts on n, then destructs the index list [As] and eliminates
     the contradictory cases, then finally destructs any indexed list in the
     context with Bounds of [As]. *)

  Ltac icons2_invert :=
    repeat match goal with
             | [il : ilist2 (_ :: _) |- _]
               => let il' := fresh "il" in
                  let b' := fresh "b" in
                  let il'_eq := fresh "il_eq" in
                  generalize (ilist2_invert il);
                    intros il'; destruct il' as [b' [il' il'_eq]]; subst
           end.

  Ltac ith2_induction n As :=
    induction n; simpl; intros;
    (destruct As; simpl in *;
                  [intros; elimtype False; eapply lt_n_0; eassumption
                  | icons2_invert ]).

  Lemma ith2_default_In :
    forall (n : nat)
           (As : list A)
           (il : ilist2 As)
           (default_A : A)
           (default_B : B default_A),
      n < List.length As ->
      ilist2_In (ith2_default default_B il n) il.
  Proof.
    ith2_induction n As; simpl; constructor; eauto with arith.
  Qed.

  Lemma ith2_default_indep :
    forall (n : nat)
           (As : list A)
           (il : ilist2 As)
           (default_A : A)
           (default_B default_B' : B default_A),
      n < List.length As ->
      ith2_default default_B il n = ith2_default default_B' il n.
  Proof.
    ith2_induction n As; simpl; eauto with arith.
  Qed.

End ilist2.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways *)
Section ilist2_map.
  Context {A} (B : A -> Type).

  Fixpoint imap_list (f : forall a : A, B a) (As : list A) : ilist2 B As
    := match As with
         | nil => inil2 _
         | x::xs => @icons2 _ B x _ (f x) (imap_list f xs)
       end.

  Fixpoint map_ilist2 {C} (f : forall (a : A), B a -> C) {As} (Bs : ilist2 B As) : list C
    := match Bs with
         | inil2 => nil
         | icons2 _ _ x xs => (f _ x)::map_ilist2 f xs
       end.

End ilist2_map.

Section of_list.
  Context {T : Type}.

  Definition ilist2_of_list : forall ls : list T, ilist2 (fun _ => T) ls := imap_list (fun _ => T) (fun x => x).
  Definition list_of_ilist2 {T'} {is} (ls : ilist2 (fun _ : T' => T) is) : list T
    := map_ilist2 (B := fun _ => T) (fun _ x => x) ls.

  Lemma list_of_ilist2_of_list ls : list_of_ilist2 (ilist2_of_list ls) = ls.
  Proof.
    unfold list_of_ilist2, ilist2_of_list.
    induction ls; simpl in *; f_equal; assumption.
  Qed.
End of_list.


Ltac icons2_invert :=
  repeat match goal with
           | [il : ilist2 _ (_ :: _) |- _]
             => let il' := fresh "il" in
                let b' := fresh "b" in
                let il'_eq := fresh "il_eq" in
                generalize (ilist2_invert il);
                  intros il'; destruct il' as [b' [il' il'_eq]]; subst
         end.

Ltac ith2_induction n As :=
  induction n; simpl; intros;
  (destruct As; simpl in *;
                [intros; elimtype False; eapply lt_n_0; eassumption
                | icons2_invert ]).

Section ilist2_imap.

  (* Mapping a function over an indexed list. *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the list. *)

  Fixpoint imap2 (As : list A)
           (il : ilist2 B As)
  : ilist2 B' As :=
    match il in ilist2 _ As return ilist2 _ As with
      | icons2 a As b il' => icons2 a (f b) (imap2 il')
      | inil2 => inil2 B'
    end.

  (* [imap] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith2_default_imap :
    forall (n : nat)
           (As : list A)
           (il : ilist2 _ As)
           (default_A : A)
           (default_B : B default_A),
      f (ith2_default default_A default_B il n) =
      ith2_default default_A (f default_B) (imap2 il) n.
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons2_invert; simpl; auto.
  Qed.

  (* [imap2] behaves as expected with the [ith_error] lookup
     function as well, albeit with a more dependently-typed statement. *)

  Lemma ith2_error_imap :
    forall (n : nat)
           (As : list A)
           (il : ilist2 _ As),
      Dep_Option_Map B' f (ith2_error il n) =
      ith2_error (imap2 il) n.
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons2_invert; simpl; auto.
  Qed.

End ilist2_imap.

Section ilist2_izip.

  (* Merging two indexed lists together. *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' D : A -> Type. (* The three types of indexed elements. *)
  Variable f : forall a, B a -> B' a -> D a.

  (* The function which merges the two sets of elements. *)
  Fixpoint izip2 (As : list A)
           (il : ilist2 B As) (il' : ilist2 B' As)
  : ilist2 D As :=
    match As return ilist2 B As -> ilist2 B' As -> ilist2 D As with
      | a :: As' =>
        fun il il' =>
          icons2 a (f (ilist2_hd il) (ilist2_hd il'))
                (izip2 (ilist2_tl il) (ilist2_tl il'))
      | [] => fun il il' => inil2 D
    end il il'.

  (* [izip] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith2_default_izip2 :
    forall (n : nat)
           (As : list A)
           (il : ilist2 B As)
           (il' : ilist2 B' As)
           (default_A : A)
           (default_B : B default_A)
           (default_B' : B' default_A),
      ith2_default _ (f default_B default_B') (izip2 il il') n =
      f (ith2_default _ default_B il n) (ith2_default _ default_B' il' n).
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons2_invert; simpl; auto.
  Qed.

  (* [izip] behaves as expected with the [ith_error] lookup
     function as well, albeit with a more dependently-typed statement. *)

  Lemma ith2_error_izip :
    forall (n : nat)
           (As : list A)
           (il : ilist2 B As)
           (il' : ilist2 B' As),
      ith2_error (izip2 il il') n =
      Dep_Option_Zip D f (ith2_error il n) (ith2_error il' n).
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons2_invert; simpl; auto.
  Qed.

End ilist2_izip.

Section ilist2_replace.

  (* Replacing an element of an indexed list. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)

  Program Fixpoint replace_Index2
           {B : A -> Type}
           (n : nat)
           (As : list A)
           (il : ilist2 B As)
           (new_b : Dep_Option_elimT B (nth_error As n))
           {struct As} : ilist2 B As :=
    match n return
            ilist2 B As
            -> Dep_Option_elimT B (nth_error As n)
            -> ilist2 B As with
      | 0 => match As return
                   ilist2 B As
                   -> Dep_Option_elimT B (nth_error As 0)
                   -> ilist2 B As with
               | nil =>
                 fun il _ => inil2 _
               | cons a Bound' =>
                 fun il new_b =>
                   icons2 _ new_b (ilist2_tl il)
             end
      | S n => match As return
                     ilist2 B As
                     -> Dep_Option_elimT B (nth_error As (S n))
                     -> ilist2 B As with
                 | nil => fun il _ => inil2 _
                 | cons a Bound' =>
                   fun il new_b =>
                     icons2 _ (ilist2_hd il)
                           (@replace_Index2 B n Bound'
                                           (ilist2_tl il) new_b)
               end
    end il new_b.

  Lemma replace_Index2_overflow
  : forall
      (n : nat)
      (As : list A)
      (il : ilist2 _ As)
      (new_b : Dep_Option_elimT B (nth_error As n)),
      List.length As <= n
      -> replace_Index2 n il new_b = il.
  Proof.
    induction n; simpl;
    (destruct As; intros;
     [generalize (ilist2_invert il); intros; subst; reflexivity |
      icons2_invert; simpl in *]).
    - destruct (le_Sn_0 _ H).
    - f_equal; auto with arith.
  Qed.

  Lemma ith2_replace_Index2_neq
  : forall
      (n : nat)
      (As : list A)
      (il : ilist2 _ As)
      (n' : nat)
      (new_b : Dep_Option_elimT B (nth_error As n')),
      n <> n'
      -> Dep_Option_elim_P2
           (fun a b b' => b = b')
           (ith2_error (replace_Index2 n' il new_b) n)
           (ith2_error il n).
  Proof.
    unfold Dep_Option_elim_P2.
    induction n; simpl; destruct As; intros; icons2_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    eapply Dep_Option_P2_refl.
    eapply IHn; congruence.
  Qed.

  Lemma ith2_replace_Index2_eq
  : forall
      (n : nat)
      (As : list A)
      (il : ilist2 _ As)
      (new_b : Dep_Option B (nth_error As n)),
      Dep_Option_elim_P2
        (fun a b b' => b = b')
        (ith2_error (replace_Index2 n il (Dep_Option_elim new_b)) n)
        new_b.
  Proof.
    unfold Dep_Option_elim_P2.
    induction n; destruct As; simpl; auto; intros; icons2_invert.
    apply IHn.
  Qed.

End ilist2_replace.

Section findIndex.

  (* Find the index of an element in a list matching a comparator.
     Originally used to look up the element of an ilist2 using ith_default. *)

  Variable A : Type. (* The indexing type. *)
  Variable C : Type. (* The type of comparators. *)

  Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Fixpoint findIndex2 (As : list A) (c : C)
  : nat :=
    match As with
      | a :: As' => if AC_eq a c then 0 else S (findIndex2 As' c)
      | _ => 0
    end.

  Lemma findIndex2_In
  : forall (As : list A) (c : C) (a : A),
      In a As -> AC_eq a c = true ->
      findIndex2 As c < List.length As.
  Proof.
    induction As; intros; simpl in *; intuition; subst.
    - rewrite H0; auto with arith.
    - find_if_inside; auto with arith.
      generalize (@IHAs c _ H1 H0); auto with arith.
  Qed.

  Local Hint Resolve findIndex2_In.

  Lemma findIndex2_NIn
  : forall (As : list A) (c : C),
      (forall a, In a As -> AC_eq a c = false) ->
      findIndex2 As c = List.length As.
  Proof.
    induction As; intros; simpl in *; intuition; subst.
    rewrite H; auto.
  Qed.

  Local Hint Resolve findIndex2_NIn.

  Lemma nth_findIndex_In
  : forall (As : list A) (c : C) (a : A),
      In a As -> AC_eq a c = true ->
      forall a a',
        nth (findIndex2 As c) As a = nth (findIndex2 As c) As a'.
  Proof.
    intros; apply nth_indep; eauto.
  Qed.

  Lemma AC_eq_nth_In
  : forall (As : list A) (c : C) (a default_A : A),
      In a As -> AC_eq a c = true ->
      AC_eq (nth (findIndex2 As c) As default_A) c = true.
  Proof.
    induction As; simpl; intros; intuition;
    caseEq (AC_eq a c); eauto; subst; congruence.
  Qed.

  Lemma AC_eq_nth_NIn
  : forall (As : list A) (c c' : C) (a default_A : A),
      c <> c' ->
      In a As -> AC_eq a c = true ->
      (forall a, AC_eq a c = true -> AC_eq a c' = false) ->
      AC_eq (nth (findIndex2 As c) As default_A) c' = false.
  Proof.
    induction As; simpl; intros; intuition;
    caseEq (AC_eq a c); eauto; subst; try congruence.
  Qed.

  Lemma nth_findIndex_NIn
  : forall (As : list A) (c : C),
      (forall a, In a As -> AC_eq a c = false) ->
      forall a, nth (findIndex2 As c) As a = a.
  Proof.
    intros; apply nth_overflow; rewrite findIndex2_NIn;
    auto with arith.
  Qed.

  Lemma In_As
        (As : list A)
        (default_A : A)
  : forall (a : A) (c : C),
      List.In a As -> AC_eq a c = true ->
      List.In (nth (findIndex2 As c) As default_A) As.
  Proof.
    induction As; simpl; intros; destruct H; subst.
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
      -> AC_eq (nth (findIndex2 As c') As default_A) c = true
      -> c = c'.
  Proof.
    induction As; simpl; intros; destruct H; subst.
    - caseEq (AC_eq a0 c'); rewrite H in H1; eauto.
      congruence.
    - caseEq (AC_eq a c'); rewrite H2 in H1; eauto.
  Qed.

End findIndex.
