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

    Variable C : Type. (* The type of comparators. *)

    Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Fixpoint findIndex (As : list A) (c : C)
  : nat :=
    match As with
      | a :: As' => if AC_eq a c then 0 else S (findIndex As' c)
      | _ => 0
    end.

  Program Fixpoint ith (As : list A) (il : ilist As) (c : C) (default_A : A)
          (default_B : B default_A)
  {struct As} : B (nth (findIndex As c) As default_A) :=
    match As as As' return ilist As' -> B (nth (findIndex As' c) As' default_A) with
        | a :: As' => (fun H il => _) (@ith As')
        | _ => fun il => _
    end il.
  Next Obligation.
    destruct (AC_eq a c).
    exact (ilist_hd il0).
    exact (H (ilist_tail il0) _ _ default_B).
  Defined.

  Lemma In_ith :
    forall (a : A)
           (As : list A)
           (il : ilist As)
           (c : C)
           (default_A : A)
           (default_B : B default_A),
      In a As -> AC_eq a c = true ->
      forall default_B',
        ith il c default_B' = ith il c default_B.
  Proof.
    induction As; simpl; intros; intuition; subst;
    unfold ith_obligation_2; simpl.
    - rewrite H0; auto.
    - find_if_inside; eauto.
  Qed.

  Variable P : forall a, B a -> Prop.

  Lemma ith_default :
    forall (As : list A)
           (il : ilist As)
           (c : C)
           (default_A : A)
           (default_B default_B' : B default_A),
      (P default_B' -> P default_B)
      -> P (ith il c default_B')
      -> P (ith il c default_B).
  Proof.
    induction As; intros; generalize (ilist_invert il); intros;
    destruct_ex; subst; simpl in *.
    - unfold ith_obligation_1 in *; eauto.
    - unfold ith_obligation_2 in *; destruct (AC_eq a c); eauto.
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

  Lemma ith_imap :
    forall (As : list A)
           (il : ilist _ As)
           (c : C)
           (default_A : A)
           (default_B : B default_A),
      f (ith AC_eq il c default_A default_B) =
      ith AC_eq (imap il) c default_A (f (default_B)).
  Proof.
    induction As; intros; generalize (ilist_invert il);
    intros; destruct_ex; subst; simpl.
    unfold ith_obligation_1; auto.
    unfold ith_obligation_2; auto.
    find_if_inside; simpl; eauto.
  Qed.

End ilist_imap.
