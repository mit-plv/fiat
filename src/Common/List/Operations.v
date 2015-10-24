(** Useful list operations *)
Require Import Coq.Lists.List.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Fixpoint drop {A} (n : nat) (ls : list A) : list A
  := match n, ls with
       | 0, _ => ls
       | S n', nil => nil
       | S n', x::xs => drop n' xs
     end.

Fixpoint take {A} (n : nat) (ls : list A) : list A
  := match n, ls with
       | 0, _ => nil
       | _, nil => nil
       | S n', x::xs => x::take n' xs
     end.

Definition uniquize {A} (beq : A -> A -> bool) (ls : list A) : list A
  := fold_right
       (fun x xs => if list_bin beq x xs then xs else x::xs)
       nil
       ls.

Definition drop_all_but {A} (n : nat) (ls : list A) : list A
  := drop (List.length ls - n) ls.

Definition rev_nth {A} (n : nat) (ls : list A) : A -> A
  := List.nth (List.length ls - n) ls.

Arguments drop_all_but : simpl never.
Arguments rev_nth : simpl never.

Fixpoint enumerate {A} (ls : list A) (start : nat) : list (nat * A)
  := match ls with
       | nil => nil
       | x::xs => (start, x)::enumerate xs (S start)
     end.

Definition disjoint {A} (eq_A : A -> A -> bool) (ls1 ls2 : list A) : bool
  := fold_right
       andb
       true
       (map
          (fun x => negb (list_bin eq_A x ls2))
          ls1).

Lemma disjoint_bl {A eq_A} (lb : forall x y : A, x = y -> eq_A x y = true) ls1 ls2
      (H : disjoint eq_A ls1 ls2 = true)
: forall x, List.In x ls1 -> List.In x ls2 -> False.
Proof.
  unfold disjoint in *.
  induction ls1; simpl in *; trivial.
  apply Bool.andb_true_iff in H.
  destruct H as [H0 H1].
  specialize (IHls1 H1).
  intros x [H'|H']; eauto; subst.
  apply Bool.negb_true_iff, Bool.not_true_iff_false in H0.
  specialize (fun k => H0 (list_in_lb lb k)); assumption.
Defined.

Lemma disjoint_lb {A eq_A} (bl : forall x y : A, eq_A x y = true -> x = y) ls1 ls2
      (H : forall x, List.In x ls1 -> List.In x ls2 -> False)
: disjoint eq_A ls1 ls2 = true.
Proof.
  unfold disjoint in *.
  induction ls1; simpl in *; trivial.
  rewrite IHls1 by intuition eauto.
  rewrite Bool.andb_comm; simpl.
  apply Bool.negb_true_iff, Bool.not_true_iff_false.
  intro H'.
  apply list_in_bl in H'; trivial; [].
  intuition eauto.
Defined.

Lemma disjoint_comm {A eq_A}
      ls1 ls2
: disjoint (A := A) eq_A ls1 ls2 = disjoint (fun x y => eq_A y x) ls2 ls1.
Proof.
  unfold disjoint.
  revert ls2.
  induction ls1; simpl; trivial.
  { induction ls2; eauto. }
  { intro ls2.
    rewrite IHls1; clear IHls1.
    revert a ls1.
    induction ls2; simpl; trivial.
    { intros.
      rewrite <- IHls2; simpl.
      rewrite !Bool.negb_orb.
      rewrite !Bool.andb_assoc.
      repeat (f_equal; []).
      rewrite !(Bool.andb_comm _ (negb (eq_A _ _))).
      rewrite <- !Bool.andb_assoc.
      repeat (f_equal; []).
      apply Bool.andb_comm. } }
Qed.

Definition included {A} (eq_A : A -> A -> bool) (ls1 ls2 : list A) : bool
  := fold_right
       andb
       true
       (map
          (fun x => list_bin eq_A x ls2)
          ls1).

Lemma included_bl {A eq_A} (bl : forall x y : A, eq_A x y = true -> x = y) ls1 ls2
      (H : included eq_A ls1 ls2 = true)
: incl ls1 ls2.
Proof.
  unfold included, incl in *.
  induction ls1; simpl in *; trivial; try tauto.
  apply Bool.andb_true_iff in H.
  destruct H as [H0 H1].
  specialize (IHls1 H1).
  intros x [H'|H']; eauto; subst.
  eapply list_in_bl; eassumption.
Defined.

Lemma included_lb {A eq_A} (lb : forall x y : A, x = y -> eq_A x y = true) ls1 ls2
      (H : incl ls1 ls2)
: included eq_A ls1 ls2 = true.
Proof.
  unfold included, incl in *.
  induction ls1; simpl in *; trivial.
  (rewrite IHls1 by intuition eauto); clear IHls1.
  rewrite Bool.andb_comm; simpl.
  eapply list_in_lb; eauto.
Defined.

Fixpoint first_index_error {A} (f : A -> bool) (ls : list A) : option nat
  := match ls with
       | nil => None
       | x::xs => if f x then Some 0 else option_map S (first_index_error f xs)
     end.

Fixpoint first_index {A} (f : A -> bool) (ls : list A) : nat
  := match ls with
       | nil => 0
       | x::xs => if f x then 0 else S (first_index f xs)
     end.

Fixpoint first_index_recr {A B R} (f : A -> B -> option R) (ls : list A) (ls' : list B)
: option (nat * R)
  := match ls, ls' with
       | nil, _ => None
       | _, nil => None
       | x::xs, y::ys =>
         match f x y with
           | None => option_map (fun ab => (S (fst ab), snd ab)) (first_index_recr f xs ys)
           | Some r => Some (0, r)
         end
     end.
