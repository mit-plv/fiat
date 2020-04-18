(** Useful list operations *)
Require Import Coq.Lists.List.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Module Export List.
  Scheme Minimality for list Sort Type.
  Scheme Minimality for list Sort Set.
  Scheme Minimality for list Sort Prop.

  Definition list_caset A (P : list A -> Type) (N : P nil) (C : forall x xs, P (x::xs))
             ls
  : P ls
    := match ls with
         | nil => N
         | x::xs => C x xs
       end.

  Definition list_caset_nodep {A} (P : Type) (N : P) (C : A -> list A -> P)
             ls
    : P
    := match ls with
       | nil => N
       | x::xs => C x xs
       end.

 Section InT.
    Context {A : Type} (a : A).

    Fixpoint InT (ls : list A) : Set
      := match ls return Set with
           | nil => False
           | b :: m => (b = a) + InT m
         end%type.
  End InT.

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

  Fixpoint up_to (n : nat) : list nat :=
    match n with
      | 0 => nil
      | S n' => n'::up_to n'
    end.

  Definition drop_all_but {A} (n : nat) (ls : list A) : list A
    := drop (List.length ls - n) ls.

  Definition rev_nth {A} (n : nat) (ls : list A) : A -> A
    := List.nth (List.length ls - n) ls.

  Arguments drop_all_but : simpl never.
  Arguments rev_nth : simpl never.

  Fixpoint nth'_helper {A} (n : nat) (ls : list A) (default : A) (offset : nat) :=
    match ls with
      | nil => default
      | x::xs => if EqNat.beq_nat n offset
                 then x
                 else nth'_helper n xs default (S offset)
    end.

  Definition nth' {A} (n : nat) (ls : list A) (default : A) :=
    Eval unfold nth'_helper in nth'_helper n ls default 0.

  Section filter_out.
    Context {A} (f : A -> bool).

    Fixpoint filter_out (ls : list A) : list A
      := match ls with
           | nil => nil
           | x::xs => if f x then filter_out xs else x::filter_out xs
         end.
  End filter_out.

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

  Section first_index_f.
    Context {A B} (f : A -> bool) (rect : option (nat * A) -> B).

    Definition first_index_helper (ls : list A) (rec : nat * A -> nat * A) : B
      := list_rect
           (fun _ => (nat * A -> nat * A) -> B)
           (fun _ => rect None)
           (fun x xs first_index_helper_xs rec
            => bool_rect_nodep
                 _
                 (rect (Some (rec (0, x))))
                 (first_index_helper_xs (fun x => rec (S (fst x), snd x)))
                 (f x))
           ls
           rec.
  End first_index_f.

  Definition first_index_default {A} (f : A -> bool) (default : nat) (ls : list A) : nat
    := first_index_helper f (option_rect (fun _ => nat) fst default) ls (fun x => x).

  Global Arguments first_index_default _ _ _ !_ / .

  Definition first_index_error {A} (f : A -> bool) (ls : list A) : option nat
    := first_index_helper f (option_map fst) ls (fun x => x).

  Global Arguments first_index_error _ _ !_ / .

  Definition first_index_and_value_option {A} (ls : list (option A)) : option (nat * A)
    := first_index_helper
         (B := option (nat * A))
         (fun x => match x with
                     | None => false
                     | Some _ => true
                   end)
         (fun x => match x with
                     | Some (x1, Some x2) => Some (x1, x2)
                     | _ => None
                   end)
         ls
         (fun x => x).

  Global Arguments first_index_and_value_option _ !_ / .

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

  Fixpoint first_index_partial {A} (f : A -> option bool) (ls : list A) : option (option nat) :=
    match ls with
    | nil => Some None
    | x :: xs =>
      match f x with
      | None => None
      | Some b =>
        if b then
          Some (Some 0)
        else
          match first_index_partial f xs with
          | Some (Some i) => Some (Some (S i))
          | v => v
          end
      end
    end.

  Definition first_index_default_partial {A} (f : A -> option bool) (default : nat) (ls : list A) :=
    match first_index_partial f ls with
    | None => None
    | Some None => Some default
    | Some v => v
    end.

  Fixpoint sig_In {A} (ls : list A) : list { x : A | List.In x ls }
    := match ls return list { x : A | List.In x ls } with
         | nil => nil
         | x::xs
           => (exist _ x (or_introl eq_refl))
                :: (List.map
                      (fun xp => exist _ (proj1_sig xp) (or_intror (proj2_sig xp)))
                      (@sig_In A xs))
       end.
End List.
