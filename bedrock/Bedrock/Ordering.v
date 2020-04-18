Require Import Coq.Lists.List.

Section ListLexOrder.
  Variable T : Type.
  Variable cmp : T -> T -> comparison.

  Fixpoint list_lex_cmp (ls rs : list T) : comparison :=
    match ls , rs with
      | nil , nil => Eq
      | nil , _ => Lt
      | _ , nil => Gt
      | l :: ls , r :: rs =>
        match cmp l r with
          | Eq => list_lex_cmp ls rs
          | x => x
        end
    end.
End ListLexOrder.

Section Sorting.
  Variable T : Type.
  Variable cmp : T -> T -> comparison.

  Section insert.
    Variable val : T.

    Fixpoint insert_in_order (ls : list T) : list T :=
      match ls with
        | nil => val :: nil
        | l :: ls' =>
          match cmp val l with
            | Gt => l :: insert_in_order ls'
            | _ => val :: ls
          end
      end.
  End insert.

  Fixpoint sort (ls : list T) : list T :=
    match ls with
      | nil => nil
      | l :: ls =>
        insert_in_order l (sort ls)
    end.

End Sorting.

Lemma insert_in_order_inserts : forall T C x l,
  exists h t, insert_in_order T C x l = h ++ x :: t /\ l = h ++ t.
Proof.
  clear. induction l; simpl; intros.
  exists nil; exists nil; eauto.
  destruct (C x a).
  exists nil; simpl. eauto.
  exists nil; simpl. eauto.
  destruct IHl. destruct H. intuition. subst.
  rewrite H0. exists (a :: x0). exists x1. simpl; eauto.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma sort_permutation : forall T (C : T -> T -> _) x,
  Permutation (sort _ C x) x.
Proof.
  induction x; simpl.
  { reflexivity. }
  { destruct (insert_in_order_inserts T C a (sort T C x)) as [ ? [ ? ? ] ].
    destruct H. rewrite H. rewrite <- Permutation_cons_app. reflexivity. rewrite H0 in *. symmetry; auto. }
Qed.
