Require Import Coq.Sets.Ensembles
        Coq.Lists.List.

Require Import Fiat.Computation.

(* Operations on lists using computations. *)

Section ListComprehension.

  Context {A : Type}.

  Definition ListComprehension
             (P : Ensemble A)
    := {l | forall x, List.In x l <-> P x }.

  Definition FilteredList
             (P : Ensemble A)
             (xs : list A)
    := ListComprehension (fun x => List.In x xs /\ P x).

  Definition build_FilteredList
             (P : Ensemble A)
             (xs : list A)
    : Comp (list A)
    := fold_right (fun (a : A) (l : Comp (list A)) =>
                     l' <- l;
                     b <- { b | decides b (P a) };
                     if b
                     then ret (a :: l')
                     else ret l'
                  ) (ret nil) xs.

  Definition refine_ListComprehension_filtered_list
    : forall (P : Ensemble A)
             (xs : list A),
      refine (FilteredList P xs)
             (build_FilteredList P xs).
  Proof.
    unfold FilteredList, ListComprehension; induction xs; simpl; intros.
    - refine pick val _; try reflexivity; intuition.
    - rewrite <- IHxs.
      unfold refine; intros; computes_to_inv.
      destruct v1; simpl in *; computes_to_inv;
        subst; computes_to_econstructor; simpl;
          setoid_rewrite H; intuition.
      + subst; eauto.
      + subst; intuition.
  Qed.

End ListComprehension.

Notation "⟦ x 'in' xs | P ⟧" :=
  (FilteredList (fun x => P) xs) : comp_scope.

Section UpperBound.

  Context {A : Type}.
  Variable op : A -> A -> Prop.

  Definition UpperBound
             (rs : list A)
             (r : A) :=
    forall r' : A, List.In r' rs -> op r r'.

  Definition SingletonSet (P : Ensemble A) :=
    {b' | forall b : A, b' = Some b <-> P b}.

  Definition ArgMax
             {B}
             (f : B -> A)
    : Ensemble B :=
    fun b => forall b', op (f b') (f b).

  Definition MaxElements
             (elements : Comp (list A))
    := elements' <- elements;
         ⟦ element in elements' | UpperBound elements' element ⟧.

End UpperBound.
