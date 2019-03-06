Require Import Coq.Lists.List Coq.Sets.Ensembles.
Require Import Fiat.Computation.Core Fiat.Computation.Notations
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.Common.Ensembles.Cardinal.

Set Implicit Arguments.

Local Open Scope comp_scope.

Definition elements {A} (ls : list A) : Ensemble A := fun x => List.In x ls.

Definition cardinal {A} (ls : list A) : Comp nat
  := Pick (cardinal _ (elements ls)).

Definition to_list {A} (S : Ensemble A) : Comp (list A) :=
  { ls : list _ | EnsembleListEquivalence S ls }.

(** QUESTION: Should I switch [fold_right] and [Ensemble_fold_right]?
    Which is more common? *)
Definition fold_right {A B}
           (f : A -> B -> Comp B) (b : Comp B) (S : Ensemble A)
: Comp B
  := (ls <- to_list S;
      List.fold_right (fun a b' => Bind b' (f a)) b ls).

Definition Ensemble_fold_right {A B}
           (f : A -> B -> B) (b : B) (S : Ensemble A)
: Comp B
  := fold_right (fun a b => ret (f a b)) (ret b) S.

Definition list_filter_pred {T} (P : T -> Prop) (ls : list T)
  := List.fold_right
       (fun (a : T) (xs : Comp (list T)) =>
          (xs' <- xs;
           b <- { b : bool | b = true <-> P a };
           ret (if b then a::xs' else xs')))
       (ret nil)
       ls.

Definition filter_pred {T} (P : T -> Prop) (S : Ensemble T)
  := fold_right
       (fun (a : T) (xs : list T) =>
          (b <- { b : bool | b = true <-> P a };
           ret (if b then a::xs else xs)))
       (ret nil)
       S.
