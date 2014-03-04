Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Pick ADTRefinement.Specs.

Generalizable All Variables.
Set Implicit Arguments.

Section MethodRefinement.
  Variables oldRep newRep : Type.
  (** Old and new representations **)

  Variable BiR : oldRep -> newRep -> Prop.
  (** Bisimulation Relation *)

  Notation "ro ≃ rn" := (BiR ro rn) (at level 70).

  (** Refinement of a mutator method: the values of the computation
      produced by applying a new mutator method [newMutator] to any new
      state [r_n] related to an old state [r_o] by the bisimulation
      relation [BiR] are related by [BiR] to some value produced by
      the corresponding old mutator on [r_o]. Related values
      are taken to related values (with the new mutator potentially
      producing more deterministic computations). That is, the
      following diagram commutes:
<<
                   old mutator
       old rep --------------> old rep
          |                         |
      BiR |                         | BiR
          ↓                         ↓
       new rep --------------> new rep
                   new mutator
>>  *)

  Definition refineMutator
             (oldMutator : mutatorMethodType oldRep)
             (newMutator : mutatorMethodType newRep)
    := forall r_o r_n n, r_o ≃ r_n ->
         refine (r_o' <- oldMutator r_o n;
                 {r_n | r_o' ≃ r_n})
                (newMutator r_n n).

  (** Refinement of an observer method: the computation produced by
   an observer [newObserver] on any new state [r_n] related to an old
   state [r_o] by the bisimulation relation [BiR] should be a refinement
   of the computation produced by the old observer [oldObserver] on
   [r_n].  That is, the following diagram should commute:
<<
                  old observer
       old rep --------------> ℕ
          |                      ∥
      BiR |                      ∥ id
          ↓                      ∥
       new rep --------------> ℕ
                  new observer
>>
   *)

  Definition refineObserver
             (oldObserver : observerMethodType oldRep)
             (newObserver : observerMethodType newRep)
    := forall r_o r_n n, r_o ≃ r_n ->
         refine (oldObserver r_o n)
                (newObserver r_n n).

End MethodRefinement.

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)
Inductive refineADT (A B : ADT) : Prop :=
| refinesADT :
    forall BiR mutatorMap observerMap,
      (forall idx, @refineMutator
                     (Rep A) (Rep B)
                     BiR
                     (MutatorMethods A idx)
                     (MutatorMethods B (mutatorMap idx)))
      -> (forall idx, @refineObserver
                     (Rep A) (Rep B)
                     BiR
                     (ObserverMethods A idx)
                     (ObserverMethods B (observerMap idx)))
      -> refineADT A B.

(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .
