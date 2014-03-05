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
             (Dom : Type)
             (oldMutator : mutatorMethodType oldRep Dom)
             (newMutator : mutatorMethodType newRep Dom)
    := forall r_o r_n n, r_o ≃ r_n ->
         refineBundled `[r_o' <- oldMutator r_o n;
                 {r_n | r_o' ≃ r_n} ]`
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
             (Dom Cod : Type)
             (oldObserver : observerMethodType oldRep Dom Cod)
             (newObserver : observerMethodType newRep Dom Cod)
    := forall r_o r_n n, r_o ≃ r_n ->
         refineBundled (oldObserver r_o n)
                (newObserver r_n n).

End MethodRefinement.

Notation "c ↝ v" := (computes_to c v) (at level 70).

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)

Inductive refineADT : ADT -> ADT -> Prop :=
| refinesADT :
    forall repA mutatorIndexA observerIndexA
           B
           mutatorMap observerMap
           mutatorMethodsA observerMethodsA
           SiR,
      (forall idx : mutatorIndexA, @refineMutator
                     repA (Rep B) SiR
                     (MutatorDom B (mutatorMap idx))
                     (MutatorMethods
                        {| Rep := repA;
                           UnbundledMutatorMethods := mutatorMethodsA;
                           UnbundledObserverMethods := observerMethodsA
                        |}
                        idx)
                     (MutatorMethods B (mutatorMap idx)))
      -> (forall idx : observerIndexA, @refineObserver
                     repA (Rep B) SiR
                     (ObserverDom B (observerMap idx))
                     (ObserverCod B (observerMap idx))
                     (ObserverMethods {| Rep := repA;
                                         UnbundledMutatorMethods := mutatorMethodsA;
                                         UnbundledObserverMethods := observerMethodsA
                                      |} idx)
                     (ObserverMethods B (observerMap idx)))
      -> refineADT {| Rep := repA;
                      UnbundledMutatorMethods := mutatorMethodsA;
                      UnbundledObserverMethods := observerMethodsA
                   |} B.

(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .
