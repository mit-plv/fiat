Require Import Common Computation ADT Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Section MethodRefinement.
  Variables oldRep newRep : Type.
  (** Old and new representations **)

  Variable SiR : oldRep -> newRep -> Prop.
  (** Simulation Relation *)

  Notation "ro ≃ rn" := (SiR ro rn) (at level 70).

  (** Refinement of a mutator method: the values of the computation
      produced by applying a new mutator method [newMutator] to any new
      state [r_n] related to an old state [r_o] by the simulation
      relation [SiR] are related by [SiR] to some value produced by
      the corresponding old mutator on [r_o]. Related values
      are taken to related values (with the new mutator potentially
      producing more deterministic computations). That is, the
      following diagram commutes:
<<
                   old mutator
       old rep --------------> old rep
          |                         |
      SiR |                         | SiR
          ↓                         ↓
       new rep --------------> new rep
                   new mutator
>>  *)

  Definition refineMutator
             (Dom : Type)
             (oldMutator : mutatorMethodType oldRep Dom)
             (newMutator : mutatorMethodType newRep Dom)
    := forall r_o r_n n, r_o ≃ r_n ->
         refine (r_o' <- oldMutator r_o n;
                 {r_n | r_o' ≃ r_n})
                (newMutator r_n n).

  (** Refinement of an observer method: the computation produced by
   an observer [newObserver] on any new state [r_n] related to an old
   state [r_o] by the simulation relation [SiR] should be a refinement
   of the computation produced by the old observer [oldObserver] on
   [r_n].  That is, the following diagram should commute:
<<
                  old observer
       old rep --------------> ℕ
          |                      ∥
      SiR |                      ∥ id
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
         refine (oldObserver r_o n)
                (newObserver r_n n).

End MethodRefinement.

Notation "c ↝ v" := (computes_to c v) (at level 70).

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods.  We place [refineADT] in [Type] so that
    we can extract the simulation relation. *)

Record refineADT {Sig} (A B : ADT Sig) :=
  refinesADT {
      SiR : _;
      ADTRefinementPreservesMutators
      : forall idx : MutatorIndex Sig,
          @refineMutator
            (Rep A) (Rep B) SiR
            (MutatorDom Sig idx)
            (MutatorMethods A idx)
            (MutatorMethods B idx);
      ADTRefinementPreservesObservers
      : forall idx : ObserverIndex Sig,
          @refineObserver
            (Rep A) (Rep B) SiR
            (fst (ObserverDomCod Sig idx))
            (snd (ObserverDomCod Sig idx))
            (ObserverMethods A idx)
            (ObserverMethods B idx) }.
(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .

Notation "ro ≃ rn" := (@SiR _ _ _ _ ro rn) (at level 70).

(*(** If our goal is a [Prop], then we can extract the simulation relation. *)
Definition refineADT_SiR_elim {Sig} {A B : ADT Sig} (P : Prop)
           (H : (Rep A -> Rep B -> Prop) -> P)
           (H' : refineADT A B)
: P
  := match H' with
       | refinesADT SiR _ _ => H SiR
     end.*)
