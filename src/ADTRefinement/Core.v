Require Import Common Computation ADT Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Section MethodRefinement.

  (** Old and new representations **)
  Variables oldRep newRep : Type.

  (** Abstraction Relation *)
  Variable AbsR : oldRep -> newRep -> Prop.

  Notation "ro ≃ rn" := (AbsR ro rn) (at level 70).

  (** Refinement of a constructor: the computation produced by
   a constructor [newConstructor] should be a refinement
   of the computation produced by the old constructor [oldObserver] on
   [d].  That is, the following diagram should commute:
<<
           old constructor
       Dom --------------> old rep
        ∥                      |
        ∥ id               AbsR |
        ∥                      |
       Dom --------------> new rep
          new constructor
>>
   *)

  Definition refineConstructor
             (Dom : Type)
             (oldConstructor : constructorType oldRep Dom)
             (newConstructor : constructorType newRep Dom)
    := forall d,
         refine (r_o' <- oldConstructor d;
                 {r_n | r_o' ≃ r_n})
                (newConstructor d).

  (** Refinement of a method : the values of the computation
      produced by applying a new method [newMethod] to any new
      state [r_n] related to an old state [r_o] by the abstraction
      relation [AbsR] are related by [AbsR] to some value produced by
      the corresponding old method on [r_o]. Related values
      are taken to related values (with the new method potentially
      producing more deterministic computations). That is, the
      following diagram commutes:
<<
                   old method
       old rep --------------> old rep
          |                         |
      AbsR |                         | AbsR
          ↓                         ↓
       new rep --------------> new rep
                   new method
>>  *)

  Definition refineMethod
             (Dom Cod : Type)
             (oldMethod : methodType oldRep Dom Cod)
             (newMethod : methodType newRep Dom Cod)
    := forall r_o r_n d, r_o ≃ r_n ->
         refine (r_o' <- oldMethod r_o d;
                 r_n' <- {r_n | fst r_o' ≃ r_n};
                 ret (r_n', snd r_o'))
                (newMethod r_n d).

End MethodRefinement.

Record refineADT {Sig} (A B : ADT Sig) :=
  refinesADT {
      AbsR : _;
      ADTRefinementPreservesConstructors
      : forall idx : ConstructorIndex Sig,
          @refineConstructor
            (Rep A) (Rep B) AbsR
            (ConstructorDom Sig idx)
            (Constructors A idx)
            (Constructors B idx);
      ADTRefinementPreservesMethods
      : forall idx : MethodIndex Sig,
          @refineMethod
            (Rep A) (Rep B) AbsR
            (fst (MethodDomCod Sig idx))
            (snd (MethodDomCod Sig idx))
            (Methods A idx)
            (Methods B idx) }.
(** We should always just unfold [refineMethod] and [refineConstructor]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMethod / .
Arguments refineConstructor / .

Notation "ro ≃ rn" := (@AbsR _ _ _ _ ro rn) (at level 70).
