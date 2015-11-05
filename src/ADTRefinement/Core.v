Require Import Fiat.Common Fiat.Computation Fiat.ADT Coq.Sets.Ensembles.

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
        ∥ id              AbsR |
        ∥                      |
       Dom --------------> new rep
          new constructor
>>
   *)

  Fixpoint refineConstructor
           {dom : list Type}
    : constructorType oldRep dom
      -> constructorType newRep dom
      -> Prop :=
    match dom return
          constructorType oldRep dom
          -> constructorType newRep dom
          -> Prop
    with
    | nil => fun oldConstructor newConstructor =>
               refine (r_o' <- oldConstructor;
                       {r_n | r_o' ≃ r_n})
                      (newConstructor)
    | cons D dom' =>
      fun oldConstructor newConstructor =>
        forall d : D,
          @refineConstructor dom' (oldConstructor d)
                             (newConstructor d)
    end.

  (* Variant for use in tactics. *)
    Fixpoint refineConstructor_eq
           {dom : list Type}
    : constructorType oldRep dom
      -> constructorType oldRep dom
      -> Prop :=
    match dom return
          constructorType oldRep dom
          -> constructorType oldRep dom
          -> Prop
    with
    | nil => fun oldConstructor newConstructor =>
               refine oldConstructor newConstructor
    | cons D dom' =>
      fun oldConstructor newConstructor =>
        forall d : D,
          @refineConstructor_eq dom' (oldConstructor d)
                                (newConstructor d)
    end.

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

  Fixpoint refineMethod'
           {dom : list Type}
           {cod : option Type}
    : methodType' oldRep dom cod
      -> methodType' newRep dom cod
      -> Prop :=
    match dom return
          methodType' oldRep dom cod
          -> methodType' newRep dom cod
          -> Prop
    with
    | nil =>
      match cod return
            methodType' oldRep [] cod
            -> methodType' newRep [] cod
            -> Prop
      with
      | Some cod' =>
        fun oldMethod newMethod =>
          refine (r_o' <- oldMethod;
                  r_n' <- {r_n | fst r_o' ≃ r_n};
                  ret (r_n', snd r_o'))
                 newMethod
      | _ =>
        fun oldMethod newMethod =>
          refine (r_o' <- oldMethod;
                  {r_n | r_o' ≃ r_n})
                 newMethod
      end
    | cons D dom' =>
      fun oldMethod newMethod =>
        forall d : D,
          @refineMethod' dom' cod (oldMethod d)
                        (newMethod d)
    end.

  Definition refineMethod
             {dom : list Type}
             {cod : option Type}
             (oldMethod : methodType oldRep dom cod)
             (newMethod : methodType newRep dom cod)
    := forall r_o r_n,
      r_o ≃ r_n ->
      @refineMethod' dom cod (oldMethod r_o) (newMethod r_n).

    Fixpoint refineMethod_eq'
           {dom : list Type}
           {cod : option Type}
    : methodType' oldRep dom cod
      -> methodType' oldRep dom cod
      -> Prop :=
    match dom return
          methodType' oldRep dom cod
          -> methodType' oldRep dom cod
          -> Prop
    with
    | nil =>
      match cod return
            methodType' oldRep [] cod
            -> methodType' oldRep [] cod
            -> Prop
      with
      | Some cod' =>
        fun oldMethod newMethod =>
          refine oldMethod newMethod
      | _ =>
        fun oldMethod newMethod =>
          refine oldMethod newMethod
      end
    | cons D dom' =>
      fun oldMethod newMethod =>
        forall d : D,
          @refineMethod_eq' dom' cod (oldMethod d)
                        (newMethod d)
    end.

  Definition refineMethod_eq
             {dom : list Type}
             {cod : option Type}
             (oldMethod : methodType oldRep dom cod)
             (newMethod : methodType oldRep dom cod)
    := forall r_o,
      @refineMethod_eq' dom cod (oldMethod r_o) (newMethod r_o).

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


Notation "ro ≃ rn" := (@AbsR _ _ _ _ ro rn) (at level 70).
