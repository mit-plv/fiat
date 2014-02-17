Require Import Common Computation ADT Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(* Specification of mutator method. *)
Definition mutatorMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final Model *)
  -> Prop.

(* Specification of an observer method *)
Definition observerMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> nat (* Return value *)
  -> Prop.

(** Every spec is trivially implementable using [Pick]. *)
Section pick.
  Variable rep : Type.
  Variable mutatorMethodIndex : Type.
  Variable observerMethodIndex : Type.
  Variable mutatorMethodSpecs : mutatorMethodIndex -> mutatorMethodSpec rep.
  Variable observerMethodSpecs : observerMethodIndex -> observerMethodSpec rep.

  Local Obligation Tactic := econstructor; eauto.

  Program Definition pickImpl : ADT :=
    {|
      Rep := rep;
      RepInv m := True;
      MutatorIndex := mutatorMethodIndex;
      ObserverIndex := observerMethodIndex;
      MutatorMethods idx :=
        fun r x =>
          { r' : rep
          | mutatorMethodSpecs idx r x r'}%comp;
      ObserverMethods idx :=
        fun r n =>
          { n' : nat
          | observerMethodSpecs idx r n n'}%comp
    |}.

End pick.

Section MethodRefinement.
  Variables oldRep newRep : Type.
  (** Old and new representations **)

  Variable oldRepInv : Ensemble oldRep.
  Variable newRepInv : Ensemble newRep.
  (** Old and new representation invariants **)

  Variable abs : newRep -> Comp oldRep.
  (** Abstraction function *)

  (** Refinement of a mutator method: if we first do the new
      computation and then abstract, this is a refinement of first
      abstracting and then doing the old computation.  That is, the
      following diagram commutes:
<<
                   old mutator
       old rep --------------> old rep
          ↑                         ↑
      abs |                         | abs
          |                         |
       new rep --------------> new rep
                   new mutator
>>  *)

  Definition refineMutator
             (oldMutator : mutatorMethodType oldRep)
             (newMutator : mutatorMethodType newRep)
    := forall new_state n,
         newRepInv new_state ->
         refine (old_state <- abs new_state;
                 oldMutator old_state n)
                (new_state' <- newMutator new_state n;
                 abs new_state').

  (** Refinement of an observer method: the new computation should be
      a refinement of first abstracting and then doing the old
      computation.  That is, the following diagram should commute:
<<
                  old observer
       old rep --------------> ℕ
          ↑                      ∥
      abs |                      ∥ id
          |                      ∥
       new rep --------------> ℕ
                  new observer
>>
   *)
  Definition refineObserver
             (oldObserver : observerMethodType oldRep)
             (newObserver : observerMethodType newRep)
    := forall new_state n,
         newRepInv new_state ->
         refine (old_state <- abs new_state;
                 oldObserver old_state n)
                (newObserver new_state n).

  (**  Abstraction should preserve representation invariants:
       The abstraction of a new representation that satisfies its
       representation invariant should satisfy the old invariant.
       Diagrammatically,

  (Old RepInv holds)
      old rep
        ↑
        | abs
        |
       new rep
  (New RepInv holds)
   **)

  Definition absPreservesInv
    := forall new_state,
         newRepInv new_state ->
         computational_inv oldRepInv (abs new_state).

End MethodRefinement.

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)
Inductive refineADT (A B : ADT) : Prop :=
| refinesADT :
    forall abs mutatorMap observerMap,
      (forall idx, @refineMutator
                     (Rep A) (Rep B)
                     (RepInv B) abs
                     (MutatorMethods A idx)
                     (MutatorMethods B (mutatorMap idx)))
      -> (forall idx, @refineObserver
                     (Rep A) (Rep B)
                     (RepInv B) abs
                     (ObserverMethods A idx)
                     (ObserverMethods B (observerMap idx)))
      -> (@absPreservesInv (Rep A) (Rep B)
                 (RepInv A) (RepInv B) abs)
      -> refineADT A B.

(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .
Arguments absPreservesInv / .

Instance refineMutator_refl rep repInv
: Reflexive (@refineMutator rep rep repInv (@Return _)).
Proof.
  intro; simpl; intros.
  autorewrite with refine_monad; reflexivity.
Qed.

Instance refineObserver_refl rep repInv
: Reflexive (@refineObserver rep rep repInv (@Return _)).
Proof.
  intro; simpl; intros.
  autorewrite with refine_monad; reflexivity.
Qed.

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (abs := @Return _)
      (mutatorMap := id)
      (observerMap := id);
      unfold id;
      try reflexivity.
    simpl; intros;
      inversion_by computes_to_inv; subst; eauto.
  - intros x y z
           [abs mutMap obsMap mutH obsH]
           [abs' mutMap' obsMap' mutH' obsH'].
    econstructor 1 with
      (abs := fun z => (z' <- abs' z; abs z')%comp)
        (mutatorMap := mutMap' ∘ mutMap)
        (observerMap := obsMap' ∘ obsMap);
    unfold id, compose; simpl in *; intros.
    + autorewrite with refine_monad.
      rewrite <- !refineEquiv_bind_bind, <- mutH', !refineEquiv_bind_bind; eauto.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor; eauto.
      eapply mutH; eauto.
    + autorewrite with refine_monad.
      rewrite <- !refineEquiv_bind_bind, <- obsH', refineEquiv_bind_bind; eauto.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor; eauto.
      eapply obsH; eauto.
    + inversion_by computes_to_inv; eauto.
Qed.

Add Parametric Relation : ADT refineADT
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as refineADT_rel.

(* To derive an ADT interactively from a specification [spec], we can build a dependent
   product [ {adt | refineADT spec adt} ]. The derivation flow has the form:
   1. Apply a refinement.
   2. Discharge any side conditions.
   3. Repeat steps 1-2 until adt is completely specialized.

   My (Ben's) current thought is that to make this as pleasant as possible,
   the refinements used in the first step should be implemented using tactics
   which present the user with 'nice' side conditions. (In particular, this lets us
   be careful about not having any dangling existential variables at the end of a
   derivation).

   Aside on notation:
   When naming these tactics, I wanted one which wasn't already used by a tactic-
   refine, specialize, and replace were taken. The thesaurus suggested 'hone'.
   This kind of agrees with 'BedRock' (in as much as a WhetStone is used to sharpen
   knives), so I'm carrying on the naming convention with a 'Sharpened' notation
   for the dependent products. *)

  Notation Sharpened spec := {adt | refineADT spec adt}.

  (* A single refinement step. *)
  Definition SharpenStep adt :
    forall adt',
      refineADT adt adt' ->
      Sharpened adt' ->
      Sharpened adt.
  Proof.
    intros adt' refineA SpecA';
    eexists (proj1_sig SpecA'); rewrite refineA; exact (proj2_sig SpecA').
  Defined.

  (* A tactic for finishing a derivation. Probably needs a better name.*)
  Tactic Notation "finish" "sharpening" := eexists; reflexivity.

Section GeneralRefinements.

  (* Refining Observers is a valid ADT refinement. *)
  Add Parametric Morphism rep repInv mutIdx obsIdx ms mutInv
  : (fun os => @Build_ADT rep repInv mutIdx obsIdx ms os mutInv)
    with signature
    (pointwise_relation _ (@refineObserver _ _ repInv (@Return _)))
      ==> refineADT
      as refineADT_Build_ADT_Observer.
  Proof.
    intros.
    let A := match goal with |- refineADT ?A ?B => constr:(A) end in
    let B := match goal with |- refineADT ?A ?B => constr:(B) end in
    eapply (@refinesADT A B (@Return _) id id);
      unfold id, pointwise_relation in *; simpl in *; intros;
      auto; try inversion_by computes_to_inv; subst; eauto;
      autorewrite with refine_monad; reflexivity.
  Qed.

  (* Refining Mutators is also a valid ADT refinement, but it's
   harder to express as a morphism because of the dependence of
   [MutatorMethodsInv] on [MutatorMethods]. *)

  Lemma refineMutatorInv
        {rep : Type} (repInv : Ensemble rep)
        {mutIdx : Type}
  : forall (muts muts' : mutIdx -> mutatorMethodType rep),
      mutatorInv repInv muts ->
      pointwise_relation mutIdx (refineMutator repInv (@Return _)) muts muts'->
      mutatorInv repInv muts'.
  Proof.
    simpl; unfold pointwise_relation; intros; eapply_hyp; eauto.
    generalize (H0 idx _ n H1).
    setoid_rewrite refine_refine; autorewrite with refine_monad; try reflexivity; eauto.
  Qed.

  Hint Resolve refineMutatorInv.

  (* The [refineADT_Build_ADT_Mutators lemma shows that refining mutators
   is a valid ADT refinement; the statement hews closely to the standard
   Parametric Morphism declaration style for future compatibility (hopefully). *)

  Lemma refineADT_Build_ADT_Mutators rep (repInv : Ensemble rep) mutIdx obsIdx obs :
    (respectful_hetero
       _ _ (fun x => mutatorInv repInv x -> ADT) (fun x => mutatorInv _ x -> ADT)
       (pointwise_relation mutIdx (@refineMutator rep rep repInv (@Return _)))
       (fun x y mInv mInv' => forall mI mI', refineADT (mInv mI) (mInv' mI')))
      (fun mut => @Build_ADT rep repInv mutIdx obsIdx mut obs) (fun mut => @Build_ADT rep repInv mutIdx obsIdx mut obs).
  Proof.
    unfold respectful_hetero; intros.
    let A := match goal with |- refineADT ?A ?B => constr:(A) end in
    let B := match goal with |- refineADT ?A ?B => constr:(B) end in
    eapply (@refinesADT A B (@Return _) id id);
      unfold id, pointwise_relation in *; simpl in *; intros;
      [ auto
      | autorewrite with refine_monad; reflexivity
      | inversion_by computes_to_inv; subst; eauto].
  Qed.

  (* [BD: I'm registering the above as a proper relation on the off-chance that the
   setoid machinary can take advantage of it :) ]*)
  Instance refineADT_Build_ADT_Mutators_Proper rep (repInv : Ensemble rep) mutIdx obsIdx obs :
    Proper
      (respectful_hetero
         _ _ (fun x => mutatorInv repInv x -> ADT) (fun x => mutatorInv _ x -> ADT)
         (pointwise_relation mutIdx (@refineMutator rep rep repInv (@Return _)))
         (fun x y mInv mInv' => forall mI mI', refineADT (mInv mI) (mInv' mI')))
      (fun mut => @Build_ADT rep repInv mutIdx obsIdx mut obs).
  Proof.
    apply refineADT_Build_ADT_Mutators.
  Qed.

  (* If the proof of [MutatorMethodsInv] doesn't depend on [MutatorMethods]
   there's no problem using the existing Parametric Morphism machinery.
   (Of course, this means that repInv is trivial.) *)

  Add Parametric Morphism rep repInv mutIdx obsIdx mutInv
  : (fun ms os => @Build_ADT rep repInv mutIdx obsIdx ms os (mutInv ms))
      with signature
      (pointwise_relation _ (@refineMutator _ _ repInv (@Return _)))
        ==> (pointwise_relation _ (@refineObserver _ _ repInv (@Return _)))
        ==> refineADT
        as refineADT_Build_ADT_Mutators'.
  Proof.
    intros.
    let A := match goal with |- refineADT ?A ?B => constr:(A) end in
    let B := match goal with |- refineADT ?A ?B => constr:(B) end in
    eapply (@refinesADT A B (@Return _) id id);
      unfold id, pointwise_relation in *; simpl in *; intros;
      auto; inversion_by computes_to_inv; subst; eauto.
  Qed.

  (* Refining observers and mutators at the same time is also a valid
   refinement. [BD: I've come to the conclusion that smaller refinement
   steps are better, so using the previous refinements should be the
   preferred mode. ]*)

  Lemma refineADT_Build_ADT_Both rep (repInv : Ensemble rep) mutIdx obsIdx :
    (respectful_hetero
       _ _ _ _
       (pointwise_relation mutIdx (@refineMutator rep rep repInv (@Return _)))
       (fun x y => respectful_hetero
                     _ _ (fun _ => mutatorInv repInv x -> ADT) (fun _ => mutatorInv _ y -> ADT)
                     (pointwise_relation obsIdx (@refineObserver rep rep repInv (@Return _)))
                     (fun obs obs' mInv mInv' =>
                        forall mI mI', refineADT (mInv mI) (mInv' mI'))))
      (@Build_ADT rep repInv mutIdx obsIdx) (@Build_ADT rep repInv mutIdx obsIdx).
  Proof.
    unfold respectful_hetero; intros.
    rewrite refineADT_Build_ADT_Observer; eauto.
    eapply refineADT_Build_ADT_Mutators; eauto.
  Qed.

  (** If we had dependent setoid relations in [Type], then we could write

<<
Add Parametric Morphism : @Build_ADT
  with signature
  (fun oldM newM => newM -> Comp oldM)
    ==> arrow
    ==> arrow
    ==> (pointwise_relation _ (@refineMutator _ _ _))
    ==> (pointwise_relation _ (@refineObserver _ _ _))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  ...
Qed.
>>

    But, alas, Matthieu is still working on those.  So the rewrite
    machinery won't work very well when we're switching reps, and
    we'll instead have to use [etransitivity] and [apply] things. *)

(* Given an abstraction function, we can transform the rep of a pickImpl ADT. *)

  Theorem refines_rep_pickImpl
          newRep oldRep
          (abs : newRep -> oldRep)
          MutatorIndex ObserverIndex
          ObserverSpec MutatorSpec :
    refineADT
      (@pickImpl oldRep MutatorIndex ObserverIndex MutatorSpec ObserverSpec)
      (@pickImpl newRep MutatorIndex ObserverIndex
                 (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
                 (fun idx nm => ObserverSpec idx (abs nm))).
  Proof.
    econstructor 1 with (abs := fun nm => Return (abs nm))
                          (mutatorMap := @id MutatorIndex)
                          (observerMap := @id ObserverIndex);
    compute; intros; inversion_by computes_to_inv; subst; eauto.
  Qed.

  (* The weakest reasonable invariant on a new representation is that
     the abstraction of a member satisfies the old invariant. *)
  Definition abs_repInv {newRep oldRep : Type}
             (abs : newRep -> Comp oldRep)
             (repInv : Ensemble oldRep) (nr : newRep) :=
    computational_inv repInv (abs nr).

  Arguments abs_repInv newRep oldRep abs repInv nr / .

  (* Refining the representation type is a valid refinement,
     as long as the new methods are valid refinements and the
     updated the old invariant is preserved by abstraction. *)

  Lemma refineADT_Build_ADT_Rep oldRep newRep
        (abs : newRep -> Comp oldRep)
        (oldRepInv : Ensemble oldRep)
        (newRepInv : Ensemble newRep)
        (absSafe : forall nr, newRepInv nr ->
                              computational_inv oldRepInv (abs nr))
        mutIdx obsIdx :
    (respectful_hetero
       (mutIdx -> mutatorMethodType oldRep)
       (mutIdx -> mutatorMethodType newRep)
       (fun oldMuts => (obsIdx -> observerMethodType oldRep) ->
                 mutatorInv oldRepInv oldMuts -> ADT)
       (fun newMuts => (obsIdx -> observerMethodType newRep) ->
                    mutatorInv (newRepInv) newMuts -> ADT)
       (fun oldMuts newMuts =>
          forall mutIdx,
            @refineMutator oldRep newRep (newRepInv) abs
                           (oldMuts mutIdx)
                           (newMuts mutIdx))
       (fun x y => respectful_hetero
                     (obsIdx -> observerMethodType oldRep)
                     (obsIdx -> observerMethodType newRep)
                     (fun _ => mutatorInv oldRepInv x -> ADT)
                     (fun _ => mutatorInv _ y -> ADT)
                     (fun obs obs' =>
                        forall obsIdx,
                          @refineObserver oldRep newRep (newRepInv) abs
                                         (obs obsIdx)
                                         (obs' obsIdx))
                     (fun obs obs' mInv mInv' =>
                        forall mI mI', refineADT (mInv mI) (mInv' mI'))))
      (@Build_ADT oldRep oldRepInv mutIdx obsIdx)
      (@Build_ADT newRep newRepInv mutIdx obsIdx).
  Proof.
    unfold Proper, respectful_hetero; intros.
    let A := match goal with |- refineADT ?A ?B => constr:(A) end in
    let B := match goal with |- refineADT ?A ?B => constr:(B) end in
    eapply (@refinesADT A B abs id id);
      unfold id, pointwise_relation in *; simpl in *; intros; eauto.
  Qed.

  (* We can always build a default implementation (computation?) for the
     mutators of an ADT with an updated representation using the old
     mutators. *)
  Definition absMutatorMethods oldRep newRep
        (abs : newRep -> Comp oldRep)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep) idx nr n : Comp newRep :=
    (or' <- abs nr;
    {nm | refine (oldMuts idx or' n) (abs nm)})%comp.

  Lemma refine_absMutatorMethods oldRep newRep
        newRepInv
        (abs : newRep -> Comp oldRep)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep)
  : forall idx,
      @refineMutator oldRep newRep newRepInv abs
                     (oldMuts idx)
                     (absMutatorMethods abs oldMuts idx).
  Proof.
    unfold refineMutator, absMutatorMethods, refine; intros.
    inversion_by computes_to_inv; econstructor; eauto.
  Qed.

  (* Always unfold absMutatorMethods. *)
  Global Arguments absMutatorMethods oldRep newRep abs mutIdx oldMuts / idx nr n.

  Hint Resolve refine_absMutatorMethods.

  Lemma absMutatorMethodsInv
        oldRep newRep
        (abs : newRep -> Comp oldRep)
        (oldRepInv : Ensemble oldRep)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep)
  : mutatorInv oldRepInv oldMuts ->
    mutatorInv (abs_repInv abs oldRepInv) (absMutatorMethods abs oldMuts).
  Proof.
    unfold absMutatorMethods, abs_repInv; simpl in *; intros;
    inversion_by computes_to_inv; eauto.
  Qed.

  (* A similar approach works for observers. *)

  Definition absObserverMethods oldRep newRep
        (abs : newRep -> Comp oldRep)
        obsIdx
        (oldObs : obsIdx -> observerMethodType oldRep) idx nr n : Comp nat :=
    (or' <- abs nr;
    {n' | refine (oldObs idx or' n) (ret n')})%comp.

  Lemma refine_absObserverMethods oldRep newRep
        newRepInv
        (abs : newRep -> Comp oldRep)
        obsIdx
        (oldObs : obsIdx -> observerMethodType oldRep)
  : forall idx,
      @refineObserver oldRep newRep newRepInv abs
                     (oldObs idx)
                     (absObserverMethods abs oldObs idx).
  Proof.
    unfold refineObserver, absObserverMethods, refine; intros.
    inversion_by computes_to_inv; econstructor; eauto.
  Qed.

  Global Arguments absObserverMethods oldRep newRep abs obsIdx oldObs / idx nr n .


  Hint Resolve refine_absObserverMethods.

  (* We can refine an ADT using the above default mutator / observer / invariant
     implementations. *)

  Lemma refineADT_Build_ADT_Rep_default oldRep newRep
        (abs : newRep -> Comp oldRep)
        (oldRepInv : Ensemble oldRep)
        mutIdx obsIdx oldMuts oldObs oldInv :
    refineADT
      (@Build_ADT oldRep oldRepInv mutIdx obsIdx oldMuts oldObs oldInv)
      (@Build_ADT newRep (abs_repInv abs oldRepInv) mutIdx obsIdx
                  (absMutatorMethods abs oldMuts)
                  (absObserverMethods abs oldObs)
                  (absMutatorMethodsInv oldInv)).
  Proof.
    eapply refineADT_Build_ADT_Rep; eauto.
  Qed.

(** TODO: Update this to reflect the new definition of ADT + ADT
    Refinement *)

(* If you mutate and then observe, you can do it before or after
    refinement.  I'm not actually sure this isn't obvious.
 *)

(* Lemma ADTRefinementOk
      (old new : ADT)
      (new_initial_value : Comp (Rep new))
      abs mutatorMap observerMap H H'
      (ref : refineADT old new
       := @refinesADT old new abs mutatorMap observerMap H H')
      mutIdx obsIdx n n'
: refine (v0 <- new_initial_value;
          v <- abs v0;
          v' <- MutatorMethods old mutIdx v n;
          ObserverMethods old obsIdx v' n')
         (v <- new_initial_value;
          v' <- MutatorMethods new (mutatorMap mutIdx) v n;
          ObserverMethods new (observerMap obsIdx) v' n').
Proof.
  simpl in *.
  apply refine_bind; [ reflexivity | ].
  intro.
  interleave_autorewrite_refine_monad_with setoid_rewrite_hyp.
Qed. *)

End GeneralRefinements.

  (* Honing tactic for refining the mutator method with the specified index.
     This version of the tactic develops the new mutator body interactively. *)
  Tactic Notation "hone" "mutator" constr(mutIdx) :=
    let A := match goal with |- Sharpened ?A => constr:(A) end in
    let mutIdx_eq' := fresh in
    assert (forall idx idx' : MutatorIndex A, {idx = idx'} + {idx <> idx'})
      as mutIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert ({mutBody | pointwise_relation _ (refineMutator (RepInv A) (@Return (Rep A)))
                                 (MutatorMethods A)
                                 (fun idx => if (mutIdx_eq' idx mutIdx) then
                                               mutBody
                                             else
                                               MutatorMethods A idx)}) as RefineH;
        [eexists _; let mutIdx' := fresh in
         unfold pointwise_relation; intro mutIdx';
         destruct (mutIdx_eq' mutIdx' mutIdx); simpl; intros; autorewrite with refine_monad; simpl;
         [idtac | (* Replaced mutator case left to user*)
          reflexivity] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_Mutators
                         (Rep A) (RepInv A) _ _
                         (ObserverMethods A)
                         (MutatorMethods A)
                         (fun idx => if (mutIdx_eq' idx ()) then
                                       (proj1_sig RefineH)
                                     else
                                       MutatorMethods A idx) (proj2_sig RefineH)
                         (MutatorMethodsInv A)
                         (refineMutatorInv (MutatorMethodsInv A) (proj2_sig RefineH))
                      ); simpl
          | idtac] ]; simpl.

  (* Honing tactic for refining the mutator method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
  Tactic Notation "hone" "mutator" constr(mutIdx) "using" constr(mutBody) :=
    let A := match goal with |- Sharpened ?A => constr:(A) end in
    let mutIdx_eq' := fresh in
    assert (forall idx idx' : MutatorIndex A, {idx = idx'} + {idx <> idx'})
      as mutIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert (pointwise_relation _ (refineMutator (RepInv A) (@Return (Rep A)))
                                 (MutatorMethods A)
                                 (fun idx => if (mutIdx_eq' idx ()) then
                                               mutBody
                                             else
                                               MutatorMethods A idx)) as RefineH;
        [let mutIdx' := fresh in
         unfold pointwise_relation; intro mutIdx';
         destruct (mutIdx_eq' mutIdx' ()); simpl; intros; autorewrite with refine_monad; simpl;
         [idtac | (* Replaced mutator case left to user*)
          reflexivity] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_Mutators
                         (Rep A) (RepInv A) _ _
                         (ObserverMethods A)
                         (MutatorMethods A)
                         (fun idx => if (mutIdx_eq' idx ()) then
                                       mutBody
                                     else
                                       MutatorMethods A idx) RefineH
                         (MutatorMethodsInv A)
                         (refineMutatorInv (MutatorMethodsInv A) RefineH)
                      ); simpl
          | idtac] ]; simpl.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(absf) :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (abs := absf) | idtac].
