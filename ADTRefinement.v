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
      MutatorIndex := mutatorMethodIndex;
      ObserverIndex := observerMethodIndex;
      UnbundledMutatorMethods idx :=
        fun r x =>
          { r' : rep
          | mutatorMethodSpecs idx r x r'}%comp;
      UnbundledObserverMethods idx :=
        fun r n =>
          { n' : nat
          | observerMethodSpecs idx r n n'}%comp
    |}.

End pick.

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

Notation "c ↝ v" := (computes_to c v) (at level 70).

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

Instance refineMutator_refl rep
: Reflexive (@refineMutator rep rep eq).
Proof.
  intro; simpl; intros; subst; econstructor; eauto.
Qed.

Instance refineObserver_refl rep
: Reflexive (@refineObserver rep rep eq).
Proof.
  intro; simpl; intros; subst; reflexivity.
Qed.

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (BiR := eq)
      (mutatorMap := id)
      (observerMap := id);
      unfold id;
      try reflexivity.
  - intros x y z
           [BiR mutMap obsMap mutH obsH]
           [BiR' mutMap' obsMap' mutH' obsH'].
    econstructor 1 with
      (BiR := fun x z => exists y, BiR x y /\ BiR' y z)
        (mutatorMap := mutMap' ∘ mutMap)
        (observerMap := obsMap' ∘ obsMap);
    unfold id, compose; simpl in *; intros.
    + destruct_ex; intuition.
      rewrite <- mutH', <- mutH; eauto.
      intros r_n' Comp_n'; inversion_by computes_to_inv.
      econstructor; eauto.
    + destruct_ex; intuition; rewrite obsH, obsH'; eauto; reflexivity.
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
    intros adt'za refineA SpecA';
    eexists (proj1_sig SpecA'); rewrite refineA; exact (proj2_sig SpecA').
  Defined.

  (* A tactic for finishing a derivation. Probably needs a better name.*)
  Tactic Notation "finish" "sharpening" := eexists; reflexivity.

Section GeneralRefinements.

  (* Refining the representation type is a valid refinement,
     as long as the new methods are valid refinements.

   If we had dependent setoid relations in [Type], then we could write

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
    we'll instead have to use [etransitivity] and [apply] the
    [refineADT_Build_ADT_Rep] lemma to switch representations.

    The statement of [refineADT_Build_ADT_Rep] mimics the notation for
    registering [Parametric Morphism]s so that it will be easy to
    integrate if dependent setoid relations are added.

 **)

  Lemma refineADT_Build_ADT_Rep oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx obsIdx :
    (respectful_hetero
       (mutIdx -> mutatorMethodType oldRep)
       (mutIdx -> mutatorMethodType newRep)
       (fun oldMuts => (obsIdx -> observerMethodType oldRep) -> ADT)
       (fun newMuts => (obsIdx -> observerMethodType newRep) -> ADT)
       (fun oldMuts newMuts =>
          forall mutIdx,
            @refineMutator oldRep newRep BiR
                           (oldMuts mutIdx)
                           (newMuts mutIdx))
       (fun x y => respectful_hetero
                     (obsIdx -> observerMethodType oldRep)
                     (obsIdx -> observerMethodType newRep)
                     (fun _ => ADT)
                     (fun _ => ADT)
                     (fun obs obs' =>
                        forall obsIdx,
                          @refineObserver oldRep newRep BiR
                                         (obs obsIdx)
                                         (obs' obsIdx))
                     (fun obs obs' => refineADT)))
      (@Build_ADT oldRep mutIdx obsIdx)
      (@Build_ADT newRep mutIdx obsIdx).
  Proof.
    unfold Proper, respectful_hetero; intros.
    let A := match goal with |- refineADT ?A ?B => constr:(A) end in
    let B := match goal with |- refineADT ?A ?B => constr:(B) end in
    eapply (@refinesADT A B BiR id id);
      unfold id, pointwise_relation in *; simpl in *; intros; eauto.
  Qed.

  (* Thankfully, we can register a number of different refinements
     which follow from [refineADT_Build_ADT_Rep] as [Parametric Morphism]s.*)

  (* Refining Observers is a valid ADT refinement. *)
  Add Parametric Morphism rep mutIdx obsIdx ms
  : (fun os => @Build_ADT rep mutIdx obsIdx ms os)
      with signature
      (pointwise_relation _ (@refineObserver _ _ eq))
        ==> refineADT
        as refineADT_Build_ADT_Observer.
  Proof.
    intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
  Qed.

  (* Refining Mutators is also a valid ADT refinement. *)

  Add Parametric Morphism rep mutIdx obsIdx obs
  : (fun ms => @Build_ADT rep mutIdx obsIdx ms obs)
      with signature
      (pointwise_relation _ (@refineMutator _ _ eq))
        ==> refineADT
        as refineADT_Build_ADT_Mutators.
  Proof.
    intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
  Qed.

  (* Refining observers and mutators at the same time is also a valid
   refinement. [BD: I've come to the conclusion that smaller refinement
   steps are better, so using the previous refinements should be the
   preferred mode. ]*)

  Add Parametric Morphism rep mutIdx obsIdx
  : (fun ms os => @Build_ADT rep mutIdx obsIdx ms os)
      with signature
      (pointwise_relation _ (@refineMutator _ _ eq))
        ==> (pointwise_relation _ (@refineObserver _ _ eq))
        ==> refineADT
        as refineADT_Build_ADT_Both.
  Proof.
    intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
  Qed.

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
    econstructor 1 with (BiR := fun om nm => om = (abs nm))
                          (mutatorMap := @id MutatorIndex)
                          (observerMap := @id ObserverIndex);
    compute; intros;
    [inversion_by computes_to_inv; subst; eauto
     | inversion_by computes_to_inv; subst; eauto].
  Qed.

  (* We can always build a default implementation (computation?) for the
     mutators of an ADT with an updated representation using the old
     mutators. *)
  Definition absMutatorMethods oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep) idx nr n : Comp newRep :=
    {nr' | forall or,
             BiR or nr ->
             exists or',
               (oldMuts idx or n) ↝ or' /\
               BiR or' nr'}%comp.

  Lemma refine_absMutatorMethods oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep)
  : forall idx,
      @refineMutator oldRep newRep BiR
                     (oldMuts idx)
                     (absMutatorMethods BiR oldMuts idx).
  Proof.
    unfold refineMutator, absMutatorMethods, refine; intros.
    inversion_by computes_to_inv.
    destruct (H0 _ H) as [or' [Comp_or BiR_or''] ].
    econstructor; eauto.
  Qed.

  (* Always unfold absMutatorMethods. *)
  Global Arguments absMutatorMethods oldRep newRep BiR mutIdx oldMuts / idx nr n.

  Hint Resolve refine_absMutatorMethods.

  (* A similar approach works for observers. *)

  Definition absObserverMethods oldRep newRep
             (BiR : oldRep -> newRep -> Prop)
             obsIdx
             (oldObs : obsIdx -> observerMethodType oldRep) idx nr n : Comp nat :=
    {n' | forall or,
            BiR or nr ->
            (oldObs idx or n) ↝ n'}%comp.

  Lemma refine_absObserverMethods oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        obsIdx
        (oldObs : obsIdx -> observerMethodType oldRep)
  : forall idx,
      @refineObserver oldRep newRep BiR (oldObs idx)
                     (absObserverMethods BiR oldObs idx).
  Proof.
    unfold refineObserver, absObserverMethods, refine; intros.
    inversion_by computes_to_inv; eauto.
  Qed.

  Global Arguments absObserverMethods oldRep newRep BiR obsIdx oldObs / idx nr n .

  Hint Resolve refine_absObserverMethods.

  (* We can refine an ADT using the above default mutator and observer
     implementations. *)

  Lemma refineADT_Build_ADT_Rep_default oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx obsIdx oldMuts oldObs :
    refineADT
      (@Build_ADT oldRep mutIdx obsIdx oldMuts oldObs)
      (@Build_ADT newRep mutIdx obsIdx
                  (absMutatorMethods BiR oldMuts)
                  (absObserverMethods BiR oldObs)).
  Proof.
    eapply refineADT_Build_ADT_Rep; eauto.
  Qed.

  Section SimplifyRep.

  (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)

    Variable oldRep : Type.
    Variable newRep : Type.

    Variable simplifyf : oldRep -> newRep.
    Variable concretize : newRep -> oldRep.
    Variable BiR : oldRep -> newRep -> Prop.

    Notation "ro ≃ rn" := (BiR ro rn) (at level 70).

    Definition simplifyMutatorMethods
               mutIdx (oldMuts : mutIdx -> mutatorMethodType oldRep)
               idx r_n n : Comp newRep :=
      (r_o' <- (oldMuts idx (concretize r_n) n);
       ret (simplifyf r_o'))%comp.

  Definition simplifyObserverMethods
             obsIdx (oldObs : obsIdx -> observerMethodType oldRep)
             idx nr n : Comp nat :=
    oldObs idx (concretize nr) n.

  Definition simplifyRep
             mutIdx obsIdx oldMuts oldObs :
    (forall r_n r_o,
                (r_o ≃ r_n) ->
                forall idx n,
                  refineEquiv (r_o'' <- oldMuts idx r_o n;
                              {r_n' | r_o'' ≃ r_n'})
                              (r_o'' <- oldMuts idx (concretize r_n) n;
                              ret (simplifyf r_o''))) ->
    (forall r_n r_o,
                (r_o ≃ r_n) ->
                forall idx n,
                  refineEquiv (oldObs idx r_o n)
                              (oldObs idx (concretize r_n) n)) ->
    refineADT
      (@Build_ADT oldRep mutIdx obsIdx oldMuts oldObs)
      (@Build_ADT newRep mutIdx obsIdx
                  (simplifyMutatorMethods oldMuts)
                  (simplifyObserverMethods oldObs)).
  Proof.
    econstructor 1 with
    (BiR := BiR)
      (mutatorMap := @id mutIdx)
      (observerMap := @id obsIdx); simpl; eauto.
    - unfold simplifyMutatorMethods; intros; eapply H; eauto.
    - unfold simplifyObserverMethods; intros; eapply H0; eauto.
  Qed.

  End SimplifyRep.

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

(* Goals with [refine] nested in a [pick] crop up when
   switching representations; this simplifies them to
   what is expected. *)
Lemma refine_pick_refine (A B : Type) f P :
  refine {a : A | refine {b : B | P b} (ret (f a))} {a : A | P (f a)}.
Proof.
  intros Ra v; constructor; intros v' Rb.
  apply computes_to_inv in Rb; subst.
  inversion_by computes_to_inv; econstructor; eauto.
Qed.

Hint Rewrite refine_pick_refine : refine_monad.

(* Honing tactic for refining the observer method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
Tactic Notation "hone" "observer" constr(obsIdx) "using" constr(obsBody) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex A) in
    let ObserverIndex' := eval simpl in (ObserverIndex A) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
      assert (forall idx idx' : ObserverIndex', {idx = idx'} + {idx <> idx'})
        as obsIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert (pointwise_relation ObserverIndex' (refineObserver (@eq Rep'))
                                 (ObserverMethods')
                                 (fun idx => if (obsIdx_eq' idx ()) then
                                               obsBody
                                             else
                                               ObserverMethods' idx)) as RefineH;
        [let obsIdx' := fresh in
         unfold pointwise_relation; intro obsIdx';
         destruct (obsIdx_eq' obsIdx' ()); simpl; intros; simpl;
         [idtac | (* Replaced mutator case left to user*)
          subst; reflexivity] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_Observer
                         Rep' ObserverIndex' MutatorIndex'
                         MutatorMethods'
                         ObserverMethods'
                         (fun idx => if (obsIdx_eq' idx ()) then
                                       obsBody
                                     else
                                       ObserverMethods' idx) RefineH)
          | idtac] ]; cbv beta in *; simpl in *.

  (* Honing tactic for refining the mutator method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
  Tactic Notation "hone" "mutator" constr(mutIdx) "using" constr(mutBody) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex A) in
    let ObserverIndex' := eval simpl in (ObserverIndex A) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
      assert (forall idx idx' : MutatorIndex', {idx = idx'} + {idx <> idx'})
        as mutIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert (pointwise_relation MutatorIndex' (refineMutator (@eq Rep'))
                                 (MutatorMethods')
                                 (fun idx => if (mutIdx_eq' idx ()) then
                                               mutBody
                                             else
                                               MutatorMethods' idx)) as RefineH;
        [let mutIdx' := fresh in
         unfold pointwise_relation; intro mutIdx';
         destruct (mutIdx_eq' mutIdx' ()); simpl; intros;
         setoid_rewrite refineEquiv_pick_eq'; autorewrite with refine_monad; simpl;
         [idtac | (* Replaced mutator case left to user*)
          subst; reflexivity] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_Mutators
                         Rep' ObserverIndex' MutatorIndex'
                         ObserverMethods'
                         MutatorMethods'
                         (fun idx => if (mutIdx_eq' idx ()) then
                                       mutBody
                                     else
                                       MutatorMethods' idx) RefineH)
          | idtac] ]; cbv beta in *; simpl in *.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(BiSR) :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (BiR := BiSR) | idtac].
