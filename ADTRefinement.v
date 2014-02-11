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

Add Parametric Morphism rep repInv mutIdx obsIdx mutInv
  : (fun ms os => @Build_ADT rep repInv mutIdx obsIdx ms os (mutInv ms))
  with signature
  (pointwise_relation _ (@refineMutator _ _ repInv (@Return _)))
    ==> (pointwise_relation _ (@refineObserver _ _ repInv (@Return _)))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B (@Return _) id id);
    unfold id, pointwise_relation in *; simpl in *; intros;
    auto; inversion_by computes_to_inv; subst; eauto.
Qed.

Add Parametric Morphism rep repInv mutIdx obsIdx ms mutInv
  : (fun os => @Build_ADT rep repInv mutIdx obsIdx ms os mutInv)
  with signature
    (pointwise_relation _ (@refineObserver _ _ repInv (@Return _)))
    ==> refineADT
    as refineADT_Build_ADT_observer_only.
Proof.
  intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B (@Return _) id id);
    unfold id, pointwise_relation in *; simpl in *; intros;
    auto; try inversion_by computes_to_inv; subst; eauto;
    autorewrite with refine_monad; reflexivity.
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

Require Import Structures.Equalities.

Section GeneralRefinements.

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
