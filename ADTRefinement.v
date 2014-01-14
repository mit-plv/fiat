Require Import Common Computation ADT.

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
  Variable model : Type.
  Variable mutatorMethodIndex : Type.
  Variable observerMethodIndex : Type.
  Variable mutatorMethodSpecs : mutatorMethodIndex -> mutatorMethodSpec model.
  Variable observerMethodSpecs : observerMethodIndex -> observerMethodSpec model.

  Definition pickImpl : ADT :=
    {|
      Model := model;
      MutatorIndex := mutatorMethodIndex;
      ObserverIndex := observerMethodIndex;
      MutatorMethods idx :=
        fun m x =>
          { m' : model
          | mutatorMethodSpecs idx m x m'}%comp;
      ObserverMethods idx :=
        fun m n =>
          { n' : nat
          | observerMethodSpecs idx m n n'}%comp
    |}.
End pick.

Section MethodRefinement.
  Variables oldModel newModel : Type.

  Variable abs : newModel -> Comp oldModel.
  (** Abstraction function *)

  (** Refinement of a mutator method: if we first do the new
      computation and then abstract, this is a refinement of first
      abstracting and then doing the old computation.  That is, the
      following diagram commutes:
<<
                   old mutator
       old model --------------> old model
          ↑                         ↑
      abs |                         | abs
          |                         |
       new model --------------> new model
                   new mutator
>>  *)
  Definition refineMutator
             (oldMutator : mutatorMethodType oldModel)
             (newMutator : mutatorMethodType newModel)
    := forall new_state n,
         refine (old_state <- abs new_state;
                 oldMutator old_state n)
                (new_state' <- newMutator new_state n;
                 abs new_state').

  (** Refinement of an observer method: the new computation should be
      a refinement of first abstracting and then doing the old
      computation.  That is, the following diagram should commute:
<<
                  old observer
       old model --------------> ℕ
          ↑                      ∥
      abs |                      ∥ id
          |                      ∥
       new model --------------> ℕ
                  new observer
>>
   *)
  Definition refineObserver
             (oldObserver : observerMethodType oldModel)
             (newObserver : observerMethodType newModel)
    := forall new_state n,
         refine (old_state <- abs new_state;
                 oldObserver old_state n)
                (newObserver new_state n).
End MethodRefinement.

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)
Inductive refineADT (A B : ADT) : Prop :=
| refinesADT :
    forall abs mutatorMap observerMap,
      (forall idx, @refineMutator
                     (Model A) (Model B) abs
                     (MutatorMethods A idx)
                     (MutatorMethods B (mutatorMap idx)))
      -> (forall idx, @refineObserver
                     (Model A) (Model B) abs
                     (ObserverMethods A idx)
                     (ObserverMethods B (observerMap idx)))
      -> refineADT A B.

(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (abs := @Return _)
      (mutatorMap := id)
      (observerMap := id);
      unfold id; simpl; intros;
      autorewrite with refine_monad;
      reflexivity.
  - intros x y z
           [abs mutMap obsMap mutH obsH]
           [abs' mutMap' obsMap' mutH' obsH'].
    econstructor 1 with
    (abs := fun z => (z' <- abs' z; abs z')%comp)
    (mutatorMap := mutMap' ∘ mutMap)
    (observerMap := obsMap' ∘ obsMap);
    unfold id, compose; simpl in *; intros;
    interleave_autorewrite_refine_monad_with setoid_rewrite_hyp.
Qed.

Add Parametric Relation : ADT refineADT
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refineADT_rel.

Add Parametric Morphism model mutIdx obsIdx : (@Build_ADT model mutIdx obsIdx)
  with signature
  (pointwise_relation _ (@refineMutator _ _ (@Return _)))
    ==> (pointwise_relation _ (@refineObserver _ _ (@Return _)))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B (@Return _) id id);
    unfold id, pointwise_relation in *; simpl in *; intros;
    auto.
Qed.

(* Given an abstraction function, we can transform the model of a pickImpl ADT. *)

Theorem refines_model_pickImpl
        newModel oldModel
        (abs : newModel -> oldModel)
        MutatorIndex ObserverIndex
        ObserverSpec MutatorSpec : 
  refineADT 
    (@pickImpl oldModel MutatorIndex ObserverIndex MutatorSpec ObserverSpec)
    (@pickImpl newModel MutatorIndex ObserverIndex 
               (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
               (fun idx nm => ObserverSpec idx (abs nm))).
Proof.
  econstructor 1 with (abs := fun nm => Return (abs nm))
                        (mutatorMap := @id MutatorIndex)
                        (observerMap := @id ObserverIndex);
  compute; intros; inversion_by computes_to_inv; subst; eauto.
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
    machinery won't work very well when we're switching models, and
    we'll instead have to use [etransitivity] and [apply] things. *)

(** If you mutate and then observe, you can do it before or after
    refinement.  I'm not actually sure this isn't obvious.  *)

Lemma ADTRefinementOk
      (old new : ADT)
      (new_initial_value : Comp (Model new))
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
Qed.
