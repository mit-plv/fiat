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

Section ADTRefinement.

  Variables (oldModel newModel : Type). (* Old and new model *)
  Variable absNewModel : newModel -> oldModel -> Prop.  
  (* Abstraction relation from new to old models *)
  (* Intuitively, there should be an injection (abstraction function) 
     from new to old models, but we'll omit that for now. *)

  (* Assumes indices are the same, we alternatively establish 
    that there is an injection from old indices to new indices. *)

  Variable observerMethodIndex : Type. (* Observer Method Index Type *)
  Variable mutatorMethodIndex : Type. (* Mutator Method Index Type *)

  Variable oldObserverMethods : observerMethodIndex -> observerMethodType oldModel.
  Variable newObserverMethods : observerMethodIndex -> observerMethodType newModel.
  Variable oldMutatorMethods : mutatorMethodIndex -> mutatorMethodType oldModel.
  Variable newMutatorMethods : mutatorMethodIndex -> mutatorMethodType newModel.

  (* Refinement of an observer method *)
  Definition refineObserver 
             (newObserver : observerMethodType newModel) 
             (oldObserver : observerMethodType oldModel) :=
      forall nm om n, 
        absNewModel nm om -> 
        refine (newObserver nm n) (oldObserver om n).
  
  (* Refinement of a mutator method *)
  Definition refineMutator 
             (newMutator : mutatorMethodType newModel)
             (oldMutator : mutatorMethodType oldModel) :=
    forall nm om n, 
      absNewModel nm om -> 
      forall nm', 
        computes_to (newMutator nm n) nm' -> (* For any mutated new model *)
        exists om',                           
          computes_to (oldMutator om n) om' /\ (* There exists a mutated old model *)
          absNewModel nm' om'.  (* which is a valid abstraction of the mutated new model *)
  
  Inductive refineADT : ADT -> ADT -> Prop := 
  | refinesADT : 
      (forall idx, refineObserver (newObserverMethods idx) (oldObserverMethods idx)) -> 
      (forall idx, refineMutator (newMutatorMethods idx) (oldMutatorMethods idx)) -> 
      refineADT (Build_ADT newMutatorMethods newObserverMethods)
                (Build_ADT oldMutatorMethods oldObserverMethods).

End ADTRefinement.
