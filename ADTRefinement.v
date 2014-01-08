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

Inductive refineADT : ADT -> ADT -> Prop := 
  | refinesADT : 
      forall oldModel newModel 
             (*  Relationship between old and new (at least as concrete) model *)
             (RepInv : oldModel -> newModel -> Prop) 
             mutatorMethodIndex observerMethodIndex
             (* Assumes indices are the same, we alternatively establish 
              that there is an injection from old indices to new indices. *)
             (oldMutatorMethods : mutatorMethodIndex -> mutatorMethodType oldModel)
             (newMutatorMethods : mutatorMethodIndex -> mutatorMethodType newModel)
             (oldObserverMethods : observerMethodIndex -> observerMethodType oldModel)
             (newObserverMethods : observerMethodIndex -> observerMethodType newModel),
        (* Need to specify that each mutator is a refinement 
           This should correspond to lifting [RepInv] to [Comp].
        (forall idx om nm n a, 
           RepInv om nm -> 
           refine (newMutatorMethods idx nm n) (oldMutatorMethods idx om n)) -> *)
        (* Each observer is a refinement *)
        (forall idx om nm n, 
           RepInv om nm -> 
           refine (newObserverMethods idx nm n) (oldObserverMethods idx om n)) -> 
        refineADT (Build_ADT newMutatorMethods newObserverMethods)
                  (Build_ADT oldMutatorMethods oldObserverMethods).
