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

  Variables (oldModel newModel : Type). (* Old and new model *)
  Variable absNewModel : newModel -> oldModel -> Prop.  
  (* Abstraction relation from new to old models *)
  
  Variable abs : newModel -> oldModel. (* Abstraction function *)
  Variable absValid : forall nm, absNewModel nm (abs nm). 

  (* Refinement of an observer method *)
  Definition refineObserver 
             (newObserver : observerMethodType newModel) 
             (oldObserver : observerMethodType oldModel) :=
      forall nm om n, 
        absNewModel nm om -> 
        refine (oldObserver om n) (newObserver nm n).
  
  (* Refinement of a mutator method *)
  Definition refineMutator 
             (newMutator : mutatorMethodType newModel)
             (oldMutator : mutatorMethodType oldModel) :=
    forall nm om n, 
      absNewModel nm om -> 
      forall nm', 
        computes_to (newMutator nm n) nm' -> (* For any new mutated state *)
          computes_to (oldMutator om n) (abs nm'). 
  
End MethodRefinement.

Inductive refineADT : ADT -> ADT -> Prop := 
| refinesADT : 
    forall (oldModel newModel : Type)
           (absNewModel : newModel -> oldModel -> Prop)
           (abs : newModel -> oldModel) (* Abstraction function *)
           (absValid : forall nm, absNewModel nm (abs nm)) (* absNewModel is left-total *)
           (oldObserverMethodIndex : Type) (* Old Observer Method Index Type *)
           (newObserverMethodIndex : Type) (* New Observer Method Index Type 
                                             (In order to add new observers) *)
           (mapObserverIndex : oldObserverMethodIndex -> newObserverMethodIndex)
           (* Map from old indices to new ones *)
           (oldMutatorMethodIndex : Type) (* Old Mutator Method Index Type *)
           (newMutatorMethodIndex : Type) (* New Mutator Method Index Type 
                                           (In order to add new mutators) *)
           (mapMutatorIndex : oldMutatorMethodIndex -> newMutatorMethodIndex)
           (* Map from old indices to new ones *)
           (oldObserverMethods : oldObserverMethodIndex -> observerMethodType oldModel)
           (newObserverMethods : newObserverMethodIndex -> observerMethodType newModel)
           (oldMutatorMethods : oldMutatorMethodIndex -> mutatorMethodType oldModel)
           (newMutatorMethods : newMutatorMethodIndex -> mutatorMethodType newModel),
      (forall idx idx', mapObserverIndex idx = mapObserverIndex idx' -> idx = idx') -> (* mapObserverIndex is injective *)
      (forall idx idx', mapMutatorIndex idx = mapMutatorIndex idx' -> idx = idx') -> (* mapObserverIndex is injective *)
      (forall idx, refineObserver absNewModel (newObserverMethods (mapObserverIndex idx)) (oldObserverMethods idx)) -> 
      (forall idx, refineMutator absNewModel abs (newMutatorMethods (mapMutatorIndex idx)) (oldMutatorMethods idx)) -> 
      refineADT (Build_ADT newMutatorMethods newObserverMethods)
                (Build_ADT oldMutatorMethods oldObserverMethods).

Theorem refineADT_inv old new :
  refineADT new old -> 
  match old with 
    | {| Model := m;
         MutatorIndex := mdx;
         ObserverIndex := odx;
         MutatorMethods := mutators;
         ObserverMethods := observers |} => 
      exists (absNewModel : Model new -> m -> Prop)
             (abs : Model new -> m)
             (mapObserverIndex : odx -> ObserverIndex new)
             (mapMutatorIndex : mdx -> MutatorIndex new),
        (forall nm, absNewModel nm (abs nm)) /\
        (forall idx idx', mapObserverIndex idx = mapObserverIndex idx' -> idx = idx') /\
      (forall idx idx', mapMutatorIndex idx = mapMutatorIndex idx' -> idx = idx') /\
        (forall idx, refineObserver absNewModel (ObserverMethods new (mapObserverIndex idx)) (observers idx)) /\
        (forall idx, refineMutator absNewModel abs (MutatorMethods new (mapMutatorIndex idx)) (mutators idx))
        
  end.
Proof.
  destruct 1; simpl; eauto 10.
Qed.

Section PreOrders.

  Variables (oldModel newModel : Type). (* Old and new model *)
  Variable absNewModel : newModel -> oldModel -> Prop.  
  Variable abs : newModel -> oldModel.
  Variable absValid : forall nm, absNewModel nm (abs nm).
  Variable observerMethodIndex : Type. (* Observer Method Index Type *)
  Variable mutatorMethodIndex : Type. (* Mutator Method Index Type *)
  Variable oldObserverMethods : observerMethodIndex -> observerMethodType oldModel.
  Variable newObserverMethods : observerMethodIndex -> observerMethodType newModel.
  Variable oldMutatorMethods : mutatorMethodIndex -> mutatorMethodType oldModel.
  Variable newMutatorMethods : mutatorMethodIndex -> mutatorMethodType newModel.

  Global Instance refineObserver_PreOrder Model : 
    PreOrder (refineObserver (@eq Model)).
  Proof.
    split; compute in *; intros; subst; eauto.
  Qed.

  Add Parametric Relation Model : _ (refineObserver (@eq Model)) 
      reflexivity proved by reflexivity
      transitivity proved by transitivity
    as refineObserver_rel.

  Global Instance refineMutator_PreOrder Model : 
    PreOrder (refineMutator (@eq Model) id).
  Proof.
    split; compute in *; intros; subst; eauto.
  Qed.

  Add Parametric Relation Model : _ (refineObserver (@eq Model)) 
      reflexivity proved by reflexivity
      transitivity proved by transitivity
    as refineMutator_rel.

  Global Instance refineADT_PreOrder
  : PreOrder refineADT.
  Proof.
    split; compute in *.
    intros; destruct x; econstructor 1 with 
                        (absNewModel := @eq _)
                          (mapObserverIndex := id)
                          (mapMutatorIndex := id)
                          (abs := id); eauto; reflexivity.
    intros x y z Rxy Ryz; destruct Rxy.    
    destruct z; inversion_by refineADT_inv.
    econstructor 1 with (absNewModel := fun x' z => x (abs0 x') z)
                          (mapMutatorIndex := compose mapMutatorIndex x2)
                          (mapObserverIndex := compose mapObserverIndex x1)
                          (abs := compose x0 abs0); 
      eauto; compute in *; eauto.
  Qed.

End PreOrders.
