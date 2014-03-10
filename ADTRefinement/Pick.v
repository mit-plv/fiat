Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Specs.

Generalizable All Variables.
Set Implicit Arguments.

(** Every spec is trivially implementable using [Pick]. *)
Section pick.
  
  Variable Sig : ADTSig.
  Variable rep : Type.

  Variable mutatorMethodSpecs : 
    forall idx, mutatorMethodSpec rep (MutatorDom Sig idx).
  Variable observerMethodSpecs : 
    forall idx, observerMethodSpec rep (fst (ObserverDomCod Sig idx)) (snd (ObserverDomCod Sig idx)).

  Local Obligation Tactic := econstructor; eauto.

  Program Definition pickImpl : ADT Sig :=
    {|
      Rep := rep;
      MutatorMethods idx :=
        fun r x =>
          { r' : rep
          | mutatorMethodSpecs idx r x r'}%comp;
      ObserverMethods idx :=
        fun r n =>
          { n' : snd (ObserverDomCod Sig idx) 
          | observerMethodSpecs idx r n n'}%comp
    |}.

End pick.
