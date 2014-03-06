Require Import Common Computation ADT Ensembles.

Section HideADT.

  Context {extSig : ADTSig}.
  (* The extended signature *)

  Context {resMutatorIndex : Type}.
  (* The restricted set of mutator indices *)

  Context {resObserverIndex : Type}.
  (* The restricted set of observer indices *)

  Variable MutatorMap : resMutatorIndex -> MutatorIndex extSig.
  (* Map from restricted to extended mutator indices *)

  Variable ObserverMap : resObserverIndex -> ObserverIndex extSig.
  (* Map from restricted to extended observer indices *)

  Definition resSig :=
    {| MutatorIndex := resMutatorIndex;
       ObserverIndex := resObserverIndex;
       MutatorDom idx := MutatorDom extSig (MutatorMap idx);
       ObserverDom idx := ObserverDom extSig (ObserverMap idx);
       ObserverCod idx := ObserverCod extSig (ObserverMap idx)
    |}.
  (* The signature of the ADT with restricted mutator and observer indices *)


  Definition HideADT (extADT : ADT extSig) : ADT resSig :=
    match extADT with
        {| Rep := Rep;
           MutatorMethods := extMutatorMethods;
           ObserverMethods := extObserverMethods
        |} =>
        Build_ADT resSig
          (fun idx => extMutatorMethods (MutatorMap idx))
          (fun idx => extObserverMethods (ObserverMap idx))
    end.

End HideADT.
