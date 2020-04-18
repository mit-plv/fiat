Require Import Fiat.Common Fiat.Computation.Core Fiat.ADT.Core Coq.Sets.Ensembles.

Section HideADT.

  Context {extSig : ADTSig}.
  (* The extended signature *)

  Context {resConstructorIndex : Type}.
  (* The restricted set of constructor indices *)

  Context {resMethodIndex : Type}.
  (* The restricted set of method indices *)

  Variable constructorMap : resConstructorIndex -> ConstructorIndex extSig.
  (* Map from restricted to extended constructor indices *)

  Variable methodMap : resMethodIndex -> MethodIndex extSig.
  (* Map from restricted to extended method indices *)

  Definition resSig :=
    {| ConstructorIndex := resConstructorIndex;
       MethodIndex := resMethodIndex;
       ConstructorDom idx := ConstructorDom extSig (constructorMap idx);
       MethodDomCod idx := MethodDomCod extSig (methodMap idx)
    |}.
  (* The signature of the ADT with restricted constructor and method indices *)

  Definition HideADT (extADT : ADT extSig) : ADT resSig :=
    match extADT with
        {| Rep := rep;
           Constructors := extConstructors;
           Methods := extMethods
        |} =>
        Build_ADT resSig
          (fun idx => extConstructors (constructorMap idx))
          (fun idx => extMethods (methodMap idx))
    end.

End HideADT.
