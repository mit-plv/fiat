Require Import Fiat.Common Fiat.Computation.Core Fiat.ADT.Core Coq.Sets.Ensembles.

Section HideADT.

  Context {extSig : ADTSig}.
  (* The extended signature *)

  Context {resMethodIndex : Type}.
  (* The restricted set of method indices *)

  Variable methodMap : resMethodIndex -> MethodIndex extSig.
  (* Map from restricted to extended method indices *)

  Definition resSig :=
    {| MethodIndex := resMethodIndex;
       MethodDomCod idx := MethodDomCod extSig (methodMap idx)
    |}.
  (* The signature of the ADT with restricted constructor and method indices *)

  Definition HideADT (extADT : ADT extSig) : ADT resSig :=
    match extADT with
        {| Rep := rep;
           Methods := extMethods
        |} =>
        Build_ADT resSig rep
                  (fun idx => extMethods (methodMap idx))
    end.

End HideADT.
