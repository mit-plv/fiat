Require Import Coq.Lists.List
        Coq.Strings.String
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.Common
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.ADTNotation.BuildADTSig
        Fiat.ADTNotation.BuildADT.

(* Definitions for replacing method bodies of ADTs built
   from [BuildADT] . *)

Section ReplaceMethods.

  Variable Rep : Type.
  Context {n' : nat}.
  Variable methSigs : Vector.t methSig n'.
  Variable methDefs : ilist (B := @methDef Rep) methSigs.

  Definition replaceMethDef
             (idx : Fin.t n')
             (newDef : methDef (Vector.nth methSigs idx))
  : ilist (B:= @methDef Rep) methSigs :=
    replace_Index _ methDefs idx newDef.

  Definition ADTReplaceMethDef
             (idx : Fin.t n')
             (newDef : methDef (Vector.nth methSigs idx))
  : ADT (BuildADTSig methSigs)
    := BuildADT (replaceMethDef idx newDef).

End ReplaceMethods.

(* Always simplify method replacement when the index and new
   body are specified. *)

Arguments replaceMethDef [_ _ _] _ idx%string newDef%methDef / .
Arguments ADTReplaceMethDef [_ _ _] _ idx%string newDef%methDef / .
