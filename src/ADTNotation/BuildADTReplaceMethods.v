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
  Context {n n' : nat}.
  Variable consSigs : Vector.t consSig n.
  Variable methSigs : Vector.t methSig n'.
  Variable consDefs : ilist (B := @consDef Rep) consSigs.
  Variable methDefs : ilist (B := @methDef Rep) methSigs.

  Program Definition replaceConsDef
             (idx : Fin.t n)
             (newDef : consDef (Vector.nth consSigs idx))
  : ilist (B := @consDef Rep) consSigs :=
    replace_Index _ consDefs idx newDef.

  Definition ADTReplaceConsDef
             (idx : Fin.t n)
             (newDef : consDef (Vector.nth consSigs idx))
  : ADT (BuildADTSig consSigs methSigs)
    := BuildADT _ _ _ (replaceConsDef idx newDef) methDefs.

  Definition replaceMethDef
             (idx : Fin.t n')
             (newDef : methDef (Vector.nth methSigs idx))
  : ilist (B:= @methDef Rep) methSigs :=
    replace_Index _ methDefs idx newDef.

  Definition ADTReplaceMethDef
             (idx : Fin.t n')
             (newDef : methDef (Vector.nth methSigs idx))
  : ADT (BuildADTSig consSigs methSigs)
    := BuildADT _ _ _ consDefs (replaceMethDef idx newDef).

End ReplaceMethods.

(* Always simplify method replacement when the index and new
   body are specified. *)

Arguments replaceConsDef [_ _ _] _ idx%string newDef%consDef / .
Arguments ADTReplaceConsDef [_ _ _ _ _] _ _ idx%string newDef%consDef / .

Arguments replaceMethDef [_ _ _] _ idx%string newDef%methDef / .
Arguments ADTReplaceMethDef [_ _ _ _ _] _ _ idx%string newDef%methDef / .
