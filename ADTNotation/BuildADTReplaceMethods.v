Require Export Common Computation ADTSig ADT ADTNotation.ilist
        ADTNotation.BuildADTSig ADTNotation.BuildADT.
Require Import Ensembles StringBound String List.

(* Definitions for replacing method bodies of ADTs built
   from [BuildADT] . *)

Section ReplaceMethods.

  Variable Rep : Type.
  Variable mutSigs : list mutSig.
  Variable obsSigs : list obsSig.
  Variable mutDefs : ilist (@mutDef Rep) mutSigs.
  Variable obsDefs : ilist (@obsDef Rep) obsSigs.

  Definition replaceMutDef
             (idx : string)
             (newDef : mutDef (nth (findIndex mutSig_eq mutSigs idx)
                                   mutSigs ("null" : rep × () → rep)%mutSig))
  : ilist (@mutDef Rep) mutSigs :=
    replace_index mutSig_eq mutDefs idx _ newDef.

  Definition ADTReplaceMutDef
             (idx : string)
             (newDef : mutDef (nth (findIndex mutSig_eq mutSigs idx)
                                   mutSigs ("null" : rep × () → rep)%mutSig))
  : ADT (BuildADTSig mutSigs obsSigs)
    := BuildADT (replaceMutDef idx newDef) obsDefs.

  Definition replaceObsDef
             (idx : string)
             (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx)
                                   obsSigs ("null" : rep × () → ())%obsSig))
  : ilist (@obsDef Rep) obsSigs :=
    replace_index obsSig_eq obsDefs idx _ newDef.

  Definition ADTReplaceObsDef
             (idx : string)
             (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx)
                                   obsSigs ("null" : rep × () → ())%obsSig))
  : ADT (BuildADTSig mutSigs obsSigs)
      := BuildADT mutDefs (replaceObsDef idx newDef).

End ReplaceMethods.

(* Always simplify method replacement when the index and new 
   body are specified. *)

Arguments replaceMutDef [_ _] _ idx%string newDef%mutDef / .
Arguments ADTReplaceMutDef [_ _ _] _ _ idx%string newDef%mutDef / .

Arguments replaceObsDef [_ _] _ idx%string newDef%obsDef / .
Arguments ADTReplaceObsDef [_ _ _] _ _ idx%string newDef%obsDef / .
