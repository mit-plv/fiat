Require Export Common Computation ADTSig ADT ADTNotation.ilist
        ADTNotation.BuildADTSig ADTNotation.BuildADT.
Require Import Ensembles ADTNotation.StringBound String List.

(* Definitions for replacing method bodies of ADTs built
   from [BuildADT] . *)

Section ReplaceMethods.

  Variable Rep : Type.
  Variable mutSigs : list mutSig.
  Variable obsSigs : list obsSig.
  Variable mutDefs : ilist (@mutDef Rep) mutSigs.
  Variable obsDefs : ilist (@obsDef Rep) obsSigs.

  Program Definition replaceMutDef
             (idx : BoundedString (map mutID mutSigs))
             (newDef : mutDef (nth_Bounded mutID mutSigs idx))
  : ilist (@mutDef Rep) mutSigs :=
    replace_BoundedIndex _ mutDefs idx newDef.

  Definition ADTReplaceMutDef
             (idx : BoundedString (map mutID mutSigs))
             (newDef : mutDef (nth_Bounded mutID mutSigs idx))
  : ADT (BuildADTSig mutSigs obsSigs)
    := BuildADT (replaceMutDef idx newDef) obsDefs.

  Definition replaceObsDef
             (idx : BoundedString (map obsID obsSigs))
             (newDef : obsDef (nth_Bounded obsID obsSigs idx))
  : ilist (@obsDef Rep) obsSigs :=
    replace_BoundedIndex _ obsDefs idx newDef.

  Definition ADTReplaceObsDef
             (idx : BoundedString (map obsID obsSigs))
             (newDef : obsDef (nth_Bounded obsID obsSigs idx))
  : ADT (BuildADTSig mutSigs obsSigs)
    := BuildADT mutDefs (replaceObsDef idx newDef).

End ReplaceMethods.

(* Always simplify method replacement when the index and new
   body are specified. *)

Arguments replaceMutDef [_ _] _ idx%string newDef%mutDef / .
Arguments ADTReplaceMutDef [_ _ _] _ _ idx%string newDef%mutDef / .

Arguments replaceObsDef [_ _] _ idx%string newDef%obsDef / .
Arguments ADTReplaceObsDef [_ _ _] _ _ idx%string newDef%obsDef / .
