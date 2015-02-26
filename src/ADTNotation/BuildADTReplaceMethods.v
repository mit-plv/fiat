Require Import ADTSynthesis.Common Coq.Lists.List Coq.Strings.String
        ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist
        ADTSynthesis.ADTNotation.BuildADTSig ADTSynthesis.ADTNotation.BuildADT.

(* Definitions for replacing method bodies of ADTs built
   from [BuildADT] . *)

Section ReplaceMethods.

  Variable Rep : Type.
  Variable consSigs : list consSig.
  Variable methSigs : list methSig.
  Variable consDefs : ilist (@consDef Rep) consSigs.
  Variable methDefs : ilist (@methDef Rep) methSigs.

  Program Definition replaceConsDef
             (idx : @BoundedString (map consID consSigs))
             (newDef : consDef (nth_Bounded consID consSigs idx))
  : ilist (@consDef Rep) consSigs :=
    replace_BoundedIndex _ consDefs idx newDef.

  Definition ADTReplaceConsDef
             (idx : @BoundedString (map consID consSigs))
             (newDef : consDef (nth_Bounded consID consSigs idx))
  : ADT (BuildADTSig consSigs methSigs)
    := BuildADT (replaceConsDef idx newDef) methDefs.

  Definition replaceMethDef
             (idx : @BoundedString (map methID methSigs))
             (newDef : methDef (nth_Bounded methID methSigs idx))
  : ilist (@methDef Rep) methSigs :=
    replace_BoundedIndex _ methDefs idx newDef.

  Definition ADTReplaceMethDef
             (idx : @BoundedString (map methID methSigs))
             (newDef : methDef (nth_Bounded methID methSigs idx))
  : ADT (BuildADTSig consSigs methSigs)
    := BuildADT consDefs (replaceMethDef idx newDef).

End ReplaceMethods.

(* Always simplify method replacement when the index and new
   body are specified. *)

Arguments replaceConsDef [_ _] _ idx%string newDef%consDef / .
Arguments ADTReplaceConsDef [_ _ _] _ _ idx%string newDef%consDef / .

Arguments replaceMethDef [_ _] _ idx%string newDef%methDef / .
Arguments ADTReplaceMethDef [_ _ _] _ _ idx%string newDef%methDef / .
