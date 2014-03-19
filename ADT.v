Require Export Common Computation ADTSig ilist.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** * Basic ADT definitions *)

(** Interface of an ADT *)
Record ADT (Sig : ADTSig) :=
  {
    Rep : Type;
    (** The representation type of the ADT **)

    MutatorMethods :
      forall idx : MutatorIndex Sig,
        mutatorMethodType Rep (MutatorDom Sig idx);
    (** Mutator method implementations *)

    ObserverMethods :
      forall idx : ObserverIndex Sig,
        observerMethodType Rep (fst (ObserverDomCod Sig idx))
                           (snd (ObserverDomCod Sig idx))
    (** Observer method implementations *)

  }.

Bind Scope ADT_Scope with ADT.
Delimit Scope ADT_scope with ADT.

(* Some notations for ADT Signatures. *)

Require Import List String.

Record mutDef {Rep : Type} (Sig : mutSig) :=
  { mutBody : mutatorMethodType Rep (mutDom Sig) }.

Notation "'def' id `[ r `: 'rep' , x `: dom ]` : 'rep' := bod" :=
  (Build_mutDef {| mutID := id; mutDom := dom |} (fun r x => bod))
    (at level 70, format "'def'  id  `[ r  `:  'rep' ,  x  `:  dom ]`  :  'rep'  :=  '[v'   bod ']' " ) :
mutDef_scope.

Bind Scope mutDef_scope with mutDef.
Delimit Scope mutDef_scope with mutDef.

Definition insertDef :=
  (def "Insert" `[ r `: rep , n `: unit ]` : rep := ret (plus r 0))%mutDef.

Record obsDef {Rep : Type} (Sig : obsSig) :=
  { obsBody : observerMethodType Rep (obsDom Sig) (obsCod Sig)}.

Notation "'def' id `[ r `: 'rep' , x `: dom ]` : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |} (fun r x => bod))
    (at level 70, format "'def'  id  `[ r  `:  'rep' ,  x  `:  dom ]`  :  cod  :=  '[v'   bod ']' " ) :
obsDef_scope.

Bind Scope obsDef_scope with obsDef.
Delimit Scope obsDef_scope with obsDef.

Definition minDef :=
  (def "Min" `[r `: rep , n `: unit ]` : nat := ret (plus r 0))%obsDef.

Definition getMutDef
        (Rep : Type)
        (mutSigs : list mutSig)
        (mutDefs : ilist (@mutDef Rep) mutSigs)
        (idx : string)
: mutatorMethodType Rep
                    (mutDom
                       (nth (findIndex mutSig_eq mutSigs idx)
                            mutSigs ("null" : rep × () → rep)%mutSig)) :=
  mutBody (ith mutSig_eq mutDefs idx
              ("null" : rep × () → rep)%mutSig
              {| mutBody := (fun r _ => ret r) |}).

Definition getObsDef
         (Rep : Type)
         (obsSigs : list obsSig)
         (obsDefs : ilist (@obsDef Rep) obsSigs)
         (idx : string)
: observerMethodType Rep
                     (obsDom (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs ("null" : rep × () → ())%obsSig))
                     (obsCod (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs ("null" : rep × () → ())%obsSig)) :=
  obsBody (ith obsSig_eq obsDefs idx _
               (@Build_obsDef Rep ("null" : rep × () → ()) (fun r _ => ret tt))).

Arguments getMutDef / .
Arguments getObsDef / .

Program Definition BuildADT
        (Rep : Type)
        (mutSigs : list mutSig)
        (obsSigs : list obsSig)
        (mutDefs : ilist (@mutDef Rep) mutSigs)
        (obsDefs : ilist (@obsDef Rep) obsSigs)
: ADT (BuildADTSig mutSigs obsSigs)
      := {|
          Rep := Rep;
          MutatorMethods idx := getMutDef mutDefs idx;
          ObserverMethods idx := getObsDef obsDefs idx
          |}.

Notation "'ADTRep' r `[ mut1 , .. , mutn ; obs1 , .. , obsn ]` " :=
  (@BuildADT r
             _
             _
             (icons _ mut1%mutDef .. (icons _ mutn%mutDef (inil (@mutDef r))) ..)
             (icons _ obs1%obsDef .. (icons _ obsn%obsDef (inil (@obsDef r))) ..))
    (at level 1,
     format "'ADTRep'  r  '/' '[hv  ' `[  mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn  ']' ]`") : ADT_scope.

Local Open Scope ADT_scope.

Definition MinCollection : ADT MinCollectionSig :=
  ADTRep nat `[
           def "Insert" `[ r `: rep , n `: nat ]` : rep :=
             ret (plus r n) ;
           def "Min" `[r `: rep , n `: unit ]` : nat :=
               ret (plus r 0)
         ]` .

Section ReplaceMethods.

  (* Definitions for replacing method bodies. *)

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

Arguments replaceMutDef _ _ _ _ (newDef%mutDef) / .
Arguments ADTReplaceMutDef _ _ _ _ _ _ (newDef%mutDef) / .

Arguments replaceObsDef _ _ _ _ (newDef%obsDef) / .
Arguments ADTReplaceObsDef _ _ _ _ _ _ (newDef%obsDef) / .

Definition MinCollection' :=
  ADTReplaceObsDef
    (icons _ (def "Insert" `[ r `: rep , n `: nat ]` : rep :=
                ret (plus r n))%mutDef (inil (@mutDef _)))
    (icons _ (def "Min" `[r `: rep , n `: unit ]` : nat :=
                ret (plus r 0))%obsDef (inil (@obsDef _)))
    "Min"%string
    (def "Min" `[r `: rep , n `: unit ]` : nat :=
       ret (plus 0 r)).

Definition MinCollection'' :=
  ADTReplaceMutDef
    (icons _ (def "Insert" `[ r `: rep , n `: nat ]` : rep :=
                ret (plus r n))%mutDef (inil (@mutDef _)))
    (icons _ (def "Min" `[r `: rep , n `: unit ]` : nat :=
                ret (plus r 0))%obsDef (inil (@obsDef _)))
    "Insert"%string
    (def "Insert" `[r `: rep , n `: nat ]` : rep :=
       ret (r + n)).

Goal (MinCollection'' = MinCollection').
  unfold MinCollection'', MinCollection'; simpl.
Abort.
