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

Obligation Tactic := intros; simpl in *; find_if_inside; eassumption.

Definition getMutDef
        (Rep : Type)
        (mutSigs : list mutSig)
        (mutDefs : ilist (@mutDef Rep) mutSigs)
        (idx : string)
: mutatorMethodType Rep
                    (mutDom
                       (nth (findIndex mutSig_eq mutSigs idx)
                            mutSigs (idx : rep ✕ () → rep)%mutSig)) :=
  mutBody (ith mutSig_eq mutDefs idx
              (idx : rep ✕ () → rep)%mutSig
              {| mutBody := (fun r _ => ret r) |}).

Print obsDef.

Definition getObsDef
         (Rep : Type)
         (obsSigs : list obsSig)
         (obsDefs : ilist (@obsDef Rep) obsSigs)
         (idx : string)
: observerMethodType Rep
                     (obsDom (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs (idx : rep ✕ () → ())%obsSig))
                     (obsCod (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs (idx : rep ✕ () → ())%obsSig)) :=
  obsBody (ith obsSig_eq obsDefs idx _
               (@Build_obsDef Rep (idx : rep ✕ () → ()) (fun r _ => ret tt))).

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

Print MinCollection.
