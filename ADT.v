Require Export Common Computation ADTSig.
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

Record mutDef {Rep : Type} :=
  { mutDefSig :> mutSig;
    mutBody : mutatorMethodType Rep (mutDom mutDefSig) }.

Notation "'def' id `[ r `: 'rep' , x `: dom ]` : 'rep' := bod" :=
  {| mutDefSig := {| mutID := id; mutDom := dom |};
     mutBody := (fun r x => bod) |}
    (at level 70, format "'def'  id  `[ r  `:  'rep' ,  x  `:  dom ]`  :  'rep'  :=  '[v'   bod ']' " ) :
mutDef_scope.

Bind Scope mutDef_scope with mutDef.
Delimit Scope mutDef_scope with mutDef.

Record obsDef {Rep : Type} :=
  { obsDefSig : obsSig;
    obsBody : observerMethodType Rep (obsDom obsDefSig) (obsCod obsDefSig)}.

Notation "'def' id `[ r `: 'rep' , x `: dom ]` : cod := bod" :=
  {| obsDefSig := {| obsID := id; obsDom := dom; obsCod := cod |};
     obsBody := (fun r x => bod) |}
    (at level 70, format "'def'  id  `[ r  `:  'rep' ,  x  `:  dom ]`  :  cod  :=  '[v'   bod ']' " ) :
obsDef_scope.

Bind Scope obsDef_scope with obsDef.
Delimit Scope obsDef_scope with obsDef.

Definition minDef :=
  (def "Min" `[r `: rep , n `: unit ]` : nat := ret (plus r 0))%obsDef.

Obligation Tactic := intros; simpl in *; find_if_inside; eassumption.

Program Fixpoint getmut
        (Rep : Type)
        (mutDefs : list (@mutDef Rep))
        (idx : string)
: mutatorMethodType Rep
                    (mutDom
                       (nth (findName (map mutID (map mutDefSig mutDefs)) idx)
                            (map mutDefSig mutDefs) (idx : rep ✕ () → rep)%mutSig)) :=
  match mutDefs with
    | {| mutDefSig :=
           {| mutID := id;
              mutDom := dom |};
         mutBody := mdef |} :: mutDefs' => (fun IndH => _ ) (getmut mutDefs' idx)
    | [] => fun r _ => ret r
  end.

Program Fixpoint getobs
         (Rep : Type)
         (obsDefs : list (@obsDef Rep))
         (idx : string)
: observerMethodType Rep
                     (obsDom (nth (findName (map obsID (map obsDefSig obsDefs)) idx)
                                  (map obsDefSig obsDefs) (idx : rep ✕ () → ())%obsSig))
                     (obsCod (nth (findName (map obsID (map obsDefSig obsDefs)) idx)
                                  (map obsDefSig obsDefs) (idx : rep ✕ () → ())%obsSig)) :=
  match obsDefs with
    | {| obsDefSig :=
           {| obsID := id;
              obsDom := dom;
              obsCod := cod |};
         obsBody := mdef |} :: obsDefs' => (fun IndH => _ ) (getobs obsDefs' idx)

    | [] => fun r t => ret tt
  end.

Program Definition BuildADT (Rep : Type)
           (mutDefs : list mutDef)
           (obsDefs : list obsDef)
: ADT (BuildADTSig (map mutDefSig mutDefs)
                   (map obsDefSig obsDefs))
      := {|
          Rep := Rep;
          MutatorMethods idx := getmut mutDefs idx;
          ObserverMethods idx := getobs obsDefs idx
          |}.

Notation "'ADTRep' r `[ mut1 , .. , mutn ; obs1 , .. , obsn ]` " :=
  (@BuildADT r
             (mut1%mutDef :: .. (mutn%mutDef :: []) ..)
             (obs1%obsDef :: .. (obsn%obsDef :: []) ..))
    (at level 70,
     format "'ADTRep'  r  `[ '[v' '//' mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn '//'  ']' ]`") : ADT_scope.

Local Open Scope ADT_scope.

Definition MinCollection : ADT MinCollectionSig :=
  ADTRep nat `[
           def "Insert" `[ r `: rep , n `: nat ]` : rep :=
             ret (plus r n) ;
           def "Min" `[r `: rep , n `: unit ]` : nat :=
               ret (plus r 0)
         ]` .
