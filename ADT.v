Require Export Common Computation ADTSig.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

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

(*
Notation "'observer' id ( dom x ) { bod }" :=
  (id, fun x : dom => bod ) (at level 60).

Notation "'mutator' id ( dom x ) { bod }" :=
  (id, fun x : dom => bod ) (at level 60).

Notation "'ADT' 'with' 'sig' Sig { mut1 ; .. ; mutn } { obs1 ; .. ; obsn }" :=
  (@Build_ADT Sig
             (fun idx => IdxMap.find idx (IdxAdd mut1 .. (IdxAdd mutn IdxMap.empty) ..))
             (fun idx => IdxMap.find idx (IdxAdd obs1 .. (IdxAdd obsn IdxMap.empty) ..)))
            (at level 70) *)
