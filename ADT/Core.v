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
