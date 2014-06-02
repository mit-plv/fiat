Require Export Common Computation ADTSig.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** Basic ADT definitions *)

(** Interface of an ADT *)
Record ADT (Sig : ADTSig) :=
  {
    (** The representation type of the ADT **)
    Rep : Type;

    (** Constructor implementations *)
    Constructors :
      forall idx : ConstructorIndex Sig,
        constructorType Rep (ConstructorDom Sig idx);

    (** Method implementations *)
    Methods :
      forall idx : MethodIndex Sig,
        methodType Rep (fst (MethodDomCod Sig idx))
                   (snd (MethodDomCod Sig idx))

  }.
