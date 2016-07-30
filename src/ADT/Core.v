Require Export Fiat.Common
        Fiat.Computation
        Fiat.ADT.ADTSig.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** Basic ADT definitions *)

(** Interface of an ADT *)
Record ADT (Sig : ADTSig) :=
  {
    (** The representation type of the ADT **)
    Rep : Type;

    (** Method implementations *)
    Methods :
      forall idx : MethodIndex Sig,
        methodType (fst (fst (MethodDomCod Sig idx)))
                   Rep (snd (fst (MethodDomCod Sig idx)))
                   (snd (MethodDomCod Sig idx))

  }.
