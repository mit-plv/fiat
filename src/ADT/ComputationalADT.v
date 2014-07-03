Require Export Common Computation ADTSig ADT.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** Definition of a fully computational ADT *)

(** Type of a computational constructor. *)
Definition computationalConstructorType (rep dom : Type)
  :=  dom (* Initialization arguments *)
     -> rep (* Freshly constructed model *).

(** Type of a method. *)
Definition computationalMethodType (rep dom cod : Type)
  := rep    (* Initial model *)
     -> dom (* Method arguments *)
     -> (rep * cod) (* Final model and return value. *).

(** Interface of a computational ADT *)
Record cADT (Sig : ADTSig) :=
  {
    (** The representation type of the ADT **)
    cRep : Type;

    (** Constructor implementations *)
    cConstructors :
      forall idx : ConstructorIndex Sig,
        computationalConstructorType cRep (ConstructorDom Sig idx);

    (** Method implementations *)
    cMethods :
      forall idx : MethodIndex Sig,
        computationalMethodType cRep (fst (MethodDomCod Sig idx))
                                (snd (MethodDomCod Sig idx))
  }.

Definition is_computationalADT (Sig : ADTSig) (A : ADT Sig) :=
  (forall (idx : ConstructorIndex Sig) i,
     is_computational (Constructors A idx i))
  /\ (forall (idx : MethodIndex Sig) i r,
        is_computational (Methods A idx i r)).
