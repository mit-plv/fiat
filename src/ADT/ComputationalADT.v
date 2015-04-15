Require Export Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** Definition of a fully computational ADT *)

(** Type of a computational constructor. *)
Definition cConstructorType (rep dom : Type)
  :=  dom (* Initialization arguments *)
     -> rep (* Freshly constructed model *).

(** Type of a method. *)
Definition cMethodType (rep dom cod : Type)
  := rep    (* Initial model *)
     -> dom (* Method arguments *)
     -> (rep * cod) (* Final model and return value. *).

(** Interface of a computational ADT *)
Record pcADT (Sig : ADTSig)
       (* Representation Type of the ADT is a parameter to get around
        Universe problems. *)
       (cRep : Type)
: Type :=
  {
    (** Constructor implementations *)
    pcConstructors :
      forall idx : ConstructorIndex Sig,
        cConstructorType cRep (ConstructorDom Sig idx);

    (** Method implementations *)
    pcMethods :
      forall idx : MethodIndex Sig,
        cMethodType cRep (fst (MethodDomCod Sig idx))
                                (snd (MethodDomCod Sig idx))
  }.

Definition cADT (Sig : ADTSig) := sigT (pcADT Sig).
Definition cRep {Sig : ADTSig} (c : cADT Sig) : Type := projT1 c.
Definition cConstructors {Sig : ADTSig} (c : cADT Sig)
           (idx : ConstructorIndex Sig)
: cConstructorType (cRep c) (ConstructorDom Sig idx)
  := pcConstructors (projT2 c) idx.
Definition cMethods {Sig : ADTSig} (c : cADT Sig)
           (idx : MethodIndex Sig) :
  cMethodType (cRep c) (fst (MethodDomCod Sig idx))
              (snd (MethodDomCod Sig idx))
  := pcMethods (projT2 c) idx.

Definition LiftcADT (Sig : ADTSig) (A : cADT Sig) : ADT Sig :=
  {| Rep                := cRep A;
     Constructors idx d := ret (cConstructors A idx d);
     Methods idx r d    := ret (cMethods A idx r d) |}.
