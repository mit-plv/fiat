Require Export ADTSynthesis.Common ADTSynthesis.Computation ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.
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

Definition is_computationalADT (Sig : ADTSig) (A : ADT Sig) :=
  (forall (idx : ConstructorIndex Sig) i,
     is_computational (Constructors A idx i))
  /\ (forall (idx : MethodIndex Sig) i r,
        is_computational (Methods A idx i r)).

Definition CallComputationalMethod
           (Sig : ADTSig)
           (A : ADT Sig)
           (CompA : is_computationalADT A)
           (idx : MethodIndex Sig)
           (r : Rep A)
           (i : fst (MethodDomCod Sig idx))
: Rep A * snd (MethodDomCod Sig idx) :=
  is_computational_val (proj2 CompA idx r i).

Definition CallComputationalConstructor
           (Sig : ADTSig)
           (A : ADT Sig)
           (CompA : is_computationalADT A)
           (idx : ConstructorIndex Sig)
           (i : ConstructorDom Sig idx)
: Rep A :=
  is_computational_val (proj1 CompA idx i).
