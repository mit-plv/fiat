Require Export Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** Definition of a fully deterministic ADT *)

(** Type of a deterministic constructor. *)
Fixpoint cConstructorType (rep : Type) (dom : list Type)
  :=
    match dom with
    | nil =>
      rep (* Freshly constructed model *)
    | cons d dom' =>
      d -> cConstructorType rep dom' (* Initialization arguments *)
    end.

(** Type of a deterministic method. *)
Fixpoint cMethodType' (rep cod : Type)
           (dom : list Type) : Type :=
  match dom with
  | nil =>
    (prod rep cod) (* Final model and return value *)
  | cons d dom' =>
    d -> cMethodType' rep cod dom' (* Method arguments *)
  end.
Definition cMethodType (rep : Type)
           (dom : list Type)
           (cod : Type) : Type :=
  rep -> cMethodType' rep cod dom.

(** Interface of a ADT implementation *)
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

(* Definition of of an ADT implementation *)
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

(* Lifting a deterministic ADT to computation-land. *)
Fixpoint LiftcConstructor
         (rep : Type) (dom : list Type)
  : cConstructorType rep dom
    -> constructorType rep dom :=
  match dom return
        cConstructorType rep dom
        -> constructorType rep dom
  with
  | nil => fun cConstructor => ret cConstructor
  | cons d dom' => fun cConstructor t =>
                   LiftcConstructor rep dom' (cConstructor t)
  end.

Fixpoint LiftcMethod'
         (rep cod : Type) (dom : list Type)
  : cMethodType' rep cod dom
    -> methodType' rep cod dom :=
  match dom return
        cMethodType' rep cod dom
        -> methodType' rep cod dom
  with
  | nil => fun cMethod => ret cMethod
  | cons d dom' => fun cMethod t =>
                     LiftcMethod' rep cod dom' (cMethod t)
  end.

Definition LiftcMethod
           (rep : Type) (dom : list Type) (cod : Type)
           (cMethod : cMethodType rep dom cod)
  : methodType rep dom cod
  := fun r => LiftcMethod' rep cod dom (cMethod r).

Definition LiftcADT (Sig : ADTSig) (A : cADT Sig) : ADT Sig :=
  {| Rep                := cRep A;
     Constructors idx :=  LiftcConstructor _ _ (cConstructors A idx);
     Methods idx    := LiftcMethod (cMethods A idx) |}.
