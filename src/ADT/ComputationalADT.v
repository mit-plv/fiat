Require Export Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** Definition of a fully deterministic ADT *)

(** Type of a deterministic method. *)
Fixpoint cMethodType' (rep : Type)
         (dom : list Type)
         (cod : option Type)
  : Type :=
  match dom with
  | nil =>
    match cod with
    | Some cod' =>  (prod rep cod') (* Final model and return value *)
    | None => rep
    end
  | cons d dom' =>
    d -> cMethodType' rep dom' cod (* Method arguments *)
  end.
Fixpoint cMethodType
         (arity : nat)
         (rep : Type)
         (dom : list Type)
         (cod : option Type) : Type :=
  match arity with
  | 0 => cMethodType' rep dom cod
  | S arity' => rep -> cMethodType arity' rep dom cod
  end.

(** Type of a deterministic constructor. *)
Definition cConstructorType (rep : Type) (dom : list Type)
  := cMethodType 0 rep dom None.

(** Interface of a ADT implementation *)
Record pcADT (Sig : ADTSig)
       (* Representation Type of the ADT is a parameter to get around
        Universe problems. *)
       (cRep : Type)
: Type :=
  {
    (** Method implementations *)
    pcMethods :
      forall idx : MethodIndex Sig,
        cMethodType
          (fst (fst (MethodDomCod Sig idx)))
          cRep
          (snd (fst (MethodDomCod Sig idx)))
          (snd (MethodDomCod Sig idx))
  }.

(* Definition of of an ADT implementation *)
Definition cADT (Sig : ADTSig) := sigT (pcADT Sig).
Definition cRep {Sig : ADTSig} (c : cADT Sig) : Type := projT1 c.
Definition cMethods {Sig : ADTSig} (c : cADT Sig)
           (idx : MethodIndex Sig) :
  cMethodType
    (fst (fst (MethodDomCod Sig idx)))
    (cRep c)
    (snd (fst (MethodDomCod Sig idx)))
    (snd (MethodDomCod Sig idx))
  := pcMethods (projT2 c) idx.

(* Lifting a deterministic ADT to computation-land. *)
Fixpoint LiftcConstructor
         (rep : Type)
         (dom : list Type)
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
         (rep : Type)
         (dom : list Type)
         (cod : option Type)
  : cMethodType' rep dom cod
    -> methodType' rep dom cod :=
  match dom return
        cMethodType' rep dom cod
        -> methodType' rep dom cod
  with
  | nil =>
    match cod with
    | Some cod' => fun cMethod => ret cMethod
    | None => fun cMethod => ret cMethod
    end
  | cons d dom' => fun cMethod t =>
                     LiftcMethod' rep dom' cod (cMethod t)
  end.

Fixpoint LiftcMethod
         (arity : nat)
         (rep : Type)
         (dom : list Type)
         (cod : option Type)
  : cMethodType arity rep dom cod
    -> methodType arity rep dom cod
  := match arity return
           cMethodType arity rep dom cod
           -> methodType arity rep dom cod with
     | 0 => LiftcMethod' rep dom cod
     | S arity' => fun cMethod r => LiftcMethod arity' rep dom cod (cMethod r)
     end.

Definition LiftcADT (Sig : ADTSig)
           (A : cADT Sig) : ADT Sig :=
  {| Rep                := cRep A;
     Methods idx    := LiftcMethod _ _ _ _ (cMethods A idx) |}.
