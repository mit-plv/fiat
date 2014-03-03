Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

(** Basic ADT definitions **)

(* The domain and codomain of an ADT Context use
   option types to signify whether the type is
   an ADT rep. Simply parameterizing over the representation
   type complicates the simulation relation *)

Definition ADTContext (names : Type)
           (dom cod : names -> option Type)
           (rep : Type)
: Context:=
  {|
    names := names;
    dom idx := match (dom idx) with
                   | Some Ty => Ty
                   | _ => rep
               end;
    cod idx := match (cod idx) with
                   | Some Ty => Ty
                   | _ => rep
               end
  |}.

Definition MethodType (ctx : Context) (dom cod : Type)
: Type := dom -> Comp (ctx := ctx) cod.

(** Interface of an ADT. The [ADTSignature] parameter is a context
    which contains the signatures of this ADT's methods. **)

Record ADT (ADTSignature : Type -> Context) :=
  {
    Rep : Type;
    (** The way we model state mathematically *)

    Methods : forall idx : @names (ADTSignature Rep),
                MethodType (ADTSignature Rep) (dom idx) (cod idx)
    (** Implementations of the methods with sigatures given in
     [ADTSignature] **)

  }.

(* ADT bundled with its signature. *)
Record BundledADT :=
  { ADTSig : Type -> Context;
    UnBundledADT : ADT ADTSig }.

Definition UnBundledRep (A : BundledADT) := Rep (UnBundledADT A).
Definition UnBundledMethods (A : BundledADT) := Methods (UnBundledADT A).
Definition UnBundledADTSig (A : BundledADT) := ADTSig A (UnBundledRep A).
Definition UnBundledMethodNames (A : BundledADT) := @names (UnBundledADTSig A).

Definition ADTLookupContext (A : BundledADT) : LookupContext
  := {| LContext := UnBundledADTSig A;
        lookup := UnBundledMethods A |}.

Definition Method (A : BundledADT) (i : UnBundledMethodNames A) :
  MethodType (UnBundledADTSig A) (dom i) (cod i) :=
  fun d => ``[UnBundledMethods A i d with ADTLookupContext A ]``.
