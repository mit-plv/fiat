Require Export Fiat.Common
        Fiat.Computation.

(** Type of a method. *)
Fixpoint methodType' (rep : Type)
         (dom : list Type)
         (cod : option Type) : Type :=
  match dom with
  | nil =>
    match cod with
    | Some cod' => Comp (rep * cod') (* Final model and a return value *)
    | _ => Comp rep
    end
  | cons d dom' =>
    d -> methodType' rep dom' cod (* Method arguments *)
  end.

Fixpoint methodType
           (arity : nat)
           (rep : Type)
           (dom : list Type)
           (cod : option Type) : Type :=
  match arity with
  | 0 => methodType' rep dom cod
  | S arity' => rep -> methodType arity' rep dom cod
  end.

(** Type of a constructor. *)
Definition constructorType
         (rep : Type)
         (dom : list Type) : Type :=
  methodType 0 rep dom None.

(* Signatures of ADT operations *)
Record ADTSig :=
  {
    (** The index set of methods *)
    MethodIndex : Type;

    (** The representation-independent domain and codomain of methods. *)
    MethodDomCod : MethodIndex -> nat * (list Type) * (option Type)

  }.
