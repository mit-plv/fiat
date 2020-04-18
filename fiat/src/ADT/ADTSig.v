Require Export Fiat.Common Fiat.Computation.

(** Type of a constructor. *)
Fixpoint constructorType (rep : Type)
         (dom : list Type) : Type :=
  match dom with
  | nil =>
    Comp rep (* Freshly constructed model *)
  | cons d dom' =>
    d -> constructorType rep dom' (* Initialization arguments *)
  end.

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
Definition methodType (rep : Type)
           (dom : list Type)
           (cod : option Type) : Type :=
  rep -> methodType' rep dom cod.

(* Signatures of ADT operations *)
Record ADTSig :=
  {
    (** The index set of constructors *)
    ConstructorIndex : Type;

    (** The index set of methods *)
    MethodIndex : Type;

    (** The representation-independent domain of constructors. *)
    ConstructorDom : ConstructorIndex -> list Type;

    (** The representation-independent domain and codomain of methods. *)
    MethodDomCod : MethodIndex -> (list Type) * (option Type)

  }.
