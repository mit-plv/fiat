Require Export Common Computation.

(** Type of a mutator method. *)
Definition mutatorMethodType (Ty dom : Type)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> Comp Ty (* Final Model *).

(** Type of an obeserver method. *)
Definition observerMethodType (Ty dom cod : Type)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> Comp cod. (* Return value *)

Record ADTSig :=
  { MutatorIndex : Type;
     (** The index set of mutators *)

     ObserverIndex : Type;
     (** The index set of observers *)

     MutatorDom : MutatorIndex -> Type;
     (** The representation-independent piece of the
         domain of mutator methods. **)

    ObserverDomCod : ObserverIndex -> (Type * Type)
     (** The representation-independent piece of the
         domain and codomain of observer methods. **)

  }.

(* Some notations for ADT Signatures. *)

Require Import List String.

Notation "id : 'rep' ✕ dom → cod" :=
  (@pair string (@prod Type Type) id%string
         (@pair Type Type dom cod))
    (at level 60, format "id  :  'rep'  ✕  dom  →  cod" ).

Notation "id : 'rep' ✕ dom → 'rep'" :=
  (@pair string Type id%string dom)
    (at level 60, format "id  :  'rep'  ✕  dom  →  'rep'" ).

Fixpoint mutSigMap (sig : list (string * Type)) (id : string)
: Type :=
  match sig with
    | (id', ty) :: sig' => if string_dec id id' then ty else mutSigMap sig' id
    | _ => unit
  end.

Fixpoint obsSigMap (sig : list (string * (Type * Type))) (id : string)
: (Type * Type) :=
  match sig  with
    | (id', ty) :: sig' => if string_dec id id' then ty else obsSigMap sig' id
    | _ => @pair Type Type unit unit
  end.

Notation "'ADTsignature' { mut1 , .. , mutn ; obs1 , .. , obsn }" :=
  {| MutatorIndex := string ;
     ObserverIndex := string ;
    MutatorDom := mutSigMap (mut1 :: .. (mutn :: []) ..);
    ObserverDomCod := obsSigMap (obs1 :: .. (obsn :: []) ..)
  |} (at level 70,
     format "'ADTsignature'  { '[v' '//' mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn '//'  ']' }").
