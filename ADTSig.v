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

Record mutSig :=
  { mutID : string;
    mutDom : Type }.

Arguments Build_mutSig mutID%string mutDom%type_scope.
Bind Scope mutSig_scope with mutSig.
Delimit Scope mutSig_scope with mutSig.

Record obsSig :=
  { obsID : string ;
    obsDom : Type ;
    obsCod : Type
  }.

Arguments Build_obsSig obsID%string obsDom%type_scope obsCod%type_scope.
Bind Scope obsSig_scope with obsSig.
Delimit Scope obsSig_scope with obsSig.

Notation "id : 'rep' ✕ dom → cod" :=
  {| obsID := id;
     obsDom := dom;
     obsCod := cod |}
    (at level 60, format "id  :  'rep'  ✕  dom  →  cod" ) : obsSig_scope.

Notation "id : 'rep' ✕ dom → 'rep'" :=
  {| mutID := id;
     mutDom := dom |}
    (at level 60, format "id  :  'rep'  ✕  dom  →  'rep'" ) : mutSig_scope.

Fixpoint findName (sig : list string) (id : string)
: nat :=
  match sig with
    | id' :: sig' => if string_dec id id' then 0 else S (findName sig' id)
    | _ => 0
  end.

Definition BuildADTSig
           (mutSigs : list mutSig)
           (obsSigs : list obsSig)
: ADTSig :=
  {| MutatorIndex := string ;
     ObserverIndex := string ;
     MutatorDom idx := mutDom (nth (findName (map mutID mutSigs) idx)
                                mutSigs {| mutID := idx;
                                           mutDom := unit |} ) ;
    ObserverDomCod idx := let domcod := (nth (findName (map obsID obsSigs) idx)
                                   obsSigs {| obsID := idx;
                                              obsDom := unit;
                                              obsCod := unit |})
                          in (obsDom domcod, obsCod domcod)
  |}.

Bind Scope ADTSig_scope with ADTSig.
Delimit Scope ADTSig_scope with ADTSig.

Notation "'ADTsignature' { mut1 , .. , mutn ; obs1 , .. , obsn }" :=
  (BuildADTSig (mut1%mutSig :: .. (mutn%mutSig :: []) ..)
              (obs1%obsSig :: .. (obsn%obsSig :: []) ..))
    (at level 70,
     format "'ADTsignature'  { '[v' '//' mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn '//'  ']' }") : ADTSig_scope.

Local Open Scope ADTSig_scope.

Definition MinCollectionSig : ADTSig :=
  ADTsignature {
      "Insert" : rep ✕ nat → rep ;
      "Min" : rep ✕ unit → nat
    }.

Definition BookStoreSig : ADTSig :=
  ADTsignature {
      "PlaceOrder" : rep ✕ nat → rep,
      "AddBook" : rep ✕ string → rep ;
      "GetTitles" : rep ✕ string → list string,
      "NumOrders" : rep ✕ string → nat
    }.
