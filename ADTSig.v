Require Export Common Computation ilist.

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

Definition mutSig_eq (mdef : mutSig) (idx : string) : bool :=
  if string_dec (mutID mdef) idx then true else false.

Definition obsSig_eq (odef : obsSig) (idx : string) : bool :=
  if string_dec (obsID odef) idx then true else false.

Section StringBound.

  (* Ensuring that all of the indices are in a set
     allows us to omit a default case (method not found)
     for method lookups. *)

  Class StringBound (s : string) (Bound : list string) :=
    { sbound : In s Bound }.

  Global Instance StringBound_head (s : string) (Bound : list string)
  : StringBound s (s :: Bound).
  Proof.
    econstructor; simpl; eauto.
  Qed.

  Global Instance StringBound_tail
           (s s' : string) (Bound : list string)
           {sB' : StringBound s Bound}
  : StringBound s (s' :: Bound).
  Proof.
    econstructor; simpl; right; apply sbound.
  Qed.

  Record BoundedString (Bound : list string) :=
    { bounded_s :> string;
      s_bounded : StringBound bounded_s Bound }.

End StringBound.

Definition BuildADTSig
           (mutSigs : list mutSig)
           (obsSigs : list obsSig)
: ADTSig :=
  {| MutatorIndex := BoundedString (map mutID mutSigs);
     ObserverIndex := BoundedString (map obsID obsSigs);
     MutatorDom idx := mutDom (nth (findIndex mutSig_eq mutSigs idx)
                                   mutSigs {| mutID := "null";
                                              mutDom := unit |} ) ;
    ObserverDomCod idx := let domcod := (nth (findIndex obsSig_eq obsSigs idx)
                                   obsSigs {| obsID := "null";
                                              obsDom := unit;
                                              obsCod := unit |})
                          in (obsDom domcod, obsCod domcod)
  |}.

Bind Scope ADTSig_scope with ADTSig.
Delimit Scope ADTSig_scope with ADTSig.

Lemma In_mutIdx :
  forall mutSigs
         (mutIdx : BoundedString (map mutID mutSigs)),
    exists dom,
      List.In {| mutID := mutIdx;
            mutDom := dom
         |} mutSigs.
Proof.
  intros.
  destruct (proj1 (in_map_iff mutID mutSigs mutIdx)
                    (@sbound _ _ (s_bounded mutIdx)))
           as [ [id dom] [id_eq In_dom] ]; subst.
  exists dom; eauto; rewrite <- id_eq; eassumption.
Qed.

Lemma In_obsIdx :
  forall obsSigs
         (obsIdx : BoundedString (map obsID obsSigs)),
    exists dom cod,
      List.In {| obsID := obsIdx;
                 obsDom := dom;
                 obsCod := cod
              |} obsSigs.
Proof.
  intros.
  destruct (proj1 (in_map_iff obsID obsSigs obsIdx)
                    (@sbound _ _ (s_bounded obsIdx)))
           as [ [id dom cod] [id_eq In_dom] ]; subst.
  exists dom; exists cod; eauto; rewrite <- id_eq; eassumption.
Qed.


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
