Require Import Common Computation ADTNotation.ilist ADTSig ADTNotation.StringBound.
Require Import List String.

(* Notation for ADT Signatures. *)

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

(* Notation for ADT Methods. *)

Notation "id : 'rep' × dom → cod" :=
  {| obsID := id;
     obsDom := dom;
     obsCod := cod |} : obsSig_scope.

Notation "id : 'rep' × dom → 'rep'" :=
  {| mutID := id;
     mutDom := dom |} : mutSig_scope.

Definition mutSig_eq (mdef : mutSig) (idx : string) : bool :=
  if string_dec (mutID mdef) idx then true else false.

Definition obsSig_eq (odef : obsSig) (idx : string) : bool :=
  if string_dec (obsID odef) idx then true else false.

(* [BuildADTSig] constructs an ADT signature from a list of
   mutator signatures and a list of observer signatures.
   This definition can be formated nicely using notations. *)

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

(* Notation for ADT signatures utilizing [BuildADTSig]. *)

Notation "'ADTsignature' { mut1 , .. , mutn ; obs1 , .. , obsn }" :=
  (BuildADTSig (mut1%mutSig :: .. (mutn%mutSig :: []) ..)
              (obs1%obsSig :: .. (obsn%obsSig :: []) ..))
    (at level 70,
     format "'ADTsignature'  { '[v' '//' mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn '//'  ']' }") : ADTSig_scope.

(* Since [BuildADTSig] constructs an ADT signature with
   [BoundedString] indices, every mutator index appears
   in [mutSigs] and every observer index appears in [obsSigs]. *)
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
                    (@sbound _ _ (mutIdx)))
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
                    (@sbound _ _ obsIdx))
           as [ [id dom cod] [id_eq In_dom] ]; subst.
  exists dom; exists cod; eauto; rewrite <- id_eq; eassumption.
Qed.
