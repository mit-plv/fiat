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

Program Definition mutSig_eq (mdef : mutSig) (idx : string)
: { True } + {mutID mdef <> idx} :=
  if string_dec (mutID mdef) idx then left I else right _.

Program Definition obsSig_eq (odef : obsSig) (idx : string)
: { True } + {obsID odef <> idx} :=
  if string_dec (obsID odef) idx then left I else right _.

(* [BuildADTSig] constructs an ADT signature from a list of
   mutator signatures and a list of observer signatures.
   This definition can be formated nicely using notations. *)

Definition BuildADTSig
           (mutSigs : list mutSig)
           (obsSigs : list obsSig)
: ADTSig :=
  {| MutatorIndex := BoundedString (map mutID mutSigs);
     ObserverIndex := BoundedString (map obsID obsSigs);
     MutatorDom idx :=
       mutDom (nth_Bounded mutID mutSigs idx) ;
    ObserverDomCod idx :=
      let domcod := (nth_Bounded obsID obsSigs idx)
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
   in [mutSigs] and every observer index appears in [obsSigs].

Lemma In_mutIdx :
  forall mutSigs
         (mutIdx : BoundedString (map mutID mutSigs)),
    exists dom,
      List.In {| mutID := bindex _ mutIdx;
                 mutDom := dom
              |} mutSigs.
Proof.
  intros.
  destruct (proj1 (in_map_iff mutID mutSigs (bindex _ mutIdx))
                    (@ibound _ _ _ mutIdx))
           as [ [id dom] [id_eq In_dom] ]; subst.
  exists dom; eauto; rewrite <- id_eq; eassumption.
Qed.

Lemma In_obsIdx :
  forall obsSigs
         (obsIdx : BoundedString (map obsID obsSigs)),
    exists dom cod,
      List.In {| obsID := bindex _ obsIdx;
                 obsDom := dom;
                 obsCod := cod
              |} obsSigs.
Proof.
  intros.
  destruct (proj1 (in_map_iff obsID obsSigs (bindex _ obsIdx))
                    (@ibound _ _ _ obsIdx))
           as [ [id dom cod] [id_eq In_dom] ]; subst.
  exists dom; exists cod; eauto; rewrite <- id_eq; eassumption.
Qed.

Program Fixpoint BoundedIndex_mutIdx
      mutSigs
      (mutIdx : BoundedString (map mutID mutSigs))
: { i : BoundedIndex mutSigs |
    mutID (bindex _ i) = bindex _ mutIdx} :=
  match mutSigs as mutSigs' return
        forall mutIdx' : BoundedString (map mutID mutSigs'),
          { i : BoundedIndex mutSigs' |
             mutID (bindex _ i) = bindex _ mutIdx'} with
    | [] => fun mutIdx => _
    | mutSig :: mutSigs' => fun mutIdx' =>
      (fun H =>
         if (string_dec (mutID mutSig) (bindex _ mutIdx'))
         then _
         else _) (BoundedIndex_mutIdx mutSigs' )
  end mutIdx.
Next Obligation.
  destruct mutIdx0 as [a [[]]].
Defined.
Next Obligation.
  econstructor 1 with (x := {| bindex := mutSig0 |}); simpl; eauto.
Defined.
Next Obligation.
  pose (H (BoundIndex_tail mutIdx' H0)) as mutIdxInd.
  pose (indexb _ (` mutIdxInd)).
  econstructor 1 with
  (x := {| bindex := bindex _ (` mutIdxInd) |}); simpl in *; eauto.
  exact (proj2_sig mutIdxInd).
Defined.

Definition Build_mutSig_mutIdx
           mutSigs
           (mutIdx : BoundedString (map mutID mutSigs))
: mutSig :=
  bindex _ (` (BoundedIndex_mutIdx mutSigs mutIdx)).

Program Fixpoint BoundedIndex_obsIdx
      obsSigs
      (obsIdx : BoundedString (map obsID obsSigs))
: { i : BoundedIndex obsSigs |
    obsID (bindex _ i) = bindex _ obsIdx} :=
  match obsSigs as obsSigs' return
        forall obsIdx' : BoundedString (map obsID obsSigs'),
          { i : BoundedIndex obsSigs' |
             obsID (bindex _ i) = bindex _ obsIdx'} with
    | [] => fun obsIdx => _
    | obsSig :: obsSigs' => fun obsIdx' =>
      (fun H =>
         if (string_dec (obsID obsSig) (bindex _ obsIdx'))
         then _
         else _) (BoundedIndex_obsIdx obsSigs' )
  end obsIdx.
Next Obligation.
  destruct obsIdx0 as [a [[]]].
Defined.
Next Obligation.
  econstructor 1 with (x := {| bindex := obsSig0 |}); simpl; eauto.
Defined.
Next Obligation.
  pose (H (BoundIndex_tail obsIdx' H0)) as obsIdxInd.
  pose (indexb _ (` obsIdxInd)).
  econstructor 1 with
  (x := {| bindex := bindex _ (` obsIdxInd) |}); simpl in *; eauto.
  exact (proj2_sig obsIdxInd).
Defined.

Definition Build_obsSig_obsIdx
           obsSigs
           (obsIdx : BoundedString (map obsID obsSigs))
: obsSig :=
  bindex _ (` (BoundedIndex_obsIdx obsSigs obsIdx)).
 *)
