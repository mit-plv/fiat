Require Import Coq.Lists.List Fiat.Common
        Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADTNotation.BuildADTSig Fiat.ADTNotation.BuildADT
        Fiat.Common.ilist Fiat.Common.BoundedLookup
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.Refinements.HoneRepresentation
        Fiat.ADTRefinement.BuildADTSetoidMorphisms
        Fiat.ADTRefinement.Refinements.ADTCache.

(* A generic refinement and honing tactic for adding a cache
    to the representation of an ADT built from [BuildADT]. *)

Section addCache.

  Variable rep : Type.
  Variable cacheType : Type.

  Variable cacheSpec : rep -> cacheType -> Prop.

  (* When switching representations, we can always build a default
     implementation (computation?) for the methods of an ADT with
     using the old methods. *)

  (*Definition addCacheToConsDef
             (Sig : consSig)
             (oldCons : @consDef rep Sig)
  : @consDef (@cachedRep rep cacheType) Sig :=
    {| consBody := addCacheToConstructor cacheSpec (consBody oldCons) |}.

  Definition addCacheToMethDef
             (Sig : methSig)
             (oldCons : @methDef rep Sig)
  : @methDef (@cachedRep rep cacheType) Sig :=
    {| methBody := addCacheToMethod cacheSpec (methBody oldCons) |}. *)

  (*Lemma refine_addCacheTo_BuildADT
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef rep) consSigs)
            (methDefs : ilist (@methDef rep) methSigs) :
    refineADT
      (BuildADT consDefs methDefs)
      (BuildADT (imap _ addCacheToConsDef consDefs)
                (imap _ addCacheToMethDef methDefs)).
  Proof.
    generalize (refine_addCacheToADT
                  cacheSpec
                  (BuildADTSig consSigs methSigs)
                  (fun idx => getConsDef consDefs idx)
                  (fun idx => getMethDef methDefs idx)); eauto; intros.
    econstructor; intros.
    - simpl Constructors; rewrite <- ith_Bounded_imap.
      apply refine_addCacheToConstructor.
    - simpl Methods; rewrite <- ith_Bounded_imap.
      apply refine_addCacheToMethod.
  Qed. *)

End addCache.

(* Honing tactic for refining the ADT representation which provides
   default method and constructor implementations. *)

(*Tactic Notation "add" "cache" "with" "spec" constr(cacheSpec') :=
  eapply SharpenStep;
  [eapply refine_addCacheTo_BuildADT with (cacheSpec := cacheSpec') |
   compute [imap addCacheToConsDef addCacheToConstructor
                 addCacheToMethDef addCacheToMethod]; simpl ]. *)
