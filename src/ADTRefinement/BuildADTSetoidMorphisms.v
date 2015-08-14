Require Import Fiat.Common
        Fiat.ADTNotation.BuildADT Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.SetoidMorphisms.

(* A notation-friendly version of the setoid morphisms
   infrastructure for ADT refinement. *)

Theorem refineADT_BuildADT_Rep n n' consSigs methSigs oldRep newRep
      (AbsR : oldRep -> newRep -> Prop)
: @respectful_heteroT _ _ _ _
      (fun oldCons newCons =>
         forall consIdx,
           @refineConstructor oldRep newRep AbsR
                          _
                          (getConsDef oldCons consIdx)
                          (getConsDef newCons consIdx))
      (fun x y => @respectful_heteroT _ _ _ _
                    (fun oldMeth newMeth =>
                       forall methIdx,
                         @refineMethod oldRep newRep AbsR _ _
                                         (getMethDef oldMeth methIdx)
                                         (getMethDef newMeth methIdx))
                    (fun m m' => refineADT))
     (@BuildADT oldRep n n' consSigs methSigs)
     (@BuildADT newRep n n' consSigs methSigs).
 Proof.
   unfold Proper, respectful_heteroT; intros.
   let A := match goal with |- refineADT ?A ?B => constr:(A) end in
   let B := match goal with |- refineADT ?A ?B => constr:(B) end in
   eapply (@refinesADT _ A B AbsR);
     unfold id, pointwise_relation in *; simpl in *; intros; eauto.
 Qed.

Lemma refineADT_BuildADT_Both
      rep n n' consigs methSigs
: forall oldCons newCons,
    (forall consIdx, @refineConstructor _ _ eq _
                                   (getConsDef oldCons consIdx)
                                   (getConsDef newCons consIdx))
    -> forall oldMeth newMeth,
         (forall methIdx, @refineMethod _ _ eq _ _
                                         (getMethDef oldMeth methIdx)
                                         (getMethDef newMeth methIdx))
         -> refineADT (@BuildADT n n' rep consigs methSigs oldCons oldMeth)
                      (@BuildADT n n' rep consigs methSigs newCons newMeth).
Proof.
  intros; eapply refineADT_BuildADT_Rep; eauto; reflexivity.
Qed.

(*Add Parametric Morphism rep consigs methSigs
: (@BuildADT rep consigs methSigs)
    with signature
    (fun oldCons newCons =>
       forall consIdx, @refineConsator _ _ eq _
                                  (getConsDef oldCons consIdx)
                                  (getConsDef newCons consIdx))
      ==> (fun oldMeth newMeth =>
             forall methIdx, @refineMetherver _ _ eq _ _
                                         (getMethDef oldMeth methIdx)
                                         (getMethDef newMeth methIdx))
      ==> refineADT
      as refineADT_BuildADT_Both.
Proof.
  intros; apply refineADT_BuildADT_Both'.
Qed.*)
