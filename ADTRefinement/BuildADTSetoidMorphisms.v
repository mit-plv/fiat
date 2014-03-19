Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Core ADTRefinement.SetoidMorphisms.

Generalizable All Variables.
Set Implicit Arguments.

Lemma refineADT_BuildADT_Rep mutSigs obsSigs oldRep newRep
      (SiR : oldRep -> newRep -> Prop)
: respectful_hetero _ _ _ _
      (fun oldMuts newMuts =>
         forall mutIdx,
           @refineMutator oldRep newRep SiR
                          _
                          (getMutDef oldMuts mutIdx)
                          (getMutDef newMuts mutIdx))
      (fun x y => respectful_hetero _ _ _ _
                    (fun oldObs newObs =>
                       forall obsIdx,
                         @refineObserver oldRep newRep SiR _ _
                                         (getObsDef oldObs obsIdx)
                                         (getObsDef newObs obsIdx))
                    (fun obs obs' => refineADT))
     (@BuildADT oldRep mutSigs obsSigs)
     (@BuildADT newRep mutSigs obsSigs).
 Proof.
   unfold Proper, respectful_hetero; intros.
   let A := match goal with |- refineADT ?A ?B => constr:(A) end in
   let B := match goal with |- refineADT ?A ?B => constr:(B) end in
   eapply (@refinesADT _ A B SiR);
     unfold id, pointwise_relation in *; simpl in *; intros; eauto.
 Qed.

Add Parametric Morphism rep mutSigs obsSigs
: (@BuildADT rep mutSigs obsSigs)
    with signature
    (fun oldMuts newMuts =>
       forall mutIdx, @refineMutator _ _ eq _
                                  (getMutDef oldMuts mutIdx)
                                  (getMutDef newMuts mutIdx))
      ==> (fun oldObs newObs =>
             forall obsIdx, @refineObserver _ _ eq _ _
                                         (getObsDef oldObs obsIdx)
                                         (getObsDef newObs obsIdx))
      ==> refineADT
      as refineADT_BuildADT_Both.
Proof.
  intros; eapply refineADT_BuildADT_Rep; eauto; reflexivity.
Qed.
