Require Import Fiat.Common
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADT.ADTHide
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.SetoidMorphisms.

Lemma RefineHideADT
      extSig'
      oldMethodIndex
      (MethodMap : oldMethodIndex -> MethodIndex extSig')
      oldADT
: forall newADT newADT',
    refineADT newADT newADT'
    -> arrow (refineADT oldADT (HideADT MethodMap newADT))
             (refineADT oldADT (HideADT MethodMap newADT')).
Proof.
  unfold arrow.
  intros ? ? [AbsR ?] [AbsR' ?].
  destruct_head ADT.
  exists (fun r_o r_n => exists r_n', AbsR' r_o r_n' /\ AbsR r_n' r_n);
    simpl; intros.
  - eauto using refineMethod_trans.
Qed.
