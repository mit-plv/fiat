Require Import Common 
        ADT.ADTSig ADT.Core ADT.ADTHide
        ADTRefinement.Core.

Lemma RefineHideADT
      extSig'
      oldConstructorIndex oldMethodIndex
      (ConstructorMap : oldConstructorIndex -> ConstructorIndex extSig')
      (MethodMap : oldMethodIndex -> MethodIndex extSig')
      oldADT
: forall newADT newADT',
    refineADT newADT newADT'
    -> arrow (refineADT oldADT (HideADT ConstructorMap MethodMap newADT))
             (refineADT oldADT (HideADT ConstructorMap MethodMap newADT')).
Proof.
  unfold arrow.
  intros ? ? [SiR ? ?] [SiR' ? ?].
  destruct_head ADT.
  exists (fun r_o r_n => exists r_n', SiR' r_o r_n' /\ SiR r_n' r_n);
    simpl; intros.
  - destruct_ex; intuition.
    rewrite_rev_hyp; try eassumption; [].
    autorewrite with refine_monad; f_equiv;
    unfold pointwise_relation; intros.
    econstructor; inversion_by computes_to_inv; eauto.
  - destruct_ex; intuition.
    rewrite_rev_hyp; try eassumption; [].
    autorewrite with refine_monad; f_equiv;
    unfold pointwise_relation; intros.
    intros v Comp_v; inversion_by computes_to_inv; subst; simpl in *; 
    eauto.
Qed.
