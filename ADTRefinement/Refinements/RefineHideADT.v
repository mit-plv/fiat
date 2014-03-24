Require Import Common Computation ADT Ensembles ADTHide.
Require Import ADTRefinement.Core.

Lemma RefineHideADT'
      extSig'
      oldMutatorIndex oldObserverIndex
      (MutatorMap : oldMutatorIndex -> MutatorIndex extSig')
      (ObserverMap : oldObserverIndex -> ObserverIndex extSig')
      oldADT
: forall newADT newADT',
    refineADT newADT newADT'
    -> arrow (refineADT oldADT (HideADT MutatorMap ObserverMap newADT))
             (refineADT oldADT (HideADT MutatorMap ObserverMap newADT')).
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
    rewrite_rev_hyp; eauto; reflexivity.
Qed.

Definition RefineHideADT := RefineHideADT'.

(*Add Parametric Morphism
    extSig'
    oldMutatorIndex oldObserverIndex
    (MutatorMap : oldMutatorIndex -> MutatorIndex extSig')
    (ObserverMap : oldObserverIndex -> ObserverIndex extSig')
    oldADT
: (fun newADT => refineADT oldADT (HideADT MutatorMap ObserverMap newADT))
    with signature
    refineADT ==> impl
as RefineHideADT.
Proof.
  unfold impl; intros; apply RefineHideADT'.
Qed.*)
