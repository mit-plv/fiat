Require Import Common Computation ADT Ensembles ADTHide.
Require Import ADTRefinement.Core.

Add Parametric Morphism
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
  unfold impl.
  intros; inversion H; inversion H0; subst;
  unfold HideADT in *; destruct x; destruct y;
  destruct oldADT; simpl in *.
  econstructor 1 with
  (SiR := fun r_o r_n =>
            exists r_n', SiR0 r_o r_n' /\ SiR r_n' r_n);
    simpl; intros.
  - destruct_ex; intuition.
    rewrite <- H1, <- H5; eauto.
    autorewrite with refine_monad; f_equiv;
    unfold pointwise_relation; intros.
    econstructor; inversion_by computes_to_inv; eauto.
  - destruct_ex; intuition.
    rewrite <- H2, <- H6; eauto; reflexivity.
Qed.
