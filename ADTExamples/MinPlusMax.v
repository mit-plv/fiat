Require Import Common String ADT ADTRefinement.Specs.
Require Import ADTRefinement ADTCache ADTRepInv Pick ADTHide DelegateMethods.
Require Import ADTExamples.BinaryOperationSpec ADTExamples.CombineBinaryOperationsSpec.

Section MinMaxExample.

  Definition MinMaxSig : ADTSig :=
    ADTsignature {
        "Insert" : rep ✕ nat → rep ;
        "Min" : rep ✕ nat → nat ,
        "Max" : rep ✕ nat → nat
      }%ADTSig.

  Definition defaultSpec : nat -> Prop := fun _ => True.

  Definition MinMaxSpec 
  : ADT MinMaxSig :=
    ADTRep multiset `[
             def "Insert" `[ m `: rep , n `: nat ]` : rep :=
               {m' | add_spec m n m'}%comp ;
             def "Min" `[m `: rep , n `: nat ]` : nat :=
                 {n' | bin_op_spec le defaultSpec m n n'}%comp ,
             def "Max" `[m `: rep , n `: nat ]` : nat :=
                 {n' | bin_op_spec ge defaultSpec m n n'}%comp
           ]`%ADT .

  Variable MinMaxImpl : ADT MinMaxSig.
  Variable refineMinMax : refineADT MinMaxSpec MinMaxImpl.

  Definition foo idx : 
    fst (ObserverDomCod (CombTwoOpCollectionSig "MinPlusMax") idx) -> 
    nat.
  Proof.
    destruct idx; inversion s_bounded.
    simpl.
    caseEq (obsSig_eq ("MinPlusMax" : rep ✕ nat → nat) bounded_s); eauto.
    elimtype False.
    inversion sbound; simpl in *; subst.
    unfold obsSig_eq in H; find_if_inside; eauto; discriminate.
    eauto.
  Defined.

  Definition bar idx : 
    nat -> 
    snd (ObserverDomCod (CombTwoOpCollectionSig "MinPlusMax") idx).
  Proof.
    destruct idx; inversion s_bounded.
    simpl.
    caseEq (obsSig_eq ("MinPlusMax" : rep ✕ nat → nat) bounded_s); eauto.
    elimtype False.
    inversion sbound; simpl in *; subst.
    unfold obsSig_eq in H; find_if_inside; eauto; discriminate.
    eauto.
  Defined.

  Definition MinPlusMaxImpl (defaultValue : nat)
  : Sharpened MinPlusMaxSpec.
  Proof.
    eapply SharpenStep.
    eapply refineADT_DelegatedMethods with 
    (delegateDomCod := ObserverDomCod MinMaxSig)
    (delegateADT := MinMaxImpl).
    eapply SharpenStep with (adt' := 
                               {|
     Rep := Rep MinPlusMaxSpec * Rep MinMaxImpl;
     MutatorMethods := fun
                         (idx : MutatorIndex
                                  (CombTwoOpCollectionSig "MinPlusMax"))
                         (r : Rep MinPlusMaxSpec * Rep MinMaxImpl)
                         (x : MutatorDom
                                (CombTwoOpCollectionSig "MinPlusMax") idx) =>
                       r1 <- MutatorMethods MinPlusMaxSpec idx (fst r) x;
                       r2 <- MutatorMethods MinMaxImpl idx (snd r) x;
                       ret (r1, r2);
     ObserverMethods := fun
                          (idx : ObserverIndex
                                   (CombTwoOpCollectionSig "MinPlusMax"))
                          (r : Rep MinPlusMaxSpec * Rep MinMaxImpl) 
                          n =>
                         (min <- (ObserverMethods MinMaxImpl
                                                  {|bounded_s := "Min"%string |} (snd r) (foo _ n));
                          max <- (ObserverMethods MinMaxImpl
                                                  {|bounded_s := "Max"%string |} (snd r) (foo _ n));
                          ret (bar idx (min + max)))%comp |}).
    assert (exists SiR : multiset -> Rep MinMaxImpl -> Prop,
              (forall idx : ObserverIndex MinMaxSig,
                refineObserver SiR (ObserverMethods MinMaxSpec idx)
                               (ObserverMethods MinMaxImpl idx)) /\
              (forall idx : MutatorIndex MinMaxSig,
                  refineMutator SiR (MutatorMethods MinMaxSpec idx)
                                 (MutatorMethods MinMaxImpl idx))).
    inversion refineMinMax; eauto.
    clear refineMinMax; destruct H as [SiR [refineMinMaxObs refineMinMaxMut] ].
    eapply refineADT_Build_ADT_Rep with 
    (SiR := fun (or nr : Rep MinPlusMaxSpec * Rep MinMaxImpl) => 
              or = nr /\
              SiR (fst nr) (snd nr)).
    - intro.
      assert (exists pf,
                mutIdx = {| bounded_s := "Insert"%string;
                            s_bounded := pf |}) as mutIdx_eq by 
          (clear;
           destruct mutIdx; destruct s_bounded; inversion sbound; 
           subst; simpl; 
           [ exists {| sbound := sbound |}; reflexivity
                  | inversion H ]) ;
      destruct mutIdx_eq as [pf mutIdx_eq]; rewrite mutIdx_eq.
      unfold refineMutator; intros; intuition; subst.
      unfold refine; intros; econstructor; eauto.
      econstructor; split; eauto.
      inversion_by computes_to_inv; subst; simpl.
      generalize (refineMinMaxMut _  _ _ n H1 _ H2); intros.
      inversion_by computes_to_inv.
      unfold getMutDef in H0, H3; simpl in H0, H3.
      inversion_by computes_to_inv.
      unfold add_spec in *.
      assert (x1 = x) by 
          (apply functional_extensionality;
           intros; rewrite H0, H3; reflexivity).
      rewrite H in H4; assumption.
    - intro; 
      assert (exists pf,
                 obsIdx = {| bounded_s := "MinPlusMax"%string;
                            s_bounded := pf |}) as obsIdx_eq by 
          (clear;
           destruct obsIdx; destruct s_bounded; inversion sbound; 
           subst; simpl; 
           [ exists {| sbound := sbound |}; reflexivity
                  | inversion H ]) ;
      destruct obsIdx_eq as [pf obsIdx_eq]; rewrite obsIdx_eq.
      simpl; intros; intuition; subst; unfold getObsDef; simpl.
      unfold two_op_spec, refine; intros.
      apply computes_to_inv in H; destruct_ex; intuition.
      apply computes_to_inv in H2; destruct_ex; intuition.
      apply computes_to_inv in H3; destruct_ex; intuition.
      destruct pf; subst.
      econstructor; eexists x; split; eauto.
      generalize (refineMinMaxObs {|bounded_s := "Min" |} _ _ _ H1 _ H0).
      simpl; unfold getObsDef; simpl; intros; inversion_by computes_to_inv; eauto.
      eexists x0; split; eauto.
      generalize (refineMinMaxObs {|bounded_s := "Max" |} _ _ _ H1 _ H2).
      simpl; unfold getObsDef; simpl; intros; inversion_by computes_to_inv; eauto.
    - finish sharpening.
  Defined.

  (* Show the term derived above as a sanity check. *)
  Goal (forall b, ObserverMethods (proj1_sig (MinPlusMaxImpl 0)) 
                                 {| bounded_s := "MinPlusMax" |} = b).
    simpl.
  Abort.

End MinMaxExample.
