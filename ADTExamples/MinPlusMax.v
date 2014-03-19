Require Import Common String ADT ADTRefinement.Specs.
Require Import ADTRefinement ADTCache ADTRepInv Pick ADTHide DelegateMethods.
Require Import ADTExamples.BinaryOperationSpec ADTExamples.CombineBinaryOperationsSpec
        ADTRefinement.BuildADTRefinements ADTRefinement.BuildADTSetoidMorphisms.

Section MinMaxExample.

  Definition MinMaxSig : ADTSig :=
    ADTsignature {
        "Insert" : rep × nat → rep ;
        "Min" : rep × nat → nat ,
        "Max" : rep × nat → nat
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

  Lemma extract_MinMaxSiR :
    exists SiR : multiset -> Rep MinMaxImpl -> Prop,
      (forall idx : ObserverIndex MinMaxSig,
         refineObserver SiR (ObserverMethods MinMaxSpec idx)
                        (ObserverMethods MinMaxImpl idx)) /\
            (forall idx : MutatorIndex MinMaxSig,
               refineMutator SiR (MutatorMethods MinMaxSpec idx)
                             (MutatorMethods MinMaxImpl idx)).
  Proof.
    inversion refineMinMax; subst; eauto.
  Defined.

  Definition foo idx :
    fst (ObserverDomCod (CombTwoOpCollectionSig "MinPlusMax") idx) ->
    nat.
  Proof.
    destruct idx; inversion s_bounded.
    simpl.
    caseEq (obsSig_eq ("MinPlusMax" : rep × nat → nat) bounded_s); eauto.
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
    caseEq (obsSig_eq ("MinPlusMax" : rep × nat → nat) bounded_s); eauto.
    elimtype False.
    inversion sbound; simpl in *; subst.
    unfold obsSig_eq in H; find_if_inside; eauto; discriminate.
    eauto.
  Defined.

  Definition delegateADTSiR (or : multiset) (nr : multiset * Rep MinMaxImpl) :=
    or = fst nr.

  Ltac autorefine :=
    unfold repInvSiR in *|-*;
    subst; split_and; intros;
    autorewrite with refine_monad;
    eauto 50 with cache_refinements typeclass_instances;
    match goal with
        |- refine _ (ret _) => let v := fresh in
                               let CompV := fresh in
                               intros v CompV; apply computes_to_inv in CompV;
                               subst; econstructor; intros; eauto
      | _ => idtac
    end.

  Tactic Notation "hone''" "observer" constr(obsIdx) "using" open_constr(obsBod) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutSigs :=
        match ASig with
            BuildADTSig ?mutSigs _ => constr:(mutSigs) end in
    let obsSigs :=
        match ASig with
            BuildADTSig _ ?obsSigs => constr:(obsSigs) end in
    let mutDefs :=
        match A with
            BuildADT ?mutDefs _  => constr:(mutDefs) end in
    let obsDefs :=
        match A with
            BuildADT _ ?obsDefs  => constr:(obsDefs) end in
    let Rep' :=
        match A with
            @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
    let MutatorIndex' := eval simpl in (MutatorIndex ASig) in
    let ObserverIndex' := eval simpl in (ObserverIndex ASig) in
    let ObserverDomCod' := eval simpl in (ObserverDomCod ASig) in
    let obsIdxB := eval simpl in
    (@Build_BoundedString (List.map obsID obsSigs) obsIdx _) in
        eapply SharpenStep;
      [ eapply (refineADT_BuildADT_ReplaceObserver_generic_ex
                  mutDefs obsDefs obsIdxB
                  (@Build_obsDef Rep'
                                 {| obsID := obsIdx;
                                    obsDom := fst (ObserverDomCod' obsIdxB);
                                    obsCod := snd (ObserverDomCod' obsIdxB)
                                 |}
                                 obsBod))
      | ];
      cbv beta in *; simpl in * .

  Tactic Notation "hone''" "observer" constr(obsIdx) :=
    hone'' observer obsIdx using _.

  Tactic Notation "hone''" "mutator" constr(mutIdx) "using" open_constr(mutBod) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutSigs :=
        match ASig with
            BuildADTSig ?mutSigs _ => constr:(mutSigs) end in
    let obsSigs :=
        match ASig with
            BuildADTSig _ ?obsSigs => constr:(obsSigs) end in
    let mutDefs :=
        match A with
            BuildADT ?mutDefs _  => constr:(mutDefs) end in
    let obsDefs :=
        match A with
            BuildADT _ ?obsDefs  => constr:(obsDefs) end in
    let Rep' :=
        match A with
            @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
    let MutatorIndex' := eval simpl in (MutatorIndex ASig) in
    let ObserverIndex' := eval simpl in (ObserverIndex ASig) in
    let MutatorDom' := eval simpl in (MutatorDom ASig) in
    let mutIdxB := eval simpl in
    (@Build_BoundedString (List.map mutID mutSigs) mutIdx _) in
        eapply SharpenStep with
        (adt' := ADTReplaceMutDef mutDefs obsDefs mutIdxB
                                  (@Build_mutDef Rep'
                                                 {| mutID := mutIdx;
                                                    mutDom := MutatorDom' mutIdxB
                                                 |}
                                                 mutBod
                                )); cbv beta in *; simpl in * .

  Arguments delegateADTSiR or nr / .

  Definition MinPlusMaxImpl (defaultValue : nat)
  : Sharpened MinPlusMaxSpec.
  Proof.
    (** Add a MinMax instance to the representation so we can delegate to it. *)
    hone' representation using delegateADTSiR.
    (* Implement the Insert Mutator.  *)
    hone'' mutator "Insert"%string using
          (fun r x =>
           r1 <- MutatorMethods MinPlusMaxSpec {| bounded_s := "Insert"%string |} (fst r) x;
           r2 <- MutatorMethods MinMaxImpl {|bounded_s := "Insert"%string |} (snd r) x;
           ret (r1, r2)).
    - destruct extract_MinMaxSiR as [MinMaxSiR [refineMinMaxObs refineMinMaxMut] ].
      eapply refineADT_BuildADT_Rep with
      (SiR := fun (or nr : Rep MinPlusMaxSpec * Rep MinMaxImpl) =>
                or = nr /\
                MinMaxSiR (fst nr) (snd nr)).
      unfold getMutDef; simpl; unfold ith_obligation_2; simpl.
      intros mutIdx r_o r_n; find_if_inside; intros; intuition;
      subst; simpl; autorefine.
      unfold refine; intros; inversion_by computes_to_inv; subst;
      econstructor.
      econstructor; intros; subst; eexists; split.
      econstructor; eauto.
      instantiate (1 := (x, x0)); reflexivity.
      econstructor; split; eauto.
      generalize (refineMinMaxMut {| bounded_s := "Insert"%string |} _ _ n H1 _ H2);
        simpl; unfold getMutDef; simpl; intros.
      inversion_by computes_to_inv; unfold add_spec in *.
      assert (x1 = x) by
          (apply functional_extensionality;
           intros; rewrite H0, H3; reflexivity).
      rewrite H in H4; assumption.
      intros; unfold refineObserver; intros; intuition; subst;
      reflexivity.
    - (** Implement the MinPlusMax Observer. *)
      hone'' observer "MinPlusMax"%string.
      Print refineADT.
      (** TODO: Write small manual inversion tactic to pick up hypothesis automatically *)
      inversion_clear refineMinMax.
      exists (fun a b => fst a = fst b /\ SiR (fst a) (snd a) /\ SiR (fst b) (snd b)).
      unfold ith_obligation_2 in *; simpl in *.
      repeat split; intros; simpl.
      specialize (H {| bounded_s := "Insert" |}).
      pose proof (H0 {| bounded_s := "Min" |}) as H0'.
      specialize (H0 {| bounded_s := "Max" |}).
      revert H H0 H0'.
      simpl.
      find_if_inside; simpl.
      intros.
      split_and; destruct_head prod; subst.
      repeat (setoid_rewrite refineEquiv_bind_bind || setoid_rewrite refineEquiv_bind_unit || setoid_rewrite refineEquiv_unit_bind).
      simpl in *.
      eapply refine_bind; [ reflexivity | intro ].
      (** HERE *)

      admit.
      admit.
      admit.


      unfold two_op_spec.



      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite
      autorewrite with refine_monad.
let P := match goal with |- ex ?P => constr:(P) end in
      refine (match refineMinMax in (return ex P with
                | @refinesADT _ _ SiR _ _ => ex_intro P SiR _
              end).

      let G := match goal with |- ?G => constr:(G) end in
      pose (fun SiR => (@refineADT_BuildADT_ReplaceObserver_generic _ _ _ _ _ {| bounded_s := "MinPlusMax"%string |} _ _ SiR _ _: G)).
      Print refineADT.
      match refineMinMax return (
           (fun (r : Rep MinPlusMaxSpec * Rep MinMaxImpl)
                n =>
              (min <- (ObserverMethods MinMaxImpl
                                       {|bounded_s := "Min"%string |} (snd r) n);
               max <- (ObserverMethods MinMaxImpl
                                       {|bounded_s := "Max"%string |} (snd r) n);
               ret ((min + max)))%comp).
    destruct extract_MinMaxSiR as [MinMaxSiR [refineMinMaxObs refineMinMaxMut] ].
    eapply refineADT_BuildADT_Rep with
    (SiR := fun (or nr : Rep MinPlusMaxSpec * Rep MinMaxImpl) =>
              or = nr /\
              MinMaxSiR (fst nr) (snd nr)).
    Focus 2.
    unfold getObsDef; simpl; intros.


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
