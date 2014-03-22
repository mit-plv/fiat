Require Import Common String ADT ADTRefinement.Specs ADTNotation.
Require Import ADTRefinement ADTCache ADTRepInv Pick ADTHide DelegateMethods.
Require Import ADTExamples.BinaryOperationSpec ADTExamples.CombineBinaryOperationsSpec
        ADTRefinement.BuildADTRefinements.HoneRepresentation ADTRefinement.GeneralBuildADTRefinements
        ADTRefinement.BuildADTSetoidMorphisms.

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
    ADTRep multiset {
             def mut "Insert" ( m : rep , n : nat ) : rep :=
               {m' | add_spec m n m'}%comp ;
             def obs "Min" (m : rep , n : nat ) : nat :=
                 {n' | bin_op_spec le defaultSpec m n n'}%comp ,
             def obs "Max" (m : rep , n : nat ) : nat :=
                 {n' | bin_op_spec ge defaultSpec m n n'}%comp
           }%ADT .

  Variable MinMaxImpl : ADT MinMaxSig.
  Variable refineMinMax : refineADT MinMaxSpec MinMaxImpl.

  Definition MinMaxSiR (or : multiset) (nr : Rep MinMaxImpl) :=
    exists SiR : multiset -> Rep MinMaxImpl -> Prop,
      SiR or nr /\
      (forall idx : ObserverIndex MinMaxSig,
         refineObserver SiR (ObserverMethods MinMaxSpec idx)
                        (ObserverMethods MinMaxImpl idx)) /\
      (forall idx : MutatorIndex MinMaxSig,
         refineMutator SiR (MutatorMethods MinMaxSpec idx)
                       (MutatorMethods MinMaxImpl idx)).
  (*
  Inductive type_SiR {Sig} {A B : ADT Sig} (P : (Rep A -> Rep B -> Prop) -> Prop) : refineADT A B -> Type
    := Build_type_SiR : forall SiR H0 H1,
                          P SiR
                          -> type_SiR P (@refinesADT _ A B SiR H0 H1).

  Global Instance trunc_type_SiR {Sig A B} (P : _ -> Prop)
         `{forall R, IsHProp (P R)}
         rH
  : IsHProp (@type_SiR Sig A B P rH).
  Proof.
    apply hprop_allpath.
    intros x y.
    destruct x.
    inversion y.

  Definition MinMaxSiR (or : Rep MinMaxSpec) (nr : Rep MinMaxImpl) (H : refineADT MinMaxSpec MinMaxImpl) :=
    inhabited (type_SiR (fun SiR => SiR or nr) H).*)

  Definition delegateADTSiR (or : multiset)
             (nr : { nr : multiset * Rep MinMaxImpl
                   | MinMaxSiR (fst nr) (snd nr)(* refineMinMax*) }) :=
    or = fst (proj1_sig nr).

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
    let A := match goal with  |- Sharpened ?A => constr:(A) end in
    lazymatch A with
      | @BuildADT ?Rep' ?mutSigs ?obsSigs ?mutDefs ?obsDefs
        => let ASig := constr:(BuildADTSig mutSigs obsSigs) in
           let MutatorIndex' := (eval simpl in (MutatorIndex ASig)) in
           let ObserverIndex' := (eval simpl in (ObserverIndex ASig)) in
           let ObserverDomCod' := (eval simpl in (ObserverDomCod ASig)) in
           let obsIdxB := (eval simpl in (@Build_BoundedString (List.map obsID obsSigs) obsIdx _)) in
           eapply SharpenStep;
             [ eapply (refineADT_BuildADT_ReplaceObserver_generic
                         mutDefs obsDefs obsIdxB
                         (@Build_obsDef Rep'
                                        {| obsID := obsIdx;
                                           obsDom := fst (ObserverDomCod' obsIdxB);
                                           obsCod := snd (ObserverDomCod' obsIdxB)
                                        |}
                                        obsBod))
             | ]
    end;
  cbv beta in *; simpl in * .

  Tactic Notation "hone''" "∑-observer" constr(obsIdx) "using" open_constr(obsBod) :=
    let A := match goal with  |- Sharpened ?A => constr:(A) end in
    lazymatch A with
      | @BuildADT ?Rep' ?mutSigs ?obsSigs ?mutDefs ?obsDefs
        => let RepInv := lazymatch (eval hnf in Rep') with sig ?P => constr:(P) end in
           let ASig := constr:(BuildADTSig mutSigs obsSigs) in
           let MutatorIndex' := (eval simpl in (MutatorIndex ASig)) in
           let ObserverIndex' := (eval simpl in (ObserverIndex ASig)) in
           let ObserverDomCod' := (eval simpl in (ObserverDomCod ASig)) in
           let obsIdxB := (eval simpl in (@Build_BoundedString (List.map obsID obsSigs) obsIdx _)) in
           eapply SharpenStep;
             [ eapply (refineADT_BuildADT_ReplaceObserver_sigma
                         mutDefs obsDefs obsIdxB
                         (@Build_obsDef Rep'
                                        {| obsID := obsIdx;
                                           obsDom := fst (ObserverDomCod' obsIdxB);
                                           obsCod := snd (ObserverDomCod' obsIdxB)
                                        |}
                                        obsBod))
             | ]
    end;
  cbv beta in *; simpl in * .

  Tactic Notation "hone''" "∑-observer" constr(obsIdx) :=
    hone'' ∑-observer obsIdx using _.

  Tactic Notation "hone''" "observer" constr(obsIdx) "under" constr(refineADT_with_SiR) "using" open_constr(obsBod) :=
    hone'' observer obsIdx using obsBod;
  [ (*let H' := fresh "SiR" in
    pose proof refineADT_with_SiR as H'; revert H';
    refine (refineADT_SiR_elim _);
    intro H';
    exists H'*)
    exists (SiR refineADT_with_SiR)
  | ].


  Tactic Notation "hone''" "observer" constr(obsIdx) :=
    hone'' observer obsIdx using _.

  Tactic Notation "hone''" "observer" constr(obsIdx) "under" constr(refineADT_with_SiR) :=
    hone'' observer obsIdx under refineADT_with_SiR using _.

  Tactic Notation "hone''" "∑-mutator" constr(mutIdx) "using" open_constr(mutBod) :=
    let A := match goal with  |- Sharpened ?A => constr:(A) end in
    lazymatch A with
      | @BuildADT ?Rep' ?mutSigs ?obsSigs ?mutDefs ?obsDefs
        => let RepInv := lazymatch (eval hnf in Rep') with sig ?P => constr:(P) end in
           let ASig := constr:(BuildADTSig mutSigs obsSigs) in
           let MutatorIndex' := (eval simpl in (MutatorIndex ASig)) in
           let MutatorDom' := (eval simpl in (MutatorDom ASig)) in
           let mutIdxB := (eval simpl in (@Build_BoundedString (List.map mutID mutSigs) mutIdx _)) in
           eapply SharpenStep;
             [ eapply (refineADT_BuildADT_ReplaceMutator_eq
                         mutDefs obsDefs mutIdxB
                         (@Build_mutDef Rep'
                                        {| mutID := mutIdx;
                                           mutDom := MutatorDom' mutIdxB
                                        |}
                                        mutBod))
             | ]
    end;
  cbv beta in *; simpl in * .

  Tactic Notation "hone''" "∑-mutator" constr(mutIdx) :=
    hone'' ∑-mutator mutIdx using _.


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

  Ltac higher_order_2_reflexivity :=
    let x := match goal with |- ?R ?x (?f ?a ?b) => constr:(x) end in
    let f := match goal with |- ?R ?x (?f ?a ?b) => constr:(f) end in
    let a := match goal with |- ?R ?x (?f ?a ?b) => constr:(a) end in
    let b := match goal with |- ?R ?x (?f ?a ?b) => constr:(b) end in
    let x' := (eval pattern a, b in x) in
    let f' := match x' with ?f' _ _ => constr:(f') end in
    unify f f';
      cbv beta;
      reflexivity.

  Tactic Notation "dubiously" "specialized" "hone" "∑-observer" constr(observer_name) "rewriting" "with" "observer" constr(rew_observer_name) :=
    hone'' ∑-observer observer_name;
    [ intros;
      rewrite_hyp; clear;
      let SiR := fresh "SiR" in
      let H := fresh "H" in
      let H' := fresh "H'" in
      lazymatch goal with
        | [ r_n : sig _ |- _ ]
          => destruct (proj2_sig r_n) as [SiR [H [H' ?]]];
            specialize (fun arg => H' {| bstring := rew_observer_name |} _ _ arg H);
            simpl in H';
            set_evars;
            instantiate;
            setoid_rewrite H';
            subst_body;
            higher_order_2_reflexivity
      end
    | ].

  Definition MinPlusMaxImpl (defaultValue : nat)
  : Sharpened MinPlusMaxSpec.
  Proof.
    (** Add a MinMax instance to the representation so we can delegate to it. *)
    hone representation' using delegateADTSiR.
    (** Split out the [Pick]s in the MinPlusMax Observer. *)
    hone'' ∑-observer "MinPlusMax"%string.
    { intros.
      set_evars; simpl in *.
      unfold two_op_spec.
      unfold delegateADTSiR; simpl.
      setoid_rewrite remove_forall_eq0.
      setoid_rewrite refineEquiv_pick_computes_to.
      setoid_rewrite refineEquiv_split_func_ex2'.
      subst_body.
      rewrite_hyp.
      higher_order_2_reflexivity. }
    (** Rewrite the "Min" and then "Max" [Pick] in the MinPlusMax Observer. *)
    dubiously specialized hone ∑-observer "MinPlusMax"%string  rewriting with observer "Min"%string.
    dubiously specialized hone ∑-observer "MinPlusMax"%string  rewriting with observer "Max"%string.
    hone'' ∑-mutator "Insert"%string.
    { intros.
      subst.
      set_evars; simpl in *.
      unfold two_op_spec.
      unfold delegateADTSiR; simpl.
      setoid_rewrite remove_forall_eq0.
      setoid_rewrite remove_exists_and_eq0.
      setoid_rewrite refineEquiv_pick_eq'.
      autorewrite with refine_monad.
      subst_body.
      higher_order_2_reflexivity. }
     (*
      destruct refineMinMax.
      SearchAbout refineEquiv Pick eq.
      setoid_rewrite refineEquiv_pick_computes_to.
      setoid_rewrite refineEquiv_split_func_ex2'.
      subst_body.
      rewrite_hyp.
      simpl in *.
      unfold delegateADTSiR; simpl; subst.
      set_evars.
      lazymatch goal with |- refine _ (?f _ _) => is_evar f; set (H' := f) end.
      setoid_rewrite remove_forall_eq0.
      se
    (* TODO: Implement the Insert Mutator. *)
    (*** HERE *)
    (** Idea: do it the same way we split out the picks in the observer *)
    hone'' mutator "Insert"%string using
          (fun (r : {nr : multiset * Rep MinMaxImpl | MinMaxSiR (fst nr) (snd nr)}) x =>
             r1 <- callMut MinPlusMaxSpec "Insert" (fst (proj1_sig r)) x;
           r2 <- callMut MinMaxImpl "Insert" (snd (proj1_sig r)) x;
           ret (ex_intro (fun nr => MinMaxSiR (fst nr) (snd nr)) (r1, r2) _ )).
    intros; subst.
    simpl.
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


      setoid_rewrite remove_forall_eq'.




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
      simpl; unfold getObsDef; simpl; intros; inversion_by computes_to_inv; eauto. *)
    - finish sharpening.
  Defined.

  (* Show the term derived above as a sanity check. *)
  Goal (forall b, ObserverMethods (projT1 (MinPlusMaxImpl 0))
                                 {| bstring := "MinPlusMax" |} = b).
    simpl.
  Abort.

End MinMaxExample.
