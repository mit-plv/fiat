Require Import Common String ADT ADT.Specs ADTNotation.
Require Import ADTRefinement ADTCache ADTRepInv ADT.Pick ADT.ADTHide ADTRefinement.Refinements.DelegateMethods.
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
  Let SiR := SiR refineMinMax.

  Definition MinMaxSiR (or : multiset) (nr : Rep MinMaxImpl) :=
    SiR or nr.

  Lemma refineObserver_MinMaxSiR
  : forall idx : ObserverIndex MinMaxSig,
      refineObserver SiR (ObserverMethods MinMaxSpec idx)
                     (ObserverMethods MinMaxImpl idx).
  Proof.
    destruct refineMinMax; eauto.
  Qed.
  Lemma refineMutator_MinMaxSiR
  : forall idx : MutatorIndex MinMaxSig,
      refineMutator SiR (MutatorMethods MinMaxSpec idx)
                    (MutatorMethods MinMaxImpl idx).
  Proof.
    destruct refineMinMax; eauto.
  Qed.

  Hypothesis refineMutatorPreservesSiR
  : forall idx : MutatorIndex MinMaxSig,
      forall x0 k x1 x2 y,
        computes_to (MutatorMethods MinMaxSpec idx x0 k) x1
        -> computes_to (MutatorMethods MinMaxSpec idx x0 k) x2
        -> SiR x1 y
        -> SiR x2 y.

  Lemma helper_SiR_preserved
        (r : {nr : multiset * Rep MinMaxImpl | MinMaxSiR (fst nr) (snd nr)})
        (x : nat)
        (r1 : {v : multiset | {m' : multiset | add_spec (fst (` r)) x m'} ↝ v})
        (r2 : {v : Rep MinMaxImpl |
               (callMut MinMaxImpl "Insert") (snd (` r)) x ↝ v})
  : MinMaxSiR (` r1) (` r2).
  Proof.
    unfold MinMaxSiR in *.
    pose proof (refineMutatorPreservesSiR {| bstring := "Insert" |}) as SiRPreserved.
    clear refineMutatorPreservesSiR; simpl in *.
    abstract (
        destruct_head sig;
        simpl in *;
          inversion_by computes_to_inv;
        let H := fresh in
        pose proof (refineMutator_MinMaxSiR {| bstring := "Insert" |}) as H;
        simpl in *;
          match goal with
            | [ x : _, y : _, z : _ |- _ ] =>
              specialize (H _ _ x y _ z)
          end;
        repeat match goal with
                 | [ H : computes_to _ _ |- _ ] => apply computes_to_inv in H
                 | _ => progress destruct_head ex
                 | _ => progress destruct_head and
               end;
        eapply SiRPreserved;
        solve [ eassumption
              | constructor; eassumption ]
      ).
  Qed.
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
          => pose proof (fun arg =>
                           refineObserver_MinMaxSiR
                             {| bstring := rew_observer_name |}
                             _ _ arg
                             (proj2_sig r_n)) as H';
            simpl in H';
            set_evars;
            instantiate;
            setoid_rewrite H';
            subst_body;
            higher_order_2_reflexivity
      end
    | ].

  Print refineADT_BuildADT_ReplaceMutator.

  Tactic Notation "hone'" "mutator" constr(mutIdx) "using" open_constr(mutBod) :=
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
      eapply SharpenStep;
      [eapply (@refineADT_BuildADT_ReplaceMutator_eq
                 Rep'  _ _ mutDefs obsDefs mutIdxB
                 (@Build_mutDef Rep'
                                {| mutID := mutIdx;
                                   mutDom := MutatorDom' mutIdxB
                                |}
                                mutBod
                                ))
      | idtac]; cbv beta in *; simpl in * .

  Definition MinPlusMaxImpl (defaultValue : nat)
  : Sharpened MinPlusMaxSpec.
  Proof.
    unfold MinPlusMaxSpec; simpl.
    unfold NatTwoBinOpSpec.
    unfold two_op_spec.
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
    hone'' ∑-mutator "Insert"%string using
           (fun (r : {nr : multiset * Rep MinMaxImpl | MinMaxSiR (fst nr) (snd nr)}) x =>
              (r1 <- { v : { v | callMut MinPlusMaxSpec "Insert" (fst (proj1_sig r)) x ↝ v } | True };
               r2 <- { v : { v | callMut MinMaxImpl "Insert" (snd (proj1_sig r)) x ↝ v } | True};
               ret (exist (fun nr => MinMaxSiR (fst nr) (snd nr)) (`r1, `r2) (helper_SiR_preserved _ r1 r2) ))).
    admit.
(*      subst.
      unfold delegateADTSiR; simpl.
      setoid_rewrite remove_forall_eq0.
      setoid_rewrite remove_exists_and_eq0.
      setoid_rewrite refineEquiv_pick_eq'.
      autorewrite with refine_monad.
      eapply refine_pick.
      intros.
      constructor.
      inversion_by computes_to_inv.
      subst; simpl.
      destruct_head sig.
      inversion_by computes_to_inv.
      trivial. } *)
    - finish sharpening.
  Defined.

  (* An attempt to delegate to the reference spec,
     then refine the delegate ADT to the implementation. *)

  Definition delegateSpecSiR (or : multiset)
             (nr : multiset * Rep MinMaxSpec) :=
    or = fst nr /\ or = snd nr.

  Arguments delegateSpecSiR _ _ / .

  Definition delegateImplSiR (or : multiset * multiset)
             (nr : multiset * Rep MinMaxImpl) :=
    fst or = fst nr /\ SiR (snd or) (snd nr).

  Arguments delegateImplSiR _ _ / .

  Lemma refineMinMaxObs {Rep' : Type -> Type}
        {Dom Cod : Type}
        (proj : forall A, Rep' A -> A)
        (SiR' : Rep' (Rep MinMaxSpec) -> Rep' (Rep MinMaxImpl) -> Prop)
        (bod : forall (adt : ADT MinMaxSig),
                 observerMethodType (Rep adt) Dom Cod)
  : (forall or nr, SiR' or nr -> SiR (proj _ or) (proj _ nr))
    -> (refineObserver SiR (bod MinMaxSpec)
                       (bod MinMaxImpl))
    -> refineObserver eq (absObserverMethod SiR' (fun r => (bod MinMaxSpec (proj _ r))))
                   (fun r => bod MinMaxImpl (proj _ r)).
  Proof.
    simpl; intros; subst; econstructor; intros; eauto.
    eapply H0; eauto.
  Qed.

  Lemma refineMinMaxMut {Rep' : Type -> Type}
        {Dom : Type}
        (proj : forall A, Rep' A -> A)
        (SiR' : Rep' (Rep MinMaxSpec) -> Rep' (Rep MinMaxImpl) -> Prop)
        (bod : forall (adt : ADT MinMaxSig),
                 mutatorMethodType (Rep' (Rep adt)) Dom)
  : (refineMutator SiR' (bod MinMaxSpec)
                      (bod MinMaxImpl))
    -> refineMutator eq (absMutatorMethod SiR' (bod MinMaxSpec))
                  (bod MinMaxImpl).
  Proof.
    simpl; intros; subst; econstructor; intros; eauto.
    econstructor; intros.
    generalize (H _ _ _ H1 _ H0); intros; inversion_by computes_to_inv.
    eauto.
  Qed.

  Lemma refine_elim_forall
        {A B : Type}
        (P : A -> Prop)
        (P' : A -> B -> Prop)
        (b : Comp B)
  : (forall a,
       P a
       -> refine {b | P' a b} b)
    -> refine {b | forall a, P a -> P' a b} b.
  Proof.
    intros; econstructor; intros.
    generalize (H _ H1 _ H0); intros; inversion_by computes_to_inv;
    eauto.
  Qed.

  Lemma duplicate_bind {A : Type}
        (a : Comp A)
  : (forall x x', computes_to a x -> computes_to a x' -> x = x')
    -> refineEquiv (a' <- a; ret (a', a'))
                (a' <- a; a'' <- a; ret (a', a'')).
  Proof.
    split; unfold refine; intros; inversion_by computes_to_inv;
    subst; repeat econstructor; subst; eauto.
    erewrite (H _ _ H1 H2); econstructor.
  Qed.

  Tactic Notation "swap" "representation" constr(adt) "with" constr(adt') "under" constr(SiR') :=
    let A := match goal with  |- Sharpened ?A => constr:(A) end in
    lazymatch A with
      | @BuildADT ?Rep' ?mutSigs ?obsSigs ?mutDefs ?obsDefs
        => let ASig := constr:(BuildADTSig mutSigs obsSigs) in
           let MutatorIndex' := (eval simpl in (MutatorIndex ASig)) in
           let ObserverIndex' := (eval simpl in (ObserverIndex ASig)) in
           let ObserverDomCod' := (eval simpl in (ObserverDomCod ASig)) in
           eapply SharpenStep
    end;
  cbv beta in *; simpl in * .


    Lemma swap_rep 
    : 
      forall 
        Sig Sig'
        (ClientADT : ADT Sig -> ADT Sig')
        (adt adt' : ADT Sig)
        (SiR' : Rep (ClientADT adt) -> Rep (ClientADT adt') -> Prop),
      (forall mutIdx : MutatorIndex Sig',
         refineMutator SiR' 
                       (MutatorMethods (ClientADT adt) mutIdx) 
                       (MutatorMethods (ClientADT adt') mutIdx))
      -> (forall obsIdx : ObserverIndex Sig',
            refineObserver SiR' 
                           (ObserverMethods (ClientADT adt) obsIdx) 
                           (ObserverMethods (ClientADT adt') obsIdx))
      -> refineADT (ClientADT adt) (ClientADT adt').
    Proof.
      intros.
      destruct (ClientADT adt); destruct (ClientADT adt').
      eapply refineADT_Build_ADT_Rep with (SiR := SiR'); eauto.
    Qed.

  Definition MinPlusMaxImpl' (defaultValue : nat)
  : Sharpened MinPlusMaxSpec.
  Proof.
    clear refineMutatorPreservesSiR.
    (** Split out the [Pick]s in the MinPlusMax Observer. *)
    unfold MinPlusMaxSpec, NatTwoBinOpSpec, two_op_spec.
    hone' observer "MinPlusMax"%string using _; simpl.
    { intros; subst.
      set_evars. simpl in *.
      setoid_rewrite refineEquiv_split_func_ex2'.
      (* This sequence of tactics is inscrutable. *)
      subst_body.
      rewrite_hyp.
      higher_order_2_reflexivity.
    }
    (** Add a MinMax instance to the representation so we can delegate to it. *)
    hone representation' using delegateSpecSiR.
    (** Rewrite the "Min" and then "Max" [Pick] in the MinPlusMax Observer. *)
    hone' observer "MinPlusMax"%string using _.
    { intros; subst.
      set_evars. simpl in *.
      (* Split the /\ *)
      apply refine_elim_forall; intros; intuition; subst.
      rewrite H2.
      (* Rewrite with a call to Min *)
      replace ({a : nat | bin_op_spec le _ (snd r_n) n a})
      with ((callObs MinMaxSpec "Min") (snd r_n) n) by reflexivity.
      (* Rewrite with a call to Max *)
      replace ({a : nat | bin_op_spec ge _ (snd r_n) n a})
      with ((callObs MinMaxSpec "Max") (snd r_n) n) by reflexivity.
      (* Again, inscrutable. *)
      subst_body.
      rewrite_hyp.
      higher_order_2_reflexivity.
    }
    (* Rewrite insert to use MinMaxSpec's insert. *)
    hone' mutator "Insert"%string using _.
    { intros; subst.
      set_evars. simpl in *.
      setoid_rewrite refineEquiv_pick_eq'; autorewrite with refine_monad.
      apply refine_elim_forall; intros; intuition; subst.
      (* Pull of the first 'Insert' Picks. *)
      rewrite refineEquiv_split_ex.
      rewrite refineEquiv_pick_computes_to_and.
      autorewrite with refine_monad.
      (* Delegate insert to MinMax ADT*)
      rewrite H2.
      replace {m' : multiset | add_spec (snd r_n) n m'}
      with (callMut MinMaxSpec "Insert" (snd r_n) n) by reflexivity.
      (* Clean up second Pick. *)
      setoid_rewrite <- refineEquiv_split_ex.
      setoid_rewrite remove_exists_eql_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      repeat setoid_rewrite refineEquiv_bind_unit.
      rewrite duplicate_bind;
        [ | simpl; intros; inversion_by computes_to_inv;
          apply functional_extensionality; intros; rewrite H0, H1;
          reflexivity].
      rewrite <- H2 at 1.
      subst_body.
      higher_order_2_reflexivity.
    }
    (* Swap representations. *)
    eapply SharpenStep.
    (* Do the swap. We should have a 'swap representation' 
       tactic  to do the pattern matching. *)
    eapply (@swap_rep MinMaxSig _
                          (fun adt => 
                             (ADTRep (multiset * Rep adt)
      { def mut "Insert" (p : rep, n: nat) : rep := 
          a' <- (callMut MinPlusMaxSpec "Insert") (fst p) n;
          a'' <- (callMut adt "Insert") (snd p) n;
          ret (a', a'') ;
        def obs "MinPlusMax" (p : rep, n : nat) : nat := 
          {b : nat |
          (a <- (callObs adt "Min") (snd p) n ;
           a' <- (callObs adt "Max") (snd p) n;
           ret (a + a')) ↝ b}  })%ADT) MinMaxSpec MinMaxImpl
           delegateImplSiR).
    (* Show the mutator swap is valid. This is fairly boilerplate. *)
    {
      intros; simpl; unfold ith_obligation_1, ith_obligation_2; simpl.
      destruct mutIdx as  [ ? [ [? | [ ] ] ] ]; subst; simpl.
      intros; intuition; subst.
      setoid_rewrite <- (refineMutator_MinMaxSiR {| bstring := "Insert"%string |} _ _ n H1).
      rewrite H0; autorewrite with refine_monad.
      repeat (f_equiv; unfold pointwise_relation; intros;
              autorewrite with refine_monad; simpl). 
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor; simpl; auto.
    }
    (* Show the observer swap is valid. This is fairly boilerplate. *)
    {
      intros; simpl; unfold ith_obligation_1, ith_obligation_2; simpl.
      destruct obsIdx as  [ ? [ [? | [ ] ] ] ]; subst; simpl. 
      intros; intuition; subst.
      repeat rewrite refineEquiv_pick_computes_to.
      rewrite (refineObserver_MinMaxSiR {| bstring := "Min"%string |} _ _ n H1).
      f_equiv; unfold pointwise_relation; intros.
      autorewrite with refine_monad; simpl;
      rewrite (refineObserver_MinMaxSiR {| bstring := "Max"%string |} _ _ n H1); f_equiv.
    }
    - finish sharpening.
  Defined.

  (* Show the term derived above as a sanity check. *)
  Goal (forall b, ObserverMethods (projT1 (MinPlusMaxImpl' 0))
                                 {| bstring := "MinPlusMax" |} = b).
  intros; simpl.
  unfold ObserverMethods; cbv beta.
  Abort.


  (* Show the term derived above as a sanity check. *)
  Goal (forall b, ObserverMethods (projT1 (MinPlusMaxImpl 0))
                                 {| bstring := "MinPlusMax" |} = b).
    simpl.
  Abort.
  Goal (forall b, MutatorMethods (projT1 (MinPlusMaxImpl 0))
                                 {| bstring := "Insert" |} = b).
    simpl.
  Abort.

End MinMaxExample.
