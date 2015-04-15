Require Import Common String ADT ADT.Specs ADTNotation.
Require Import ADTRefinement ADTCache ADTRepInv ADT.Pick ADT.ADTHide ADTRefinement.Refinements.DelegateMethods.
Require Import Examples.BinaryOperationSpec Examples.CombineBinaryOperationsSpec
        ADTRefinement.BuildADTRefinements.HoneRepresentation ADTRefinement.GeneralBuildADTRefinements
        ADTRefinement.BuildADTSetoidMorphisms.
Require Import LogicLemmas Coq.Classes.Morphisms_Prop.

Section Delegate.
  Variable rep : Type. (** The old representation type. *)
  Variable delegateRep : Type. (** The new representation type. *)

  (** The relation between the two representations. *)
  Variable R : rep -> delegateRep -> Prop.

  Variable mutSigs : list mutSig.
  Variable obsSigs : list obsSig.
  Variable mutDefs : ilist (@mutDef rep) mutSigs.
  Variable obsDefs : ilist (@obsDef rep) obsSigs.

  (*Variable delegateMutSigs : list mutSig.*)
  (** The delegate must have the same mutators. *)
  (** TODO: generalize this to more mutators. *)
  Variable delegateObsSigs : list obsSig.
  Variable delegateMutDefs : ilist (@mutDef delegateRep) mutSigs.
  Variable delegateObsDefs : ilist (@obsDef delegateRep) delegateObsSigs.

  Definition combinedDelegateMutDef
             (Sig : mutSig)
             (Mut12 : @mutDef rep Sig * @mutDef delegateRep Sig)
  : @mutDef (rep * delegateRep) Sig
    := {| mutBody rep1rep2 arg := (r1 <- mutBody (fst Mut12) (fst rep1rep2) arg;
                                   r2 <- mutBody (snd Mut12) (snd rep1rep2) arg;
                                   ret (r1, r2)) |}.

  Definition combinedObsDef
             (Sig : obsSig)
             (Obs : @obsDef rep Sig)
  : @obsDef (rep * delegateRep) Sig
    := {| obsBody rep1rep2 := obsBody Obs (fst rep1rep2) |}.

  Definition combinedDelegateMutDefs
  : ilist (@mutDef (rep * delegateRep)) mutSigs
    := imap  _ combinedDelegateMutDef (izip _ (fun _ => pair) mutDefs delegateMutDefs).

  Definition combinedObsDefs
  : ilist (@obsDef (rep * delegateRep)) obsSigs
    := imap  _ combinedObsDef obsDefs.

  (** TODO: These should go elsewhere *)
  Local Hint Extern 0 =>
  match goal with
    | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
  end.

  Local Hint Extern 0 => progress unfold mutSig_eq; simpl.
  Local Hint Extern 0 => progress unfold obsSig_eq; simpl.

  Local Hint Extern 1 => find_if_inside; solve [ trivial ].

  Local Hint Extern 1 => progress subst.

  Lemma refineADT_BuildADT_Rep_default
  : refineADT
      (BuildADT mutDefs obsDefs)
      (BuildADT combinedDelegateMutDefs combinedObsDefs).
  Proof.
    eapply refineADT_Build_ADT_Rep with (AbsR := fun x y => x = fst y); eauto; intros.
    - unfold getMutDef.
      unfold combinedDelegateMutDefs.
      rewrite <- ith_Bounded_imap; simpl.
      rewrite ith_Bounded_izip with (f := fun _ => pair); simpl.
      unfold refine; intros.
      inversion_by computes_to_inv.
      eauto.
    - unfold getObsDef.
      unfold combinedObsDefs.
      rewrite <- ith_Bounded_imap; simpl.
      unfold refine; intros; eauto.
  Qed.


(*
  Definition absMutDef
             (Sig : mutSig)
             (oldMut : @mutDef oldRep Sig)
  : @mutDef newRep Sig :=
    {| mutBody := absMutatorMethod AbsR (mutBody oldMut) |}.

  Definition absObsDef
             (Sig : obsSig)
             (oldMut : @obsDef oldRep Sig)
  : @obsDef newRep Sig :=
    {| obsBody := absObserverMethod AbsR (obsBody oldMut) |}.*)
(*
  Lemma refineADT_BuildADT_Rep_default
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef oldRep) mutSigs)
            (obsDefs : ilist (@obsDef oldRep) obsSigs) :
    refineADT
      (BuildADT mutDefs obsDefs)
      (BuildADT (imap _ absMutDef mutDefs)
                (imap _ absObsDef obsDefs)).
*)

(*
  Variable ASig : ADTSig.
  Variable A : ADT ASig.
  Variable DelegateSig : ADTSig.
  Variables DelegateSpec DelegateImpl : ADT DelegateSig.
  Hypothesis refineDelegate : refineADT DelegateSpec DelegateImpl.

  Let AbsR := AbsR refineDelegate.

  Hypothesis refineMutatorPreservesAbsR
  : forall idx : MutatorIndex DelegateSig,
      forall x0 k x1 x2 y,
        computes_to (MutatorMethods DelegateSpec idx x0 k) x1
        -> computes_to (MutatorMethods DelegateSpec idx x0 k) x2
        -> AbsR x1 y
        -> AbsR x2 y.
*)
End Delegate.


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
  Let AbsR := AbsR refineMinMax.

  Definition MinMaxAbsR (or : multiset) (nr : Rep MinMaxImpl) :=
    AbsR or nr.

  Lemma refineObserver_MinMaxAbsR
  : forall idx : ObserverIndex MinMaxSig,
      refineObserver AbsR (ObserverMethods MinMaxSpec idx)
                     (ObserverMethods MinMaxImpl idx).
  Proof.
    destruct refineMinMax; eauto.
  Qed.
  Lemma refineMutator_MinMaxAbsR
  : forall idx : MutatorIndex MinMaxSig,
      refineMutator AbsR (MutatorMethods MinMaxSpec idx)
                    (MutatorMethods MinMaxImpl idx).
  Proof.
    destruct refineMinMax; eauto.
  Qed.

  Hypothesis refineMutatorPreservesAbsR
  : forall idx : MutatorIndex MinMaxSig,
      forall x0 k x1 x2 y,
        computes_to (MutatorMethods MinMaxSpec idx x0 k) x1
        -> computes_to (MutatorMethods MinMaxSpec idx x0 k) x2
        -> AbsR x1 y
        -> AbsR x2 y.

  Lemma helper_AbsR_preserved
        (r : {nr : multiset * Rep MinMaxImpl | MinMaxAbsR (fst nr) (snd nr)})
        (x : nat)
        (r1 : {v : multiset | {m' : multiset | add_spec (fst (` r)) x m'} ↝ v})
        (r2 : {v : Rep MinMaxImpl |
               (callMut MinMaxImpl "Insert"%string) (snd (` r)) x ↝ v})
  : MinMaxAbsR (` r1) (` r2).
  Proof.
    unfold MinMaxAbsR in *.
    pose proof (refineMutatorPreservesAbsR {| bindex := "Insert"%string |}) as AbsRPreserved.
    clear refineMutatorPreservesAbsR; simpl in *.
    abstract (
        destruct_head sig;
        simpl in *;
          inversion_by computes_to_inv;
        let H := fresh in
        pose proof (refineMutator_MinMaxAbsR {| bindex := "Insert"%string |}) as H;
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
        eapply AbsRPreserved;
        solve [ eassumption
              | constructor; eassumption ]
      ).
  Qed.
  (*
  Inductive type_AbsR {Sig} {A B : ADT Sig} (P : (Rep A -> Rep B -> Prop) -> Prop) : refineADT A B -> Type
    := Build_type_AbsR : forall AbsR H0 H1,
                          P AbsR
                          -> type_AbsR P (@refinesADT _ A B AbsR H0 H1).

  Global Instance trunc_type_AbsR {Sig A B} (P : _ -> Prop)
         `{forall R, IsHProp (P R)}
         rH
  : IsHProp (@type_AbsR Sig A B P rH).
  Proof.
    apply hprop_allpath.
    intros x y.
    destruct x.
    inversion y.

  Definition MinMaxAbsR (or : Rep MinMaxSpec) (nr : Rep MinMaxImpl) (H : refineADT MinMaxSpec MinMaxImpl) :=
    inhabited (type_AbsR (fun AbsR => AbsR or nr) H).*)

  Definition delegateADTAbsR (or : multiset)
             (nr : { nr : multiset * Rep MinMaxImpl
                   | MinMaxAbsR (fst nr) (snd nr)(* refineMinMax*) }) :=
    or = fst (proj1_sig nr).

  Ltac autorefine :=
    unfold repInvAbsR in *|-*;
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
           let obsIdxB := (eval simpl in (@Build_BoundedIndex (List.map obsID obsSigs) obsIdx _)) in
           eapply SharpenStep;
             [ eapply (refineADT_BuildADT_ReplaceObserver
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

  Tactic Notation "hone''" "=-observer" constr(obsIdx) "using" open_constr(obsBod) :=
    let A := match goal with  |- Sharpened ?A => constr:(A) end in
    lazymatch A with
      | @BuildADT ?Rep' ?mutSigs ?obsSigs ?mutDefs ?obsDefs
        => let ASig := constr:(BuildADTSig mutSigs obsSigs) in
           let MutatorIndex' := (eval simpl in (MutatorIndex ASig)) in
           let ObserverIndex' := (eval simpl in (ObserverIndex ASig)) in
           let ObserverDomCod' := (eval simpl in (ObserverDomCod ASig)) in
           let obsIdxB := (eval simpl in (@Build_BoundedIndex (List.map obsID obsSigs) obsIdx _)) in
           eapply SharpenStep;
             [ eapply (refineADT_BuildADT_ReplaceObserver_eq
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
           let obsIdxB := (eval simpl in (@Build_BoundedIndex (List.map obsID obsSigs) obsIdx _)) in
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

  Tactic Notation "hone''" "observer" constr(obsIdx) "under" constr(refineADT_with_AbsR) "using" open_constr(obsBod) :=
    hone'' observer obsIdx using obsBod;
  [ (*let H' := fresh "AbsR" in
    pose proof refineADT_with_AbsR as H'; revert H';
    refine (refineADT_AbsR_elim _);
    intro H';
    exists H'*)
    exists (AbsR refineADT_with_AbsR)
  | ].


  Tactic Notation "hone''" "observer" constr(obsIdx) :=
    hone'' observer obsIdx using _.

  Tactic Notation "hone''" "=-observer" constr(obsIdx) :=
    hone'' =-observer obsIdx using _.

  Tactic Notation "hone''" "observer" constr(obsIdx) "under" constr(refineADT_with_AbsR) :=
    hone'' observer obsIdx under refineADT_with_AbsR using _.

  Tactic Notation "hone''" "=-mutator" constr(mutIdx) "using" open_constr(mutBod) :=
    let A := match goal with  |- Sharpened ?A => constr:(A) end in
    lazymatch A with
      | @BuildADT ?Rep' ?mutSigs ?obsSigs ?mutDefs ?obsDefs
        => let ASig := constr:(BuildADTSig mutSigs obsSigs) in
           let MutatorIndex' := (eval simpl in (MutatorIndex ASig)) in
           let MutatorDom' := (eval simpl in (MutatorDom ASig)) in
           let mutIdxB := (eval simpl in (@Build_BoundedIndex (List.map mutID mutSigs) mutIdx _)) in
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

  Tactic Notation "hone''" "=-mutator" constr(mutIdx) :=
    hone'' =-mutator mutIdx using _.


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
    (@Build_BoundedIndex (List.map mutID mutSigs) mutIdx _) in
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
      let AbsR := fresh "AbsR" in
      let H := fresh "H" in
      let H' := fresh "H'" in
      lazymatch goal with
        | [ r_n : sig _ |- _ ]
          => pose proof (fun arg =>
                           refineObserver_MinMaxAbsR
                             {| bindex := rew_observer_name |}
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
    (@Build_BoundedIndex (List.map mutID mutSigs) mutIdx _) in
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
    hone representation' using delegateADTAbsR.
    (** Split out the [Pick]s in the MinPlusMax Observer. *)
    hone'' ∑-observer "MinPlusMax"%string.
    { intros.
      set_evars; simpl in *.
      unfold two_op_spec.
      unfold delegateADTAbsR; simpl.
      setoid_rewrite remove_forall_eql.
      setoid_rewrite refineEquiv_pick_computes_to.
      setoid_rewrite refineEquiv_split_func_ex2'.
      subst_body.
      rewrite_hyp.
      higher_order_2_reflexivity. }
    (** Rewrite the "Min" and then "Max" [Pick] in the MinPlusMax Observer. *)
    dubiously specialized hone ∑-observer "MinPlusMax"%string  rewriting with observer "Min"%string.
    dubiously specialized hone ∑-observer "MinPlusMax"%string  rewriting with observer "Max"%string.
    hone representation' using (fun x y => proj1_sig x = y).
    hone'' =-observer "MinPlusMax"%string.
    { intros; subst.
      set_evars; simpl in *.
      setoid_rewrite forall_sig_prop.
      simpl.
      setoid_rewrite forall_commute.
      setoid_rewrite remove_forall_eql.
      unfold MinMaxAbsR.
      setoid_rewrite flip_a_impl_b_impl_a.
      setoid_rewrite refineEquiv_pick_computes_to.
      subst_body.
      higher_order_2_reflexivity. }
    hone'' mutator "Insert"%string using
    (fun r x =>
       (r1 <- callMut MinPlusMaxSpec "Insert" (fst r) x;
        r2 <- callMut MinMaxImpl "Insert" (snd r) x;
        ret (r1, r2))).
    {
      intros; subst.
      (* Setoid rewriting is breaking down for me here. *)
      (* setoid_rewrite forall_sig_prop; simpl.
       setoid_rewrite forall_commute.
setoid_rewrite remove_forall_eq0.
       setoid_rewrite exists_sig; simpl.
      setoid_rewrite exists_and_assoc.
      setoid_rewrite remove_exists_and_eq0.
      unfold MinMaxAbsR.
      unfold delegateADTAbsR.
      simpl.
      setoid_rewrite refineEquiv_pick_eq'.
      autorewrite with refine_monad.
      setoid_rewrite flip_a_impl_b_impl_a.
      setoid_rewrite remove_forall_eq0.
      setoid_rewrite remove_exists_and_eq0.
      setoid_rewrite split_refine_fst_proj1_sig; simpl.
      setoid_rewrite refineEquiv_pick_computes_to.

      repeat intro.
      inversion_by computes_to_inv; subst; simpl.
      constructor; simpl; eauto.
      eexists.
      econstructor; simpl; eauto.
      econstructor; simpl; eauto.
      econstructor; simpl; eauto.
      unfold MinMaxAbsR.
      destruct refineMinMax.
      unfold refineMutator in *.

      econstructor.
      eauto.
      simpl in *.
      unfold refine; intros; inversion_by computes_to_inv; subst;
      econstructor.
      unfold add_spec in *.
      econstructor; intros; intuition; subst.
      econstructor; split.
      econstructor; split.
      instantiate (1 := (x, x0)); split; simpl; eauto.
      apply functional_extensionality; simpl; eauto.
      apply functional_extensionality; simpl; eauto.
      intros; rewrite H1, H0, H3; auto.
      econstructor; eauto.
    }

    { intros; subst.
      set_evars.
      setoid_rewrite forall_sig_prop; simpl.
      setoid_rewrite forall_commute.
      setoid_rewrite remove_forall_eq0.
      setoid_rewrite exists_sig; simpl.
      setoid_rewrite exists_and_assoc.
      setoid_rewrite remove_exists_and_eq0.
      unfold MinMaxAbsR.
      unfold delegateADTAbsR.
      simpl.
      setoid_rewrite refineEquiv_pick_eq'.
      autorewrite with refine_monad.
      setoid_rewrite flip_a_impl_b_impl_a.
      setoid_rewrite remove_forall_eq0.
      setoid_rewrite remove_exists_and_eq0.
      setoid_rewrite split_refine_fst_proj1_sig; simpl.
      setoid_rewrite refineEquiv_pick_computes_to.
      eapply refine_exists_mor.
      intros ? ?.
      Lemma pick_exist_computes_to A B (P : B -> Type) c v (f : A -> B)
      : impl (computes_to (v' <- c;
                           ret (f v'))
                          (proj1_sig v))
             (computes_to (v' <- c
                           ret (proj1_sig v'))
                          (proj1_sig v)
              /\ computes_to (v' <- c;
                              ret (proj2_sig v')
      SearchAbout Pick ex.
      SearchAbout computes_to.

      subst_body.
      reflexivity.
      reflexivity.
      set_evars.
      repeat intro.
      econstructor.
setoid_rewrite remove_forall_eq0.

      setoid_rewrite remove_exists_and_eq1.

        split; repeat
        firstorder.

    setoid_rewrite remove_forall_eq0'.

    hone'' ∑-mutator "Insert"%string using
           (fun (r : {nr : multiset * Rep MinMaxImpl | MinMaxAbsR (fst nr) (snd nr)}) x =>
              (r1 <- { v : { v | callMut MinPlusMaxSpec "Insert" (fst (proj1_sig r)) x ↝ v } | True };
               r2 <- { v : { v | callMut MinMaxImpl "Insert" (snd (proj1_sig r)) x ↝ v } | True};
               ret (exist (fun nr => MinMaxAbsR (fst nr) (snd nr)) (`r1, `r2) (helper_AbsR_preserved _ r1 r2) ))).
    { intros.
      subst.
      unfold delegateADTAbsR; simpl.
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
      admit.
    }
      finish sharpening.
  Defined.

  (* An attempt to delegate to the reference spec,
     then refine the delegate ADT to the implementation. *)

  Definition delegateSpecAbsR (or : multiset)
             (nr : multiset * Rep MinMaxSpec) :=
    or = fst nr /\ or = snd nr.

  Arguments delegateSpecAbsR _ _ / .

  Definition delegateImplAbsR (or : multiset * multiset)
             (nr : multiset * Rep MinMaxImpl) :=
    fst or = fst nr /\ AbsR (snd or) (snd nr).

  Arguments delegateImplAbsR _ _ / .

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

  Lemma swap_rep
    : forall
        Sig Sig'
        (ClientADT : ADT Sig -> ADT Sig')
        (adt adt' : ADT Sig)
        (AbsR' : Rep (ClientADT adt) -> Rep (ClientADT adt') -> Prop),
      (forall mutIdx : MutatorIndex Sig',
         refineMutator AbsR'
                       (MutatorMethods (ClientADT adt) mutIdx)
                       (MutatorMethods (ClientADT adt') mutIdx))
      -> (forall obsIdx : ObserverIndex Sig',
            refineObserver AbsR'
                           (ObserverMethods (ClientADT adt) obsIdx)
                           (ObserverMethods (ClientADT adt') obsIdx))
      -> refineADT (ClientADT adt) (ClientADT adt').
    Proof.
      intros.
      destruct (ClientADT adt); destruct (ClientADT adt').
      eapply refineADT_Build_ADT_Rep with (AbsR := AbsR'); eauto.
    Qed.

    Delimit Scope ADTParsing_scope with ADTParsing.

  Definition MinPlusMaxImpl' (defaultValue : nat)
  : Sharpened MinPlusMaxSpec.
  Proof.
    clear refineMutatorPreservesAbsR.
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
    hone representation' using delegateSpecAbsR.
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
      (* Duplicate the call to Insert. *)
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
           delegateImplAbsR).
    (* Show the mutator swap is valid. This is fairly boilerplate. *)
    {
      intros; simpl; unfold ith_obligation_1, ith_obligation_2; simpl.
      destruct mutIdx as  [ ? [ [? | [ ] ] ] ]; subst; simpl.
      intros; intuition; subst.
      setoid_rewrite <- (refineMutator_MinMaxAbsR {| bstring := "Insert"%string |} _ _ n H1).
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
      rewrite (refineObserver_MinMaxAbsR {| bstring := "Min"%string |} _ _ n H1).
      f_equiv; unfold pointwise_relation; intros.
      autorewrite with refine_monad; simpl;
      rewrite (refineObserver_MinMaxAbsR {| bstring := "Max"%string |} _ _ n H1); f_equiv.
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
