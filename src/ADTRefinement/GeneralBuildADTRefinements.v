Require Import Coq.Lists.List Coq.Arith.Arith
        Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.IterateBoundedIndex
        Fiat.ADTNotation.BuildADTSig Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildComputationalADT
        Fiat.ADTNotation.BuildADTReplaceMethods
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* Notation-friendly versions of the honing tactics in GeneralRefinements. *)

Section BuildADTRefinements.

  Require Import Coq.Strings.String.
  Local Hint Resolve string_dec.


  Lemma refineADT_BuildADT_ReplaceMethod
        (Rep : Type)
        {n}
        (methSigs : Vector.t methSig n)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n)
        (newDef : methDef (Vector.nth methSigs idx))
        AbsR
        (AbsR_reflexive_method :
           forall methIdx,
             refineMethod AbsR _ (getMethDef methDefs methIdx) (getMethDef methDefs methIdx))
  : refineMethod AbsR
                 _ (methBody (ith methDefs idx))
                 (methBody newDef)
    -> refineADT
         (BuildADT methDefs)
         (ADTReplaceMethDef methDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (AbsR := AbsR); trivial.
    intros; unfold getMethDef.
    unfold replaceMethDef.
    destruct (fin_eq_dec methIdx idx); subst.
    rewrite ith_replace_Index_eq; eauto.
    rewrite ith_replace_Index_neq; eauto.
  Qed.

  Corollary SharpenStep_BuildADT_ReplaceMethod_eq
        (Rep : Type)
        {n}
        (methSigs : Vector.t methSig n)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n)
        (newDef : methDef (Vector.nth methSigs idx))
        adt''
    :
      (let H := methBody newDef in refineMethod eq _ (methBody (ith methDefs idx)) newDef)
      -> refineADT (ADTReplaceMethDef methDefs idx newDef) adt''
      -> refineADT (BuildADT methDefs) adt''.
  Proof.
    intros; eapply SharpenStep.
    eapply refineADT_BuildADT_ReplaceMethod with (AbsR := eq);
    simpl; unfold refine; intros; subst; eauto; reflexivity.
    exact X.
  Qed.

  Lemma FullySharpenStep_BuildADT_ReplaceMethod_eq
        (Rep : Type)
        {n}
        (methSigs : Vector.t methSig n)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n)
        (newDef : methDef (Vector.nth methSigs idx))
        adt''
    :
      (let H := methBody newDef in refineMethod eq _ (methBody (ith methDefs idx)) newDef)
      -> FullySharpenedUnderDelegates
           (ADTReplaceMethDef methDefs idx newDef)
           adt''
      -> FullySharpenedUnderDelegates
           (BuildADT methDefs)
           adt''.
  Proof.
    intros; eapply FullySharpenStep.
    eapply refineADT_BuildADT_ReplaceMethod with (AbsR := eq);
    simpl; unfold refine; intros; subst; eauto; reflexivity.
    exact X.
  Qed.

  Definition Notation_Friendly_BuildMostlySharpenedcADT
             {n}
             {methSigs : Vector.t methSig n}
             (DelegateIDs : nat)
             (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                       ComputationalADT.cMethodType _ (rep DelegateReps)
                                                    (methDom Sig) (methCod Sig)) methSigs)
             (DelegateReps : Fin.t DelegateIDs -> Type)
             (DelegateImpls : forall idx,
                                ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
  : ComputationalADT.cADT (BuildADTSig methSigs) :=
    BuildcADT
      (imap (Build_cMethDef (rep DelegateReps))
            (cMethods DelegateReps DelegateImpls)).

  Definition Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT
             (RepT : Type)
             {n}
             {methSigs : Vector.t methSig n}
             (methDefs : ilist methSigs)
             (DelegateIDs : nat)
             (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                       ComputationalADT.cMethodType
                         (methArity Sig) (rep DelegateReps) (methDom Sig)
                         (methCod Sig)) methSigs)
             (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
             (cAbsR :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                  (ValidImpls
                   : forall idx : Fin.t DelegateIDs,
                       refineADT (DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                  RepT -> rep DelegateReps -> Prop)
             (cMethodsRefinesSpec : forall
                                      (DelegateReps : Fin.t DelegateIDs -> Type)
                                      (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                      (ValidImpls
                                       : forall idx : Fin.t DelegateIDs,
                                           refineADT (DelegateSpecs idx)
                                                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                      Iterate_Dep_Type_BoundedIndex
                                        (fun idx =>
                                           @refineMethod
                                             RepT (rep DelegateReps)
                                             (cAbsR _ _ ValidImpls)
                                             (methArity (Vector.nth methSigs idx))
                                             (methDom (Vector.nth methSigs idx))
                                             (methCod (Vector.nth methSigs idx))
                                             (getMethDef methDefs idx)
                                             (LiftcMethod (methArity (Vector.nth methSigs idx))
                                                          _ _ _ (ith (cMethods DelegateReps DelegateImpls) idx))))
  : FullySharpenedUnderDelegates (BuildADT methDefs)
                                 {|
                                   Sharpened_DelegateSigs := DelegateSigs;
                                   Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT
                                                                 _ rep cMethods;
                                   Sharpened_DelegateSpecs := DelegateSpecs |}.
  Proof.
    intros * DelegateReps DelegateImpls DelegateImplRefinesSpec.
    eapply (@refinesADT _ (BuildADT methDefs)
                        (LiftcADT (existT _ (rep DelegateReps)
                                          {| pcMethods := _|}))
                        (cAbsR DelegateReps DelegateImpls DelegateImplRefinesSpec)).
    - simpl; unfold ComputationalADT.cMethods; simpl; intros.
      rewrite <- ith_imap.
      apply (Lookup_Iterate_Dep_Type
                  _ (cMethodsRefinesSpec DelegateReps DelegateImpls DelegateImplRefinesSpec)).
  Qed.

  Definition Notation_Friendly_SharpenFully'
             (RepT : Type)
             {n}
             (methSigs : Vector.t methSig n)
             (methDefs : ilist methSigs)
             (DelegateIDs : nat)
             (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                            ComputationalADT.cMethodType
                              (methArity Sig)
                              (rep DelegateReps) (methDom Sig)
                              (methCod Sig)) methSigs)
             (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
             (cAbsR :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                  (ValidImpls
                   : forall idx : Fin.t DelegateIDs,
                       refineADT (DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                  RepT -> rep DelegateReps -> Prop)
             (cMethodsRefinesSpec : forall
                                      (DelegateReps : Fin.t DelegateIDs -> Type)
                                      (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                      (ValidImpls
                                       : forall idx : Fin.t DelegateIDs,
                                           refineADT (DelegateSpecs idx)
                                                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                      Iterate_Dep_Type_BoundedIndex
                                        (fun idx  =>
                                           @refineMethod
                                             RepT (rep DelegateReps)
                                             (cAbsR _ _ ValidImpls)
                                             _
                                             (methDom (Vector.nth methSigs idx))
                                             (methCod (Vector.nth methSigs idx))
                                             (getMethDef methDefs idx)
                                             (LiftcMethod _ _ _ _ (ith (cMethods DelegateReps DelegateImpls) idx ))))
  : FullySharpenedUnderDelegates
      (BuildADT methDefs)
      {|
        Sharpened_DelegateSigs := DelegateSigs;
        Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT _ rep cMethods;
        Sharpened_DelegateSpecs := DelegateSpecs |} :=
    (Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT
       methDefs _ rep cMethods DelegateSpecs cAbsR
       cMethodsRefinesSpec).

  Record NamedDelegatee :=
    { delegateeSig : ADTSig;
      delegateeRep : Type }.

  Definition Build_NamedDelegatees
           {n}
           (DelegateSigs : Vector.t ADTSig n)
           (DelegateReps : Vector.t Type n)
  : Vector.t NamedDelegatee n.
      pattern n, DelegateReps, DelegateSigs.
      match goal with
        |- ?P n DelegateReps DelegateSigs =>
        simpl; refine (Vector.rect2
                         P
                         (Vector.nil _)
                         (fun n DelegateReps DelegateSigs Delegatees Rep Sig =>
                            (Vector.cons
                               _
                               {| delegateeSig := Sig; delegateeRep := Rep |}
                               _ Delegatees))
                         DelegateReps DelegateSigs)
      end.
  Defined.

  Definition Notation_Friendly_SharpenFully
             (RepT : Type)
             {m n}
             (methSigs : Vector.t methSig n)
             (methDefs : ilist methSigs)
             (DelegateSigs' : Vector.t ADTSig m)
             (DelegateReps' : Vector.t Type m)
             (Delegatees := Build_NamedDelegatees DelegateSigs' DelegateReps')
             (DelegateIDs := m)
             (DelegateSigs := fun idx =>
                                delegateeSig (Vector.nth Delegatees idx))
             (DelegateReps := fun idx =>
                                delegateeRep (Vector.nth Delegatees idx))
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                            ComputationalADT.cMethodType
                              (methArity Sig)
                         (rep DelegateReps) (methDom Sig)
                         (methCod Sig)) methSigs)
             (DelegateSpecs' : ilist (B := fun nadt => ADT (delegateeSig nadt)) Delegatees )
             (DelegateSpecs := ith DelegateSpecs')
             (cAbsR :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                  (ValidImpls
                   : forall idx : Fin.t DelegateIDs,
                       refineADT (DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                  RepT -> rep DelegateReps -> Prop)
             (cMethodsRefinesSpec : forall
                                      (DelegateReps : Fin.t DelegateIDs -> Type)
                                      (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                      (ValidImpls
                                       : forall idx : Fin.t DelegateIDs,
                                           refineADT (DelegateSpecs idx)
                                                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                      Iterate_Dep_Type_BoundedIndex
                                        (fun idx =>
                                           @refineMethod
                                             RepT (rep DelegateReps)
                                             (cAbsR _ _ ValidImpls)
                                             _
                                             (methDom (Vector.nth methSigs idx))
                                             (methCod (Vector.nth methSigs idx))
                                             (getMethDef methDefs idx)
                                             (LiftcMethod _ _ _ _ (ith (cMethods DelegateReps DelegateImpls) idx))))
  : FullySharpenedUnderDelegates
      (BuildADT methDefs)
      {|
        Sharpened_DelegateSigs := DelegateSigs;
        Sharpened_Implementation :=
          Notation_Friendly_BuildMostlySharpenedcADT _ rep cMethods;
        Sharpened_DelegateSpecs := DelegateSpecs |}.
    refine (Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT
              methDefs _ rep cMethods DelegateSpecs cAbsR
              cMethodsRefinesSpec).
  Defined.

End BuildADTRefinements.

Arguments Notation_Friendly_BuildMostlySharpenedcADT _ _ _ _ _ _ _ _  / .

Ltac extract_delegate_free_impl :=
  cbv beta; simpl;
    match goal with
        |- forall idx : Fin.t 0,
             refineADT
               (ith inil idx)
               (ComputationalADT.LiftcADT
                  (existT
                     (ComputationalADT.pcADT
                        (delegateeSig _))
                     (?DelegateReps idx) (?DelegateSpecs idx))) =>
        unify DelegateReps (fun idx : Fin.t 0 => False);
          let P' := match type of DelegateSpecs with
                    | forall idx, @?P' idx => P'
                    end in
          unify DelegateSpecs (fun idx : Fin.t 0 => Fin.case0 P' idx);
            apply Fin.case0
          end.

Tactic Notation "extract" "delegate-free" "implementation" :=
  extract_delegate_free_impl.

(* A tactic for finishing a derivation. Probably needs a better name.*)
Tactic Notation "finish" "sharpening" constr(delegatees):=
  eexists; [ eapply reflexivityT
           | constructor 1 with (Sharpened_DelegateSpecs := delegatees); intros;
             split; simpl;
             match goal with
                 [|- forall idx : BoundedString, _] =>
                 let idx := fresh in
                 intro idx; pattern idx;
                 eapply Iterate_Ensemble_BoundedIndex_equiv;
                 unfold Iterate_Ensemble_BoundedIndex; simpl;
                 intuition;
                 repeat
                   (try simplify with monad laws;
                    first [constructor
                          | match goal with
                                |- context[if ?b then _ else _] =>
                                destruct b
                            end
                          ])
             end ].

Ltac destruct_pair a :=
  match type of a with
  | prod _ _ =>
    rewrite <- (surjective_pairing a)
  | _ => idtac
  end.

Tactic Notation "finish" "honing" :=
  match goal with
  | |- ?R _ (?H ?a ?b ?c ?d ?e) =>
    destruct_pair a; destruct_pair b; destruct_pair c;
    destruct_pair d; destruct_pair e;
    try subst H;  higher_order_reflexivity
  | |- ?R _ (?H ?a ?b ?c ?d) =>
    destruct_pair a; destruct_pair b; destruct_pair c;
    destruct_pair d;
    try subst H; higher_order_reflexivity
  | |- ?R _ (?H ?a ?b ?c ) =>
    destruct_pair a; destruct_pair b; destruct_pair c;
    try subst H;
    higher_order_reflexivity
  | |- ?R _ (?H ?a ?b) =>
    destruct_pair a; destruct_pair b;
    try subst H; higher_order_reflexivity
  | |- ?R _ (?H ?a ) =>
    destruct_pair a;
    try subst H; higher_order_reflexivity
  | |- ?R _ (?H ) =>
    try subst H; higher_order_reflexivity
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac ilist_of_evar C B As k :=
  match As with
    | nil => k (fun (c : C) => inil (B c))
    | cons ?a ?As' =>
      makeEvar (forall c, B c a)
               ltac:(fun b =>
                       ilist_of_evar
                         C B As'
                         ltac:(fun Bs' => k (fun c => icons a (b c) (Bs' c))))
  end.

(*Ltac FullySharpenEachMethod delegateSigs delegateSpecs :=
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_evar
        (ilist ComputationalADT.cADT delegateSigs)
        (fun Sig => cMethodType Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths => ilist_of_evar
                              (ilist ComputationalADT.cADT delegateSigs)
                              (fun Sig => cConstructorType Rep (consDom Sig))
                              consSigs
                              ltac:(fun cCons =>
                                      eapply Notation_Friendly_SharpenFully
                                      with (DelegateSpecs := delegateSpecs)
                                             (cConstructors := cCons)
                                             (cMethods := cMeths)));
        simpl;
        intros; repeat econstructor
  end.

Ltac BuildFullySharpenedConstructor :=
  intros;
  match goal with
      |- ret ?x ↝ ?Bod ?DelegateImpl ?d
      => let Bod' := eval pattern DelegateImpl, d in x in
             match Bod' with
               | (?Bod'' _ _) =>
                 unify Bod Bod''; constructor
             end
  end. *)

Lemma SharpenIfComputesTo {A} :
  forall (cond : bool) (cT cE : Comp A) vT vE,
    cT ↝ vT
    -> cE ↝ vE
    -> (if cond then cT else cE) ↝ if cond then vT else vE.
Proof.
  destruct cond; eauto.
Qed.

(*Lemma ComputesToLiftcADT {Sig}
: forall (cadt : cADT Sig) idx r_n d,
    Methods (LiftcADT cadt) idx r_n d ↝ cMethods cadt idx r_n d.
Proof.
  unfold LiftcADT; simpl; intros.
  simpl; constructor.
Qed. *)

(*Lemma refineCallMethod {Sig}
: forall (adt : ADT Sig) (cadt : cADT Sig)
         (refineA : refineADT adt (LiftcADT cadt))  idx r_o r_n d,
    refine (r_o' <- Methods adt idx r_o d;
            r_n' <- Pick (fun r_n' : cRep cadt => AbsR refineA (fst r_o') r_n');
            ret (r_n', snd r_o'))
           (Methods (LiftcADT cadt) idx r_n d)
    -> exists r_o',
         refine (Methods adt idx r_o d) (ret r_o') /\
         refine {r_n' | AbsR refineA (fst r_o') r_n'}
                (ret (fst (cMethods cadt idx r_n d))) /\
         snd r_o' = snd (cMethods cadt idx r_n d)
         /\ AbsR refineA (fst r_o') (fst (cMethods cadt idx r_n d)).
Proof.
  intros.
  pose proof (H _ (ComputesToLiftcADT cadt idx r_n d));
    computes_to_inv; subst.
  eexists v ; intuition.
  intros c Comp_v; computes_to_inv; subst; auto.
  rewrite <- H0''; refine pick val _; simpl; eauto.
  reflexivity.
  rewrite <- H0''; eauto.
  rewrite <- H0''; eauto.
Qed. *)

Ltac ilist_of_evar_dep n C D B As k :=
  match n with
  | 0 => k (fun (c : C) (d : D c) => @inil _ B)
  | S ?n' =>
    makeEvar (forall (c : C) (d : D c), B (Vector.hd As))
             ltac:(fun b =>
                           ilist_of_evar_dep n'
                                             C D B (Vector.tl As)
                                             ltac:(fun Bs' => k (fun (c : C) (d : D c) => icons (a := Vector.hd As) (b c d) (Bs' c d))))
  end.

Ltac FullySharpenEachMethod DelegateSigs DelegateReps delegateSpecs :=
    let Delegatees := constr:(Build_NamedDelegatees DelegateSigs DelegateReps) in
    let DelegateSpecs := constr:(ith delegateSpecs) in
    let NumDelegates := match type of DelegateSigs with
                        | Vector.t _ ?n => n
                        end in
    match goal with
      |- FullySharpenedUnderDelegates (@BuildADT ?Rep ?n ?methSigs ?methDefs) _ =>
      ilist_of_evar_dep n
                        (Fin.t NumDelegates -> Type)
                        (fun D =>
                           forall idx,
                             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (D idx))
                        (fun Sig => ComputationalADT.cMethodType (methArity Sig) Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                eapply (@Notation_Friendly_SharpenFully
                          Rep NumDelegates n
                          methSigs
                          methDefs
                          DelegateSigs DelegateReps
                          (fun _ => Rep)
                          cMeths
                          delegateSpecs
                          (fun
                         (DelegateReps'' : Fin.t NumDelegates -> Type)
                         (DelegateImpls'' : forall idx,
                             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (DelegateReps'' idx))
                         (ValidImpls''
                          : forall idx : Fin.t NumDelegates,
                             refineADT (DelegateSpecs idx)
                                       (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls'' idx))))
                            => @eq _)
             ))
    end; try (simpl; repeat split; intros; subst).

Ltac Implement_If_Then_Else :=
  match goal with
    | |- refine (If_Then_Else ?i (ret ?t) (ret ?e)) _ =>
      apply (refine_If_Then_Else_ret i t e)

    | |- refine (Bind (If ?i Then ?t Else ?e) ?k) _ =>
      etransitivity;
        [ apply (refine_If_Then_Else_Bind i t e k)
        | etransitivity;
          [ apply refine_If_Then_Else;
            [
              | ]
          | eapply refine_If_Then_Else_ret
          ]
        ]
  end.

Ltac Implement_If_Opt_Then_Else :=
  match goal with
    | |- refine (Ifopt ?i as a Then (ret (@?t a)) Else (ret ?e)) _ =>
      apply (refine_If_Opt_Then_Else_ret i t e)

    | |- refine (Bind (Ifopt ?i as a Then (@?t a) Else ?e) ?k) _ =>
      etransitivity;
        [ apply (refine_If_Opt_Then_Else_Bind i t e k)
        | etransitivity;
          [ apply refine_If_Opt_Then_Else;
            [ unfold pointwise_relation; intros
              | ]
          | eapply refine_If_Opt_Then_Else_ret
          ]
        ]
  end.

Ltac finish_SharpeningADT_WithoutDelegation :=
  eapply FullySharpened_Finish;
  [ FullySharpenEachMethod
      (@Vector.nil ADTSig)
      (@Vector.nil Type)
      (ilist.inil (B := fun nadt => ADT (delegateeSig nadt)));
    try simplify with monad laws; simpl; try refine pick eq; try simplify with monad laws;
    try first [ simpl];
    (* Guard setoid rewriting with [refine_if_If] to only occur when there's
    actually an [if] statement in the goal.  This prevents [setoid_rewrite] from
    uselessly descending into folded definitions. *)
    repeat lazymatch goal with
             | [ |- context [ if _ then _ else _ ] ] =>
               setoid_rewrite refine_if_If at 1
           end;
    repeat first [
             higher_order_reflexivity
           | simplify with monad laws
           | Implement_If_Then_Else
           | Implement_If_Opt_Then_Else ]
  | extract_delegate_free_impl
  | simpl; higher_order_reflexivityT ].

Lemma refineIfret {A} :
  forall (cond : bool) (a a' : A),
    refine (if cond then ret a else ret a')
           (ret (if cond then a else a')).
Proof.
  destruct cond; reflexivity.
Qed.

Ltac refine_under :=
  subst_refine_evar;
  first
    [ eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else_trans;
      [set_refine_evar; unfold pointwise_relation; intros | set_refine_evar ] ].
