Require Import Coq.Lists.List Fiat.Common
        Fiat.Common.ilist
        Fiat.Common.BoundedLookup
        Fiat.Common.IterateBoundedIndex
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADTNotation.BuildADTSig
        Fiat.ADTNotation.BuildADT
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.GeneralBuildADTRefinements
        Fiat.ADTRefinement.Refinements.HoneRepresentation
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* A generic refinement and honing tactic for switching the
    representation of an ADT built from [BuildADT]. *)

Section HoneRepresentation.

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* The abstraction relation between old and new representations. *)
  Variable AbsR : oldRep -> newRep -> Prop.

  (* When switching representations, we can always build a default
     implementation (computation?) for the methods of an ADT with
     using the old methods. *)

  Definition absConsDef
             (Sig : consSig)
             (oldCons : @consDef oldRep Sig)
  : @consDef newRep Sig :=
    {| consBody := absConstructor AbsR (consBody oldCons) |}.

  Definition absMethDef
             (Sig : methSig)
             (oldCons : @methDef oldRep Sig)
  : @methDef newRep Sig :=
    {| methBody := absMethod AbsR (methBody oldCons) |}.

  Lemma refineADT_BuildADT_Rep_default
        {n n'}
        {consSigs : Vector.t consSig n}
        {methSigs : Vector.t methSig n'}
        (consDefs : ilist (B := @consDef oldRep) consSigs)
        (methDefs : ilist (B := @methDef oldRep) methSigs) :
    refineADT
      (BuildADT consDefs methDefs)
      (BuildADT (imap absConsDef consDefs)
                (imap absMethDef methDefs)).
  Proof.
    eapply refineADT_Build_ADT_Rep with (AbsR := AbsR); eauto; intros.
    - unfold getConsDef.
      rewrite <- ith_imap.
      apply refine_absConstructor.
    - unfold getMethDef.
      rewrite <- ith_imap.
      apply refine_absMethod.
  Qed.

  (* [refine_AbsMethod] can be applied when honing methods to
     get goals in a nicer form. *)

  Lemma refine_AbsMethod :
    forall Dom Cod oldMethod nr (d : Dom) refinedMeth (H := refinedMeth),
      (forall or,
         AbsR or nr ->
         refine (or' <- oldMethod or d;
                 nr' <- { nr' | AbsR (fst or') nr'};
                 ret (nr', snd or'))
                (refinedMeth nr d))
      -> refine (absMethod (cod := Cod) AbsR oldMethod nr d)
                (H nr d).
  Proof.
    unfold absMethod, refine; intros * H v ComputesTo_v; computes_to_econstructor;
    intros or AbsR_or.
    pose proof (H _ AbsR_or v ComputesTo_v); computes_to_inv;
    subst.
    eexists; split; eauto.
  Qed.

  Lemma refine_AbsMethod' :
    forall Dom Cod oldMethod nr (d : Dom) refinedMeth,
      refine (absMethod (Cod := Cod) AbsR oldMethod nr d)
             (refinedMeth nr d)
      -> (forall or,
            AbsR or nr ->
            refine (or' <- oldMethod or d;
                    nr' <- { nr' | AbsR (fst or') nr'};
                    ret (nr', snd or'))
                   (refinedMeth nr d)).
  Proof.
    unfold absMethod, refine; intros * H or AbsR_or v ComputesTo_v.
    pose proof (H v ComputesTo_v); computes_to_inv;
    subst.
    destruct (H0 _ AbsR_or); intuition; subst.
    repeat computes_to_econstructor; eauto.
    rewrite H4; destruct v; econstructor.
  Qed.

  (* [refine_AbsConstructor] can be applied when honing constructors to
     get goals in a nicer form. *)

  Lemma refine_AbsConstructor :
    forall Dom oldConstructor (d : Dom) refinedConstructor (H := refinedConstructor),
      (refine (or' <- oldConstructor d;
               { nr' | AbsR or' nr'})
                (refinedConstructor d))
      -> refine (absConstructor AbsR oldConstructor d)
                (H d).
  Proof.
    unfold absConstructor, refine; intros * H v ComputesTo_v; computes_to_econstructor.
    pose proof (H v ComputesTo_v); computes_to_inv;
    subst.
    eexists; split; eauto.
  Qed.

  Lemma refine_AbsConstructor' :
    forall Dom oldConstructor (d : Dom) refinedConstructor,
      refine (absConstructor AbsR oldConstructor d)
             (refinedConstructor d)
      -> (refine (or' <- oldConstructor d;
                  { nr' | AbsR or' nr'})
                 (refinedConstructor d)).
  Proof.
    unfold absConstructor, refine; intros * H v ComputesTo_v.
    pose proof (H v ComputesTo_v); computes_to_inv;
    destruct_ex; intuition; subst.
  Qed.

  Inductive refine_Constructors  :
    forall {n} {consSigs : Vector.t consSig n},
      ilist (B := @consDef oldRep) consSigs
      -> ilist (B := @consDef newRep) consSigs ->
           Prop :=
  | refine_Constructors_nil : @refine_Constructors _ (Vector.nil _) inil inil
  | refine_Constructors_cons :
      forall n consSig consSigs
             (constr_body : @constructorType oldRep (consDom consSig))
             (refined_constr_body : @constructorType newRep (consDom consSig))
             (consDefs : ilist (B := @consDef oldRep) consSigs)
             (refined_consDefs : ilist (B := @consDef newRep) consSigs),
        (forall d, refine (r_o' <- constr_body d;
                           {r_n | AbsR r_o' r_n}) (refined_constr_body d))
        -> refine_Constructors consDefs refined_consDefs
        -> @refine_Constructors
             _
             (Vector.cons _ consSig n consSigs)
             (icons {|consBody := constr_body |} consDefs)
             (icons {|consBody := refined_constr_body |} refined_consDefs).

  Definition refine_Constructors_invert
             {n}
             consSigs consDefs refined_consDefs
             (refine_cons : @refine_Constructors n consSigs consDefs refined_consDefs)
  : match consSigs in Vector.t _ n return
          forall consDefs refined_consDefs
                 (refine_cons : @refine_Constructors n consSigs consDefs refined_consDefs),
            Prop
    with
      | Vector.nil => fun _ _ _ => True
      | Vector.cons consig _ consigs' =>
        fun consDefs refined_consDefs refine_cons =>
          refineConstructor AbsR (ilist_hd consDefs) (ilist_hd refined_consDefs) /\
          refine_Constructors (ilist_tl consDefs) (ilist_tl refined_consDefs)
    end consDefs refined_consDefs refine_cons.
  Proof.
    destruct refine_cons; eauto.
  Defined.

  Inductive refine_Methods :
    forall {n'} {methSigs : Vector.t methSig n'},
      ilist (B := @methDef oldRep) methSigs
      -> ilist (B := @methDef newRep) methSigs ->
           Prop :=
  | refine_Methods_nil : @refine_Methods _ (Vector.nil _) inil inil
  | refine_Methods_cons :
      forall n' methSig methSigs
             (meth_body : @methodType oldRep (methDom methSig) (methCod methSig))
             (refined_meth_body : @methodType newRep (methDom methSig) (methCod methSig))
             (methDefs : ilist (B := @methDef oldRep) methSigs)
             (refined_methDefs : ilist (B := @methDef newRep) methSigs),
        (forall r_o r_n d,
           AbsR r_o r_n ->
           refine
             (r_o' <- meth_body r_o d;
              r_n' <- {r_n0 | AbsR (fst r_o') r_n0};
              ret (r_n', snd r_o')) (refined_meth_body r_n d))
        -> refine_Methods methDefs refined_methDefs
        -> @refine_Methods
             _
             (Vector.cons _ methSig n' methSigs)
             (icons {| methBody := meth_body |} methDefs)
                          (icons {| methBody := refined_meth_body |} refined_methDefs).

  Definition refine_Methods_invert
             {n'} methSigs methDefs refined_methDefs
             (refine_meths : @refine_Methods n' methSigs methDefs refined_methDefs)
  : match methSigs in Vector.t _ n' return
          forall methDefs refined_methDefs
                 (refine_meths : @refine_Methods n' methSigs methDefs refined_methDefs),
            Prop
    with
      | Vector.nil => fun _ _ _ => True
      | Vector.cons methSig _ methSigs' =>
        fun methDefs refined_methDefs refine_meths =>
          refineMethod AbsR (ilist_hd methDefs) (ilist_hd refined_methDefs) /\
          refine_Methods (ilist_tl methDefs) (ilist_tl refined_methDefs)
    end methDefs refined_methDefs refine_meths.
  Proof.
    destruct refine_meths; eauto.
  Defined.

  (* This method is used to hone an ADT's representation and
     spawn off subgoals for each operation in one fell-swoop. *)
  Lemma refineADT_BuildADT_Rep_refine_All
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef oldRep) consSigs)
        (methDefs : ilist (B := @methDef oldRep) methSigs)
        (refined_consDefs : ilist (B := @consDef newRep) consSigs)
        (refined_methDefs : ilist (B := @methDef newRep) methSigs)
  :
    refine_Constructors consDefs refined_consDefs
    -> refine_Methods methDefs refined_methDefs
    -> refineADT
      (BuildADT consDefs methDefs)
      (BuildADT refined_consDefs refined_methDefs).
  Proof.
    intros; eapply refineADT_Build_ADT_Rep with (AbsR := AbsR).
    - induction H; simpl.
      + intro; inversion mutIdx.
      + intro; revert IHrefine_Constructors H; clear.
        revert consSig constr_body refined_constr_body
               consSigs consDefs refined_consDefs; pattern n, mutIdx.
        match goal with
          |- ?P n mutIdx => simpl; apply (Fin.caseS P); simpl; intros; eauto
        end.
    - induction H0; simpl.
      + intro; inversion obsIdx.
      + intro; revert IHrefine_Methods H0; clear.
        revert methSig meth_body refined_meth_body
               methSigs methDefs refined_methDefs consSigs; pattern n', obsIdx.
        match goal with
          |- ?P n' obsIdx => simpl; apply (Fin.caseS P); simpl; intros; eauto
        end.
  Qed.

End HoneRepresentation.

(* Honing tactic for refining the ADT representation which provides
   default method and constructor implementations. *)

Tactic Notation "hone" "representation" "using" open_constr(AbsR') "with" "defaults" :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_default with (AbsR := AbsR') |
   compute [imap absConsDef absMethDef]; simpl ].

(* Honing Tactics for working on a single constructor at a time*)
Tactic Notation "hone" "constructor" constr(consIdx) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
      match A with
          BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
      match A with
          BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let ConstructorDom' := eval simpl in (ConstructorDom ASig) in
  let consIdxB := eval simpl in
  (@Build_BoundedIndex _ (List.map consID consSigs) consIdx _) in
      eapply (@SharpenStep_BuildADT_ReplaceConstructor_eq
               Rep'  _ _ consDefs methDefs consIdxB
               (@Build_consDef Rep'
                              {| consID := consIdx;
                                 consDom := ConstructorDom' consIdxB
                              |}
                              _
             ));
    [ intros; simpl in *;
      match goal with
        |  |- refine _ (?E ?d) => is_evar E; let H := fresh in set (H := E)
        | _ => idtac
      end;
      match goal with
        |  |- refine (absConstructor ?AbsR ?oldConstructor ?d)
                     (?H ?d) =>
           eapply (@refine_AbsConstructor _ _ AbsR _ oldConstructor)
        | _ => cbv [absConstructor]
      end
    |  cbv beta in *; simpl in *;
       cbv beta delta [replace_BoundedIndex replace_Index] in *;
       simpl in *].

(* Honing Tactics for working on a single method at a time*)
Arguments DecADTSig : simpl never.
 Tactic Notation "hone" "method" constr(methIdx) :=
   let A :=
       match goal with
         |- Sharpened ?A => constr:(A) end in
   let DSig :=
       match goal with
         |- @refineADT ?DSig _ _ => constr:(DSig)
       end in
   let ASig := match type of A with
                 DecoratedADT ?Sig => Sig
               end in
   let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
      match A with
          BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
      match A with
          BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let MethodDomCod' := eval simpl in (MethodDomCod ASig) in
  let methIdxB := eval simpl in
  (ibound (indexb (@Build_BoundedIndex _ _ (Vector.map methID methSigs) methIdx _))) in
      eapply (@SharpenStep_BuildADT_ReplaceMethod_eq
                Rep' _ _ _ _ consDefs methDefs methIdxB
                (@Build_methDef Rep'
                               {| methID := methIdx;
                                  methDom := fst (MethodDomCod' methIdxB);
                                  methCod := snd (MethodDomCod' methIdxB)
                               |}
                               _
                              ));
    [ intros; simpl in *;
      match goal with
        |  |- refine _ (?E ?nr ?d) => is_evar E; let H := fresh in set (H := E)
        | _ => idtac
      end;
      match goal with
        |  |- refine (@absMethod ?oldRep ?newRep ?AbsR ?Dom ?Cod ?oldMethod ?nr ?d)
                     (?H ?nr ?d) => eapply (@refine_AbsMethod oldRep newRep AbsR Dom Cod oldMethod)
        | _ => cbv [absMethod]
      end; intros
    |
    cbv beta in *|-;
    cbv delta [replace_BoundedIndex replace_Index] in *;
    simpl in *
    ].

(* Honing tactic for refining the representation type and spawning new subgoals for
 each of the operations. *)
Tactic Notation "hone" "representation" "using" open_constr(AbsR') :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_refine_All with (AbsR := AbsR');
    [ repeat (first [eapply refine_Constructors_nil
                    | eapply refine_Constructors_cons;
                      [ intros;
                        match goal with
                          |  |- refine _ (?E _) => let H := fresh in set (H := E)
                          | _ => idtac
                        end | ] ])
    | repeat (first [eapply refine_Methods_nil
                    | eapply refine_Methods_cons;
                      [ intros;
                        match goal with
                          |  |- refine _ (?E _ _) => let H := fresh in set (H := E)
                          | _ => idtac
                        end | ]
                    ])]
  | ].
