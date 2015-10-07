Require Import FiatToFacade.Compiler.
Require Import FiatToFacade.Compiler.Automation.Vacuum.
Require Import FiniteSetADTs FiniteSetADTs.FiniteSetADTMethodLaws.
Require Import Coq.Lists.List DFacade.

Lemma compile_FiniteSetAndFunctionOfList_SCA (FiniteSetImpl : FullySharpened FiniteSetSpec)
      f (x : W) ls
      tis_empty thead vadt vdiscard {vret}
      flistrev flistempty flistpop fsetempty fsetdelete
      {env}
      {vls}
      init_knowledge
      init_scas init_adts
:
  GLabelMap.find (elt:=FuncSpec ADTValue) flistrev env = Some (Axiomatic List_rev) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistempty env = Some (Axiomatic List_empty) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistpop env = Some (Axiomatic List_pop) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) fsetempty env = Some (Axiomatic FEnsemble_sEmpty) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) fsetdelete env = Some (Axiomatic FEnsemble_sDelete) ->
  vret <> vadt ->
  vret <> vls ->
  vret <> tis_empty ->
  vadt <> vls ->
  vadt <> tis_empty ->
  thead <> vret ->
  thead <> vadt ->
  thead <> vls ->
  vls <> vret ->
  tis_empty <> vls ->
  vls <> vdiscard ->
  vadt <> vdiscard ->
  vret <> vdiscard ->
  ~ StringMap.In vadt init_adts ->
  ~ StringMap.In vret init_adts ->
  ~ StringMap.In thead init_adts ->
  ~ StringMap.In tis_empty init_adts ->
  ~ StringMap.In vdiscard init_adts ->
  ~ StringMap.In vdiscard init_scas ->
  ~ StringMap.In vadt init_scas ->
  ~ StringMap.In vls init_scas ->
  ~ StringMap.In tis_empty init_scas ->
  refine (@Prog _ env init_knowledge
                init_scas ([vret >sca> (snd (FiniteSetAndFunctionOfList FiniteSetImpl f x ls))] :: init_scas)
                ([vls >adt> List ls]::init_adts)
                ([vls >adt> List nil]::init_adts))
         (cloop <- { cloop : Stmt
                    | PairLoopBodyOk
                        env
                        (fun xs_acc w =>
                           ValidFiniteSetAndFunctionOfList_body
                             FiniteSetImpl
                              f
                             w
                             xs_acc)
                        cloop init_knowledge init_scas init_adts vls vret vadt thead tis_empty snd
                        (fun xs_acc =>
                           FEnsemble (to_ensemble FiniteSetImpl (projT1 (fst xs_acc)))) };
          ret
            (Seq
               (Seq (Call vdiscard flistrev (cons vls nil))
                    (Seq (Assign vret (Const x))
                         (Seq (Call vadt fsetempty nil)
                              (Fold thead tis_empty vls flistpop flistempty cloop))))
               (Call vdiscard fsetdelete (cons vadt nil)))).
Proof.
  intros.
  rewrite FiniteSetAndFunctionOfList_ValidFiniteSetAndFunctionOfList.
  unfold ValidFiniteSetAndFunctionOfList.
  rewrite <- (@rev_involutive _ ls).
  rewrite !fold_left_rev_right.
  rewrite -> (@rev_involutive _ ls).
  simpl.

  rewrite (compile_pair_sca vadt (fun x => FEnsemble (to_ensemble _ (projT1 (fst x))))).

  rewrite (fun b => @compile_list_rev_general env flistrev vdiscard vls b _ _ _); try first [ eassumption | rewrite add_add_add'; reflexivity | vacuum ].

  rewrite add_add_add'.
  setoid_rewrite (compile_fold_pair env _ snd (fun x => FEnsemble (to_ensemble _ (projT1 (fst x)))) vls vret vadt thead tis_empty flistpop flistempty); try first [ eassumption | solve [map_iff_solve intuition] | vacuum ].

  simpl.
  unfold W.
  apply General.refine_under_bind.

  intros.
  rewrite compile_constant; try vacuum.
  rewrite compile_AbsImpl_sEmpty; first [ eassumption | solve [map_iff_solve eauto] | vacuum ].
  erewrite (@compile_AbsImpl_sDelete _ _ _ vdiscard); try first [ eassumption | solve [map_iff_solve eauto] | vacuum ].

  reflexivity.
Qed.
Unset Implicit Arguments.
Lemma compile_adt_pair :
  forall {pair_type av env knowledge} vadt1 vadt2 (wadt1: pair_type -> av) (wadt2: pair_type -> av) adts inter_adts final_adts scas pair,
    refine
    (@Prog av env knowledge
           scas scas
           adts ([vadt2 >adt> wadt2 pair]::final_adts))
    (p <- (@Prog av env knowledge
                 scas scas
                 adts ([vadt1 >adt> wadt1 pair]::[vadt2 >adt> wadt2 pair]::inter_adts));
     cleanup <- (@Prog av env knowledge
                       scas scas
                       ([vadt1 >adt> wadt1 pair]::[vadt2 >adt> wadt2 pair]::inter_adts)
                       ([vadt2 >adt> wadt2 pair]::final_adts));
     ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  repeat (safe_seq; intros).
  specialize_states.
  assumption.

  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto.
  intuition.
Qed.

Lemma compile_FiniteSetAndFunctionOfList_ADT (FiniteSetImpl : FullySharpened FiniteSetSpec)
      f ls
      tis_empty thead vadt vdiscard {vret}
      flistrev flistempty flistpop flistnew fsetempty fsetdelete
      {env}
      {vls}
      init_knowledge
      init_scas init_adts
:
  GLabelMap.find (elt:=FuncSpec ADTValue) flistrev env = Some (Axiomatic List_rev) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistempty env = Some (Axiomatic List_empty) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistpop env = Some (Axiomatic List_pop) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistnew env = Some (Axiomatic List_new) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) fsetempty env = Some (Axiomatic FEnsemble_sEmpty) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) fsetdelete env = Some (Axiomatic FEnsemble_sDelete) ->
  vret <> vadt ->
  vret <> vls ->
  vret <> tis_empty ->
  vadt <> vls ->
  vadt <> tis_empty ->
  thead <> vret ->
  thead <> vadt ->
  thead <> vls ->
  vls <> vret ->
  tis_empty <> vls ->
  vls <> vdiscard ->
  vadt <> vdiscard ->
  vret <> vdiscard ->
  ~ StringMap.In vadt init_adts ->
  ~ StringMap.In vret init_adts ->
  ~ StringMap.In thead init_adts ->
  ~ StringMap.In tis_empty init_adts ->
  ~ StringMap.In vdiscard init_adts ->
  ~ StringMap.In vret init_scas ->
  ~ StringMap.In vdiscard init_scas ->
  ~ StringMap.In vadt init_scas ->
  ~ StringMap.In vls init_scas ->
  ~ StringMap.In tis_empty init_scas ->
  refine (@Prog _ env init_knowledge
                init_scas (init_scas)
                ([vls >adt> List ls]::init_adts)
                ([vret >adt> List (snd (FiniteSetAndFunctionOfList FiniteSetImpl f nil ls))] :: [vls >adt> List nil]::init_adts))
         (cloop <- { cloop : Stmt
                    | ADTPairLoopBodyOk
                        env
                        (fun xs_acc w =>
                           ValidFiniteSetAndFunctionOfList_body
                             FiniteSetImpl
                              f
                             w
                             xs_acc)
                        cloop init_knowledge init_scas init_adts vls vadt vret thead tis_empty
                        (fun xs_acc =>
                           FEnsemble (to_ensemble FiniteSetImpl (projT1 (fst xs_acc))))  (fun x => List (snd x)) };
          ret
            (Seq
               (Seq (Call vdiscard flistrev (cons vls nil))
                    (Seq (Call vret flistnew nil)
                         (Seq (Call vadt fsetempty nil)
                              (Fold thead tis_empty vls flistpop flistempty cloop))))
               (Call vdiscard fsetdelete (cons vadt nil)))).
Proof.
  intros.
  rewrite FiniteSetAndFunctionOfList_ValidFiniteSetAndFunctionOfList.
  unfold ValidFiniteSetAndFunctionOfList.
  rewrite <- (@rev_involutive _ ls).
  rewrite !fold_left_rev_right.
  rewrite -> (@rev_involutive _ ls).
  simpl.

  setoid_rewrite (compile_adt_pair vadt vret (fun x => FEnsemble (to_ensemble _ (projT1 (fst x)))) (fun x => List (snd x))).

  rewrite (fun b => @compile_list_rev_general env flistrev vdiscard vls b _ _ _); try first [ eassumption | rewrite add_add_add'; reflexivity | vacuum ].

  rewrite add_add_add'.
  setoid_rewrite (compile_fold_pair_adt env _ (fun x => FEnsemble (to_ensemble _ (projT1 (fst x))))  (fun x => List (snd x)) vls vadt vret thead tis_empty flistpop flistempty); try first [ eassumption | solve [map_iff_solve intuition] | vacuum ].

  simpl.
  unfold W.
  apply General.refine_under_bind.

  intros.
  rewrite compile_list_new; first [ eassumption | solve [map_iff_solve eauto] | vacuum ].
  rewrite compile_AbsImpl_sEmpty; first [ eassumption | solve [map_iff_solve eauto] | vacuum ].
  erewrite (@compile_AbsImpl_sDelete _ _ _ vdiscard); try first [ eassumption | solve [map_iff_solve eauto] | vacuum ].

  reflexivity.
Qed.

Require Import Computation.ApplyMonad.

Lemma compile_fold_right_adt :
  forall {env : GLabelMap.t (FuncSpec ADTValue)} {acc_type : Type}
         {wrapper : acc_type -> ADTValue}
         (vseq vret thead tis_empty vdiscard: StringMap.key) (fpop fempty frev : GLabelMap.key)
         (loop : W -> acc_type -> acc_type) (knowledge : Prop)
         (scas adts : StringMap.t (Value ADTValue)),
    GLabelMap.find (elt:=FuncSpec ADTValue) fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find (elt:=FuncSpec ADTValue) fpop env = Some (Axiomatic List_pop) ->
    GLabelMap.find (elt:=FuncSpec ADTValue) frev env = Some (Axiomatic List_rev) ->
    vret <> vseq ->
    vret <> tis_empty ->
    vseq <> vdiscard ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In (elt:=Value ADTValue) tis_empty adts ->
    ~ StringMap.In (elt:=Value ADTValue) tis_empty scas ->
    ~ StringMap.In (elt:=Value ADTValue) thead adts ->
    ~ StringMap.In (elt:=Value ADTValue) vdiscard adts ->
    ~ StringMap.In (elt:=Value ADTValue) vdiscard scas ->
    ~ StringMap.In (elt:=Value ADTValue) vseq scas ->
    forall (seq : list W) (init : acc_type),
      refine
        (@Prog _ env knowledge
               scas scas
               ([vseq >> ADT (List seq)]::adts)
               ([vret >> ADT (wrapper (fold_right loop init seq))]::[vseq >> ADT (List nil)]::adts))
        (cloop <- {cloop : Stmt | ADTLoopBodyOk env (fun acc x => loop x acc) cloop knowledge scas adts vseq vret thead tis_empty wrapper};
         pinit <- (@Prog _ env knowledge
                         scas scas
                         ([vseq >> ADT (List (rev seq))]::adts)
                         ([vret >> ADT (wrapper init)]::[vseq >> ADT (List (rev seq))]::adts));
         ret (Seq (Call vdiscard frev (cons vseq nil))
                  (Seq pinit (Fold thead tis_empty vseq fpop fempty cloop)))).
Proof.
  intros.
  erewrite (@compile_list_rev_general _ _ vdiscard vseq seq); first [ eassumption | map_iff_solve intuition ].
  rewrite add_add_add'.
  rewrite <- (rev_involutive seq).
  rewrite fold_left_rev_right.
  rewrite (rev_involutive seq).
  rewrite (@compile_fold_adt _ _ _ vseq vret thead tis_empty); eauto.
  simplify with monad laws.

  apply General.refine_under_bind; intros.
  apply General.refine_under_bind; intros.

  reflexivity.
Qed.
