Require Import CertifiedExtraction.Extraction.QueryStructures.FiatBedrockLemmas.
Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.

Module WBagOfTuples2Compilation.
  Locate Module BagOfTuples2ADTSpec. (* FIXME ‘M-.’ on [BagOfTuples2ADTSpec] *)
  Include (BagOfTuples2ADTSpec WBagOfTuples2ADTSpecParams).
  (* FIXME generalize to other Tuple2 *)

  Local Notation BagWrapper k1 k2 := (WrapInstance (H := QS_WrapWBagOfTuples2 k1 k2)).
  Local Notation NTSomeBag k1 k2 v := (NTSome (H := BagWrapper k1 k2) v).
  Local Notation wrapBag k1 k2 v := (wrap (FacadeWrapper := BagWrapper k1 k2) v).

  Lemma CompileNew :
    forall vret vsize vkey1 vkey2 fpointer (env: Env ADTValue) ext tenv N (k1 k2: W),
      GLabelMap.find fpointer env = Some (Axiomatic New) ->
      Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
      Lifted_MapsTo ext tenv vkey1 (wrap k1) ->
      Lifted_MapsTo ext tenv vkey2 (wrap k2) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret ∉ ext ->
      Word.wlt k1 (Word.natToWord 32 N) ->
      Word.wlt k2 (Word.natToWord 32 N) ->
      ~ Word.wlt (Word.natToWord 32 N) (Word.natToWord 32 2) ->
      {{ tenv }}
        Call vret fpointer (vsize :: vkey1 :: vkey2 :: nil)
      {{ [[ NTSomeBag k1 k2 vret ->> @FiatWBagEmpty N as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    facade_eauto.
    unfold BagConstructor.
    repeat f_equal; facade_eauto.
    facade_eauto.
  Qed.

  Lemma CompileFindFirst :
    forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N (idx1 : Fin.t N)
           (k1 := (Word.natToWord 32 (projT1 (Fin.to_nat idx1)))) k2
           (table: FiatWBag N) (key: W)
           (table':= ( results <- {l : list RawTuple |
                                   IndexedEnsembles.EnsembleIndexedListEquivalence
                                     (IndexedEnsembles.IndexedEnsemble_Intersection
                                        (table)
                                        (fun x0 : RawTuple =>
                                           ((if Word.weq match MakeWordHeading_allWords idx1 in _ = W return W with
                                                         | eq_refl => GetAttributeRaw x0 idx1
                                                         end key then true else false) && true)%bool = true)) l};
                       ret (table, results))
                     : Comp (_ * list (FiatWTuple N))),
      GLabelMap.MapsTo fpointer (Axiomatic WBagOfTuples2ADTSpec.FindFirst) env ->
      Lifted_MapsTo ext tenv vtable (wrapBag k1 k2 table) ->
      Lifted_MapsTo ext tenv vkey (wrap key) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      NoDuplicates [[[vret; vtable; vkey]]] ->
      vret ∉ ext ->
      vtable ∉ ext ->
      (* IndexedEnsembles.UnConstrFreshIdx table idx -> *)
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
      {{ tenv }}
        Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
             :: [[ NTSomeBag k1 k2 vtable ->> fst retv as _ ]]
             :: [[ NTSome (H := (@WrapInstance _ _ QS_WrapFiatWTupleList)) vret ->> snd retv as _ ]]
             :: DropName vret (DropName vtable tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

    fiat_t.
    5:solve[repeat apply DropName_remove; eauto 1].
    4:solve[simpl; eauto using f_equal, ListWToTuple_Truncated_map_keepEq].
    3:solve[fiat_t].
    2:solve[fiat_t].

    wipe.

    apply Fiat_Bedrock_Filters_Equivalence; assumption.
  Qed.

  Lemma CompileFindFirst_spec :
    forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N
           (idx1 : Fin.t N)
           (k1 := (Word.natToWord 32 (projT1 (Fin.to_nat idx1))))
           k2
           (table: FiatWBag N) (key: W)
           (table':= ( results <- {l : list RawTuple |
                                   IndexedEnsembles.EnsembleIndexedListEquivalence
                                     (IndexedEnsembles.IndexedEnsemble_Intersection
                                        (table)
                                        (fun x0 : RawTuple =>
                                           ((if Word.weq match MakeWordHeading_allWords idx1 in _ = W return W with
                                                         | eq_refl => GetAttributeRaw x0 idx1
                                                         end key then true else false) && true)%bool = true)) l};
                       ret (table, results))
                     : Comp (_ * list (FiatWTuple N))),
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      GLabelMap.MapsTo fpointer (Axiomatic WBagOfTuples2ADTSpec.FindFirst) env ->
      StringMap.MapsTo vkey (wrap key) ext ->
      PreconditionSet tenv ext [[[vret; vtable]]] ->
      vret <> vkey ->
      vtable <> vkey ->
      TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
      {{ [[ NTSomeBag k1 k2 vtable ->> table as _]] :: tenv }}
        Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
             :: [[ NTSomeBag k1 k2 vtable ->> fst retv as _ ]]
             :: [[ NTSome vret (H := (@WrapInstance _ _ QS_WrapFiatWTupleList)) ->> snd retv as _ ]]
             :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply generalized CompileFindFirst; repeat (compile_do_side_conditions || Lifted_t || PreconditionSet_t).
    setoid_rewrite (DropName_NotInTelescope _ _ H12).
    rewrite DropName_Cons_None.
    setoid_rewrite (DropName_NotInTelescope _ _ H10).
    decide_TelEq_instantiate.
  Qed.

  Require Import CallRules.Tuple.

  Lemma CompileInsert :
    forall vret vtable vtuple fpointer (env: Env QsADTs.ADTValue) ext tenv N k1 k2 idx
      (table: FiatWBag N) (tuple: FiatWTuple N),
      GLabelMap.MapsTo fpointer (Axiomatic WBagOfTuples2ADTSpec.Insert) env ->
      Lifted_MapsTo ext tenv vtable (wrapBag k1 k2 table) ->
      Lifted_MapsTo ext tenv vtuple (wrap tuple) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      NoDuplicates [[[vret; vtable; vtuple]]] ->
      vret ∉ ext ->
      vtable ∉ ext ->
      vtuple ∉ ext ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW table) idx ->
      {{ tenv }}
        Call vret fpointer (vtable :: vtuple :: nil)
      {{ [[ ( freshIdx <- {freshIdx : nat | IndexedEnsembles.UnConstrFreshIdx table freshIdx};
                  ret (Ensembles.Add IndexedEnsembles.IndexedElement table
                                     {| IndexedEnsembles.elementIndex := freshIdx;
                                        IndexedEnsembles.indexedElement := tuple |})) as rep ]]
             :: [[`vret ->> (Word.natToWord 32 0) as _ ]]
             :: [[ (NTSomeBag k1 k2 vtable) ->> rep as _ ]]
             :: DropName vtable (DropName vret (DropName vtuple tenv)) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
    facade_eauto.
    fiat_t.
    apply minFresh_UnConstrFresh; eauto.
    facade_eauto.
    facade_eauto.

    unfold BagConstructor; repeat f_equal.
    apply Ensembles.Extensionality_Ensembles.

    lazymatch goal with
    | [ H: TuplesF.minFreshIndex _ ?x, H': TuplesF.minFreshIndex _ ?y |- _ ] =>
      learn (minFreshIndex_unique H H'); subst
    end.

    apply Fiat_Bedrock_Insert.
    repeat apply DropName_remove; eauto 1.
  Qed.

  Lemma CompileInsert_spec :
    forall vtmp vtable vtuple fpointer (env: Env QsADTs.ADTValue) ext tenv N k1 k2 idx
      (table: FiatWBag N) (tuple: FiatWTuple N),
      GLabelMap.MapsTo fpointer (Axiomatic WBagOfTuples2ADTSpec.Insert) env ->
      NoDuplicates [[[vtmp; vtable; vtuple]]] ->
      vtmp ∉ ext ->
      vtable ∉ ext ->
      vtuple ∉ ext ->
      NotInTelescope vtmp tenv ->
      NotInTelescope vtuple tenv ->
      NotInTelescope vtable tenv ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW table) idx ->
      {{ [[ (NTSomeBag k1 k2 vtable) ->> table as _ ]]
           :: [[ (NTSome (H := @WrapInstance _ _ WTupleCompilation.FiatWrapper) vtuple) ->> tuple as _ ]]
           :: tenv }}
        Call vtmp fpointer (vtable :: vtuple :: nil)
      {{ [[ ( freshIdx <- {freshIdx : nat | IndexedEnsembles.UnConstrFreshIdx table freshIdx};
                  ret (Ensembles.Add IndexedEnsembles.IndexedElement table
                                     {| IndexedEnsembles.elementIndex := freshIdx;
                                        IndexedEnsembles.indexedElement := tuple |})) as rep ]]
             :: [[ (NTSomeBag k1 k2 vtable) ->> rep as _ ]]
             :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros. PreconditionSet_t.
    apply ProgOk_Remove_Skip_R; hoare.
    apply generalized CompileInsert; repeat (compile_do_side_conditions || Lifted_t).
    eauto.
    apply ProgOk_Chomp_None; intros.
    repeat match goal with
           | [ H: NotInTelescope ?k ?tenv |- context[DropName ?k ?tenv] ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
           | _ => setoid_rewrite Propagate_anonymous_ret
           | _ => fold @DropName
           end.
    apply CompileDeallocW_discretely; repeat (compile_do_side_conditions || decide_NotInTelescope).
    apply CompileSkip.
  Qed.

  Lemma CompileFindSecond :
    forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N k1
      (table: FiatWBag N) (key: W) (idx2: Fin.t N)
      (k2 := (Word.natToWord 32 (projT1 (Fin.to_nat idx2))))
      (table':= ( results <- {l : list RawTuple |
                            IndexedEnsembles.EnsembleIndexedListEquivalence
                              (IndexedEnsembles.IndexedEnsemble_Intersection
                                 table
                                 (fun x0 : RawTuple =>
                                    ((if Word.weq match MakeWordHeading_allWords idx2 in _ = W return W with
                                                  | eq_refl => GetAttributeRaw x0 idx2
                                                  end key then true else false) && true)%bool =
                                    true)) l};
                   ret (table, results))%comp
               : Comp (_ * list (FiatWTuple N))),
      GLabelMap.MapsTo fpointer (Axiomatic WBagOfTuples2ADTSpec.FindSecond) env ->
      Lifted_MapsTo ext tenv vtable (wrapBag k1 k2 table) ->
      Lifted_MapsTo ext tenv vkey (wrap key) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      NoDuplicates [[[vret; vtable; vkey]]] ->
      vret ∉ ext ->
      vtable ∉ ext ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
      {{ tenv }}
        Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
             :: [[ NTSomeBag k1 k2 vtable ->> fst retv as _ ]]
             :: [[ NTSome vret (H := (@WrapInstance _ _ QS_WrapFiatWTupleList)) ->> snd retv as _ ]]
             :: DropName vret (DropName vtable tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
    fiat_t.

    5:solve[repeat apply DropName_remove; eauto 1].
    4:solve[simpl; eauto using f_equal, ListWToTuple_Truncated_map_keepEq].
    3:solve[fiat_t].
    2:solve[fiat_t].

    apply Fiat_Bedrock_Filters_Equivalence; eassumption.
  Qed.

  Lemma CompileFindSecond_spec :
    forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N k1
      (table: FiatWBag N) (key: W) (idx2: Fin.t N)
      (k2 := (Word.natToWord 32 (projT1 (Fin.to_nat idx2))))
      (table':= ( results <- {l : list RawTuple |
                            IndexedEnsembles.EnsembleIndexedListEquivalence
                              (IndexedEnsembles.IndexedEnsemble_Intersection
                                 table
                                 (fun x0 : RawTuple =>
                                    ((if Word.weq match MakeWordHeading_allWords idx2 in _ = W return W with
                                                  | eq_refl => GetAttributeRaw x0 idx2
                                                  end key then true else false) && true)%bool =
                                    true)) l};
                   ret (table, results))%comp
               : Comp (_ * list (FiatWTuple N))),
      GLabelMap.MapsTo fpointer (Axiomatic WBagOfTuples2ADTSpec.FindSecond) env ->
      StringMap.MapsTo vkey (wrap key) ext ->
      PreconditionSet tenv ext [[[vret; vtable]]] ->
      vret <> vkey ->
      vtable <> vkey ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
      {{ [[ NTSomeBag k1 k2 vtable ->> table as _]] :: tenv }}
        Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ NTSomeBag k1 k2 vtable ->> fst retv as _ ]]
           :: [[ NTSome vret (H := (@WrapInstance _ _ QS_WrapFiatWTupleList)) ->> snd retv as _ ]]
           :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply generalized CompileFindSecond; repeat (compile_do_side_conditions || Lifted_t || PreconditionSet_t).
    setoid_rewrite (DropName_NotInTelescope _ _ H12).
    rewrite DropName_Cons_None.
    setoid_rewrite (DropName_NotInTelescope _ _ H10).
    decide_TelEq_instantiate.
  Qed.
End WBagOfTuples2Compilation.