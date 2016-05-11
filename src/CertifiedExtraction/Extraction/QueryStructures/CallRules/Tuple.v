Require Export Fiat.Computation.Notations.
Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.

Module Type TupleCompilationParams (Params: TupleADTSpecParams).
  Import Params.
  Axiom FiatTuple : nat -> Type.
  Axiom FiatTupleToBedrockTuple : forall {n}, FiatTuple n -> GenericTuple FieldType.
  Axiom FiatTupleToBedrockTuple_inj :
    forall {N} (v v' : FiatTuple N), FiatTupleToBedrockTuple v = FiatTupleToBedrockTuple v' -> v = v'.
  Axiom FiatTupleToBedrockTuple_length :
    forall {N} (v: FiatTuple N), List.length (FiatTupleToBedrockTuple v) = N.
End TupleCompilationParams.

Module TupleCompilation
       (Params: TupleADTSpecParams)
       (CompilationParams: TupleCompilationParams Params).
  Module Import Specs := (TupleADTSpec Params).
  Export CompilationParams.

  Hint Resolve TupleConstructor_inj : inj_db.
  Hint Resolve FiatTupleToBedrockTuple_inj : inj_db.
  Hint Resolve FiatTupleToBedrockTuple_length : call_helpers_db.

  Instance BedrockWrapper : FacadeWrapper QsADTs.ADTValue (GenericTuple FieldType).
  Proof.
    refine {| wrap tp := TupleConstructor tp;
              wrap_inj := _ |}; eauto with inj_db.
  Defined.

  Instance FiatWrapper {N} : FacadeWrapper QsADTs.ADTValue (FiatTuple N).
  Proof.
    refine {| wrap tp := TupleConstructor (FiatTupleToBedrockTuple tp);
              wrap_inj := _ |}; eauto with inj_db.
  Defined.

  Lemma New_RunsTo_characterization:
    forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (fnew : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (w: W),
      StringMap.MapsTo vlen (wrap w) initial_state ->
      GLabelMap.MapsTo fnew (Axiomatic New) env ->
      RunsTo env (Call vtup fnew [[[vlen]]]) initial_state st' ->
      exists x1, M.Equal st' ([vtup |> ADT (TupleConstructor x1)]::initial_state) /\ Datatypes.length x1 = Word.wordToNat w.
  Proof.
    repeat QS_t.
    reflexivity.
  Qed.

  Lemma New_Safe:
    forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (fnew : GLabelMap.key) (initial_state : State QsADTs.ADTValue) (w: W),
      StringMap.MapsTo vlen (wrap w) initial_state ->
      GLabelMap.MapsTo fnew (Axiomatic New) env ->
      not_mapsto_adt vtup initial_state = true ->
      ~ Word.wlt w (Word.natToWord 32 2) ->
      Safe env (Call vtup fnew [[[vlen]]]) initial_state.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call).
  Qed.

  (* FIXME move *)
  Hint Rewrite Word.wordToNat_natToWord_idempotent : call_helpers_db.

  Lemma CompileDelete:
    forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
      (fpointer : GLabelMap.key) (tup : FiatTuple N),
      vtup <> vtmp ->
      vtmp ∉ ext ->
      vtup ∉ ext ->
      Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := FiatWrapper)) tup) ->
      Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
      Lifted_not_mapsto_adt ext tenv vtmp ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      GLabelMap.MapsTo fpointer (Axiomatic Delete) env ->
      {{ tenv }}
        Call vtmp fpointer (vtup :: vsize :: nil)
      {{ [[`vtmp ->> (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vtup tenv)) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
    autorewrite with call_helpers_db; facade_eauto.
    facade_eauto.
    repeat apply DropName_remove; eauto 1.
  Qed.

  Lemma CompileDelete_spec:
    forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
      (fpointer : GLabelMap.key) (tup : FiatTuple N),
      vtup <> vtmp ->
      vtup <> vsize ->
      vsize <> vtmp ->
      vtmp ∉ ext ->
      vtup ∉ ext ->
      vsize ∉ ext ->
      NotInTelescope vtmp tenv ->
      NotInTelescope vtup tenv ->
      NotInTelescope vsize tenv ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      GLabelMap.MapsTo fpointer (Axiomatic Delete) env ->
      {{ [[ (NTSome (H := WrapInstance (H := FiatWrapper)) vtup) ->> tup as _]] :: tenv }}
        (Seq (Assign vsize (Const (Word.natToWord 32 N))) (Call vtmp fpointer (vtup :: vsize :: nil)))
      {{ tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply ProgOk_Remove_Skip_R; hoare.
    hoare. apply CompileConstant; try compile_do_side_conditions.
    apply CompileDeallocW_discretely; try compile_do_side_conditions.
    apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros; computes_to_inv; subst; simpl.
    apply generalized CompileDelete; try (compile_do_side_conditions ||  Lifted_t).
    apply Lifted_MapsTo_Ext; compile_do_side_conditions.
    repeat match goal with
           | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
           | _ => setoid_rewrite Propagate_anonymous_ret
           end.
    apply CompileDeallocW_discretely; try compile_do_side_conditions.
    apply CompileSkip.
  Qed.
End TupleCompilation.

Module WTupleCompilationParams <: TupleCompilationParams (WTupleADTSpecParams).
  Definition FiatTuple N := @RawTuple (MakeWordHeading N).
  Definition FiatTupleToBedrockTuple {N} := TupleToListW (N := N).

  Lemma FiatTupleToBedrockTuple_inj :
    forall {N} (v v' : FiatTuple N),
      FiatTupleToBedrockTuple v = FiatTupleToBedrockTuple v' -> v = v'.
  Proof.
    eauto using TupleToListW_inj.
  Qed.

  Lemma FiatTupleToBedrockTuple_length :
    forall {N} (v: FiatTuple N),
      List.length (FiatTupleToBedrockTuple v) = N.
  Proof.
    intros.
    unfold FiatTupleToBedrockTuple.
    apply TupleToListW_length.
  Qed.
End WTupleCompilationParams.

Module WTupleCompilation.
  Include (TupleCompilation WTupleADTSpecParams WTupleCompilationParams).

  Lemma Set_RunsTo_characterization:
    forall (vlen vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (fset : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (tup: TuplesF.tupl) (val pos: W),
      StringMap.MapsTo v (wrap val) initial_state ->
      StringMap.MapsTo vpos (wrap pos) initial_state ->
      StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := BedrockWrapper)) tup) initial_state ->
      GLabelMap.MapsTo fset (Axiomatic WTupleADTSpec.Put) env ->
      RunsTo env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state st' ->
      M.Equal st' ([vtmp |> QsADTs.SCAZero]::[vtup |> ADT (QsADTs.WTuple (Array.upd tup pos val))]::initial_state).
  Proof.
    repeat QS_t.
    reflexivity.
  Qed.

  Lemma Set_Safe:
    forall (vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (fset : GLabelMap.key) (initial_state : State QsADTs.ADTValue) (tup: TuplesF.tupl) (val pos: W),
      StringMap.MapsTo v (wrap val) initial_state ->
      StringMap.MapsTo vpos (wrap pos) initial_state ->
      StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := BedrockWrapper)) tup) initial_state ->
      GLabelMap.MapsTo fset (Axiomatic WTupleADTSpec.Put) env ->
      not_mapsto_adt vtmp initial_state = true ->
      Word.wlt pos (IL.natToW (Datatypes.length tup)) ->
      Safe env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call).
  Qed.

  (* Remove Hints Bool.trans_eq_bool. *)

  Lemma CompileNew :
    forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key)
      (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (val1 val2 val3: W)
      (fnew fset : GLabelMap.key),
      NoDuplicates [[[v1;v2;v3;o1;o2;o3;vtup;vlen;vtmp]]] ->
      StringMap.MapsTo v1 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) val1) ext ->
      StringMap.MapsTo v2 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) val2) ext ->
      StringMap.MapsTo v3 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) val3) ext ->
      StringMap.MapsTo o1 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 0)) ext ->
      StringMap.MapsTo o2 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 1)) ext ->
      StringMap.MapsTo o3 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 2)) ext ->
      StringMap.MapsTo vlen (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 3)) ext ->
      NotInTelescope vtup tenv ->
      NotInTelescope vtmp tenv ->
      vtup ∉ ext ->
      vtmp ∉ ext ->
      GLabelMap.MapsTo fnew (Axiomatic WTupleADTSpec.New) env ->
      GLabelMap.MapsTo fset (Axiomatic WTupleADTSpec.Put) env ->
      {{ tenv }}
        (Seq (Call vtup fnew (vlen :: nil))
             (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                  (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                       (Call vtmp fset (vtup :: o3 :: v3 :: nil)))))
      {{ [[(NTSome (H := WrapInstance (H := FiatWrapper)) vtup) ->> ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: [[(NTSome (H := @FacadeWrapper_SCA QsADTs.ADTValue) vtmp) ->> (Word.natToWord 32 0) as _]]
           :: (DropName vtup (DropName vtmp tenv)) }} ∪ {{ ext }} // env.
  Proof.
    unfold ProgOk.
    repeat repeat match goal with
                  | _ => cleanup
                  | _ => reflexivity
                  | _ => progress unfold WTupleADTSpecParams.FieldType in *
                  | |- Safe _ (Seq _ _) _ => econstructor
                  | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] => inversion' H
                  | _ => eapply SameValues_MapsTo_Ext_State; eassumption
                  | _ => eapply StringMap.add_1; [ congruence ]
                  | _ => eapply StringMap.add_2; [ PreconditionSet_t; congruence | ]
                  | [  |- context[Datatypes.length (Array.upd _ _ _)] ] => rewrite Arrays.upd_length
                  | [ H: RunsTo _ _ _ _ |- _ ] =>
                    eapply New_RunsTo_characterization in H; [ | clear H; try eassumption.. ]
                  | [ H: RunsTo _ _ _ _ |- _ ] =>
                    eapply Set_RunsTo_characterization in H; [ | clear H; try eassumption.. ]
                  | [  |- Safe _ _ _ ] => eapply New_Safe
                  | [  |- Safe _ _ _ ] => eapply Set_Safe
                  | [ H: StringMap.Equal ?m1 ?m2 |- StringMap.MapsTo _ _ ?m1 ] => rewrite H
                  | [ H: StringMap.Equal ?m1 ?m2 |- not_mapsto_adt _ _ = _ ] => rewrite H
                  | [ H: StringMap.Equal ?m1 ?m2 |- Safe _ _ ?m1 ] => rewrite H
                  | [ H: ?a = _ |- context[?a] ] => rewrite H
                  | [ |- not_mapsto_adt _ _ = true ] => solve [not_mapsto_adt_external_t; facade_eauto]
                  end.

    repeat StringMap_t.

    Ltac cleanup_StringMap_head :=
      repeat ((rewrite <- add_remove_comm; [ | PreconditionSet_t; congruence ])
              || (rewrite remove_trickle; [ | reflexivity])).

    apply TelEq_swap.

    wipe.                         (* FIXME remove this *)
    repeat match goal with
           | [ H: _ <> _ |- _ ] => clear dependent H
           end.

    change QsADTs.SCAZero with (wrap (WrappingType := (Value QsADTs.ADTValue)) (Word.natToWord 32 0)).
    apply SameValues_Pop_Both; [ apply (eq_ret_compute eq_refl) | ].
    cleanup_StringMap_head.

    replace (Array.upd (Array.upd (Array.upd x (Word.natToWord 32 0) val1) (Word.natToWord 32 1) val2)
                       (Word.natToWord 32 2) val3) with [[[val1; val2; val3]]].
    change (ADT (QsADTs.WTuple [[[val1; val2; val3]]])) with
    (wrap (WrappingType := (Value QsADTs.ADTValue)) (ListWToTuple [[[val1; val2; val3]]])).
    apply SameValues_Pop_Both; [ apply (eq_ret_compute eq_refl) | ].
    cleanup_StringMap_head.

    repeat apply DropName_remove; try eassumption.

    do 4 try destruct x as [ | ? x ];
      match goal with
      | [ H: context[Datatypes.length] |- _ ] => simpl in H; try discriminate H
      end.
    reflexivity.
  Qed.

  Lemma CompileNew_spec :
    forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
      (val1 val2 val3: W) setup
      (fnew fset : GLabelMap.key),
      NoDuplicates [[[v1;v2;v3;o1;o2;o3;vtup;vlen;vtmp]]] ->
      vlen ∉ ext -> NotInTelescope vlen tenv ->
      o3 ∉ ext -> NotInTelescope o3 tenv ->
      o2 ∉ ext -> NotInTelescope o2 tenv ->
      o1 ∉ ext -> NotInTelescope o1 tenv ->
      v3 ∉ ext -> NotInTelescope v3 tenv ->
      v2 ∉ ext -> NotInTelescope v2 tenv ->
      v1 ∉ ext -> NotInTelescope v1 tenv ->
      NotInTelescope vtup tenv -> NotInTelescope vtmp tenv ->
      vtup ∉ ext ->
      vtmp ∉ ext ->
      GLabelMap.MapsTo (elt:=FuncSpec QsADTs.ADTValue) fnew (Axiomatic WTupleADTSpec.New) env ->
      GLabelMap.MapsTo (elt:=FuncSpec QsADTs.ADTValue) fset (Axiomatic WTupleADTSpec.Put) env ->
      {{ tenv }}
        setup
      {{ [[`v1 ->> val1 as _]]
           :: [[`v2 ->> val2 as _]]
           :: [[`v3 ->> val3 as _]]
           :: [[`o1 ->> (Word.natToWord 32 0) as _]]
           :: [[`o2 ->> (Word.natToWord 32 1) as _]]
           :: [[`o3 ->> (Word.natToWord 32 2) as _]]
           :: [[`vlen ->> (Word.natToWord 32 3) as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        (Seq setup
             (Seq (Call vtup fnew (vlen :: nil))
                  (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                       (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                            (Call vtmp fset (vtup :: o3 :: v3 :: nil))))))
      {{ [[`vtup ->> ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
             :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply ProgOk_Remove_Skip_R.
    hoare. hoare. PreconditionSet_t.
    side_conditions_fast.
    computes_to_inv; subst.
    apply generalized CompileNew;
      repeat match goal with
             | _ => congruence
             | _ => decide_not_in
             | _ => decide_mapsto_maybe_instantiate
             | _ => compile_do_side_conditions
             end.
    apply ProgOk_Chomp_Some; try side_conditions_fast. intros.
    PreconditionSet_t; side_conditions_fast; apply CompileSkip.
  Qed.

  Lemma CompileGet_helper :
    forall N (idx: (Fin.t N)), (@Vector.nth Type (NumAttr (MakeWordHeading N)) (AttrList (MakeWordHeading N)) idx) = W.
  Proof.
    induction idx; eauto.
  Defined.

  Lemma CompileGet_goodSize_helper:
    forall (N : nat) (idx : Fin.t N),
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      IL.goodSize (` (Fin.to_nat idx)).
  Proof.
    intros *.
    pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
    apply NPeano.Nat.le_exists_sub in h; repeat cleanup.
    assert (IL.goodSize N) as h.
    eassumption.
    rewrite H0 in h.
    eapply Arrays.goodSize_plus_r.
    rewrite NPeano.Nat.add_succ_r in h.
    rewrite <- NPeano.Nat.add_succ_l in h.
    eassumption.
  Defined.

  Lemma CompileGet_helper':
    forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      Word.wlt (Word.natToWord 32 (` (Fin.to_nat idx))) (IL.natToW (Datatypes.length (TupleToListW tup))).
  Proof.
    intros. rewrite TupleToListW_length by assumption.
    pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
    apply Arrays.lt_goodSize; try eassumption.
    apply CompileGet_goodSize_helper; assumption.
  Qed.

  Hint Resolve CompileGet_helper' : call_helpers_db.

  Lemma CompileGet_helper'':
    forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      nth_error (TupleToListW tup) (` (Fin.to_nat idx)) =
      Some (match CompileGet_helper idx in (_ = W) return (Vector.nth (MakeVectorOfW N) idx -> W) with
            | eq_refl => fun t : Vector.nth (MakeVectorOfW N) idx => t
            end (ilist2.ith2 tup idx)).
  Proof.
    intros.
    induction idx; simpl.
    - reflexivity.
    - destruct (Fin.to_nat idx); simpl.
      rewrite IHidx.
      + reflexivity.
      + apply BinNat.N.lt_succ_l.
        rewrite Nnat.Nat2N.inj_succ in H; assumption.
  Qed.

  Lemma CompileGet:
    forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
      (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
      vtup <> vret ->
      vret ∉ ext ->
      Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (FiatWrapper))) tup) ->
      Lifted_MapsTo ext tenv vpos (wrap (Word.natToWord 32 (proj1_sig (Fin.to_nat idx)))) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      GLabelMap.MapsTo fpointer (Axiomatic WTupleADTSpec.Get) env ->
      {{ tenv }}
        Call vret fpointer (vtup :: vpos :: nil)
      {{ [[(NTSome (H := FacadeWrapper_SCA) vret) ->>
                                                   (match CompileGet_helper idx in _ = W return _ -> W with
                                                    | eq_refl => fun t => t
                                                    end) (ilist2.ith2 tup idx) as _]]
             :: (DropName vret tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

    facade_eauto.
    rewrite Word.wordToNat_natToWord_idempotent by
        (apply (CompileGet_goodSize_helper idx); assumption).
    rewrite CompileGet_helper'' by congruence; reflexivity.
    rewrite <- remove_add_comm by congruence.
    setoid_rewrite <- add_redundant_cancel; try eassumption.
    repeat apply DropName_remove; eauto 1.
  Qed.

  Lemma CompileGet_spec:
    forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
      (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
      PreconditionSet tenv ext [[[vtup; vret; vpos]]] ->
      vret ∉ ext ->
      vtup ∉ ext ->
      NotInTelescope vret tenv ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      GLabelMap.MapsTo fpointer (Axiomatic WTupleADTSpec.Get) env ->
      {{ [[ `vtup ->> tup as _ ]] :: tenv }}
        (Seq (Assign vpos (Const (Word.natToWord 32 (proj1_sig (Fin.to_nat idx))))) (Call vret fpointer (vtup :: vpos :: nil)))
      {{ [[ `vtup ->> tup  as _]]
           :: [[(NTSome (H := FacadeWrapper_SCA) vret) ->> (match CompileGet_helper idx in _ = W return _ -> W with
                                                        | eq_refl => fun t => t
                                                        end) (ilist2.ith2 tup idx) as _]]
           :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    hoare.
    apply CompileConstant; try compile_do_side_conditions.
    apply CompileDeallocW_discretely; try compile_do_side_conditions.
    apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
    apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.

    remember (match CompileGet_helper idx in (_ = W) return (Vector.nth (AttrList (MakeWordHeading N)) idx -> W) with
        | eq_refl => fun t : Vector.nth (AttrList (MakeWordHeading N)) idx => t
              end (ilist2.ith2 tup idx)). (* Otherwise Coq crashes *)
    setoid_replace tenv with (DropName vret tenv) using relation (@TelStrongEq QsADTs.ADTValue) at 2.
    computes_to_inv;
      subst; apply CompileGet; repeat (PreconditionSet_t || compile_do_side_conditions || decide_not_in || Lifted_t).
    apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
    apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
    symmetry; apply DropName_NotInTelescope; assumption.
  Qed.
End WTupleCompilation.