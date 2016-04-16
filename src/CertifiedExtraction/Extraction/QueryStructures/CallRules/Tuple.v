Require Export Fiat.Computation.Notations.
Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.

Lemma CompileTuple_new_RunsTo_characterization:
  forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fnew : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (w: W),
    StringMap.MapsTo vlen (wrap w) initial_state ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.Tuple_new) env ->
    RunsTo env (Call vtup fnew [[[vlen]]]) initial_state st' ->
    exists x1, M.Equal st' ([vtup <-- ADT (QsADTs.Tuple x1)]::initial_state) /\ Datatypes.length x1 = Word.wordToNat w.
Proof.
  repeat QS_t.
  reflexivity.
Qed.

Lemma CompileTuple_set_RunsTo_characterization:
  forall (vlen vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fset : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (tup: TuplesF.tupl) (val pos: W),
    StringMap.MapsTo v (wrap val) initial_state ->
    StringMap.MapsTo vpos (wrap pos) initial_state ->
    StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapBedrockTuple))) tup) initial_state ->
    GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env ->
    RunsTo env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state st' ->
    M.Equal st' ([vtmp <-- QsADTs.SCAZero]::[vtup <-- ADT (QsADTs.Tuple (Array.upd tup pos val))]::initial_state).
Proof.
  repeat QS_t.
  reflexivity.
Qed.

Lemma CompileTuple_set_Safe:
  forall (vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fset : GLabelMap.key) (initial_state : State QsADTs.ADTValue) (tup: TuplesF.tupl) (val pos: W),
    StringMap.MapsTo v (wrap val) initial_state ->
    StringMap.MapsTo vpos (wrap pos) initial_state ->
    StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapBedrockTuple))) tup) initial_state ->
    GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env ->
    not_mapsto_adt vtmp initial_state = true ->
    Word.wlt pos (IL.natToW (Datatypes.length tup)) ->
    Safe env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call).
Qed.

Lemma CompileTuple_new_Safe:
  forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fnew : GLabelMap.key) (initial_state : State QsADTs.ADTValue) (w: W),
    StringMap.MapsTo vlen (wrap w) initial_state ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.Tuple_new) env ->
    not_mapsto_adt vtup initial_state = true ->
    ~ Word.wlt w (Word.natToWord 32 2) ->
    Safe env (Call vtup fnew [[[vlen]]]) initial_state.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call).
Qed.

(* Remove Hints Bool.trans_eq_bool. *)

Lemma CompileTuple_new :
  forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
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
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.Tuple_new) env ->
    GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env ->
    {{ tenv }}
      (Seq (Call vtup fnew (vlen :: nil))
           (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                     (Call vtmp fset (vtup :: o3 :: v3 :: nil)))))
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTuple)) vtup) <-- ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: [[(NTSome (H := @FacadeWrapper_SCA QsADTs.ADTValue) vtmp) <-- (Word.natToWord 32 0) as _]]
           :: (DropName vtup (DropName vtmp tenv)) }} ∪ {{ ext }} // env.
Proof.
  unfold ProgOk.
  Time repeat repeat match goal with
                     | _ => cleanup
                     | _ => reflexivity
                     | |- Safe _ (Seq _ _) _ => econstructor
                     | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] => inversion' H
                     | _ => eapply SameValues_MapsTo_Ext_State; eassumption
                     | _ => eapply StringMap.add_1; [ congruence ]
                     | _ => eapply StringMap.add_2; [ PreconditionSet_t; congruence | ]
                     | [  |- context[Datatypes.length (Array.upd _ _ _)] ] => rewrite Arrays.upd_length
                     | [ H: RunsTo _ _ _ _ |- _ ] =>
                       eapply CompileTuple_new_RunsTo_characterization in H; [ | clear H; try eassumption.. ]
                     | [ H: RunsTo _ _ _ _ |- _ ] =>
                       eapply CompileTuple_set_RunsTo_characterization in H; [ | clear H; try eassumption.. ]
                     | [  |- Safe _ _ _ ] => eapply CompileTuple_new_Safe
                     | [  |- Safe _ _ _ ] => eapply CompileTuple_set_Safe
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
  change (ADT (QsADTs.Tuple [[[val1; val2; val3]]])) with
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

Print Assumptions CompileTuple_new.

Lemma CompileTuple_new_spec :
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
    GLabelMap.MapsTo (elt:=FuncSpec QsADTs.ADTValue) fnew (Axiomatic QsADTs.Tuple_new) env ->
    GLabelMap.MapsTo (elt:=FuncSpec QsADTs.ADTValue) fset (Axiomatic QsADTs.Tuple_set) env ->
    {{ tenv }}
      setup
    {{ [[`v1 <-- val1 as _]]
           :: [[`v2 <-- val2 as _]]
           :: [[`v3 <-- val3 as _]]
           :: [[`o1 <-- (Word.natToWord 32 0) as _]]
           :: [[`o2 <-- (Word.natToWord 32 1) as _]]
           :: [[`o3 <-- (Word.natToWord 32 2) as _]]
           :: [[`vlen <-- (Word.natToWord 32 3) as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq setup
           (Seq (Call vtup fnew (vlen :: nil))
                (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                     (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                          (Call vtmp fset (vtup :: o3 :: v3 :: nil))))))
    {{ [[`vtup <-- ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R.
  hoare. hoare. PreconditionSet_t.
  side_conditions_fast.
  computes_to_inv; subst.
  apply generalized CompileTuple_new;
    repeat match goal with
           | _ => congruence
           | _ => decide_not_in
           | _ => decide_mapsto_maybe_instantiate
           | _ => compile_do_side_conditions
           end.
  apply ProgOk_Chomp_Some; try side_conditions_fast. intros.
  PreconditionSet_t; side_conditions_fast; apply CompileSkip.
Qed.

Lemma CompileTuple_Delete:
  forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (tup : FiatTuple N),
    vtup <> vtmp ->
    vtmp ∉ ext ->
    vtup ∉ ext ->
    (* vsize ∉ ext -> *)
    Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) ->
    Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vtup :: vsize :: nil)
    {{ [[`vtmp <-- (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vtup tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuple_Delete_spec:
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
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_delete) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTuple (N := N)))) vtup) <-- tup as _]] :: tenv }}
      (Seq (Assign vsize (Const (Word.natToWord 32 N))) (Call vtmp fpointer (vtup :: vsize :: nil)))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  hoare. apply CompileConstant; try compile_do_side_conditions.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros; computes_to_inv; subst; simpl.
  apply generalized CompileTuple_Delete; try (compile_do_side_conditions ||  Lifted_t).
  apply Lifted_MapsTo_Ext; compile_do_side_conditions.
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.

Lemma CompileTuple_Get_helper :
  forall N (idx: (Fin.t N)), (@Vector.nth Type (NumAttr (MakeWordHeading N)) (AttrList (MakeWordHeading N)) idx) = W.
Proof.
  induction idx; eauto.
Defined.

Lemma CompileTuple_get_helper:
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

Lemma CompileTuple_get_helper':
  forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    Word.wlt (Word.natToWord 32 (` (Fin.to_nat idx))) (IL.natToW (Datatypes.length (TupleToListW tup))).
Proof.
  intros. rewrite TupleToListW_length by assumption.
  rewrite Word.wordToNat_natToWord_idempotent by assumption.
  pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
  apply Arrays.lt_goodSize; try eassumption.
  apply CompileTuple_get_helper; assumption.
Qed.

Hint Resolve CompileTuple_get_helper' : call_helpers_db.

Lemma CompileTuple_get_helper'':
  forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (match CompileTuple_Get_helper idx in (_ = W) return (Vector.nth (MakeVectorOfW N) idx -> W) with
     | eq_refl => fun t : Vector.nth (MakeVectorOfW N) idx => t
     end (ilist2.ith2 tup idx)) = Array.sel (TupleToListW tup) (Word.natToWord 32 (` (Fin.to_nat idx))).
Proof.
  unfold Array.sel.
  intros.
  rewrite Word.wordToNat_natToWord_idempotent by (apply (CompileTuple_get_helper idx); assumption).
  induction idx; simpl; try rewrite IHidx.
  - reflexivity.
  - destruct tup; simpl.
    unfold TupleToListW, ilist2.ilist2_hd, ilist2.ilist2_tl; simpl.
    destruct (Fin.to_nat idx); simpl; reflexivity.
  - apply BinNat.N.lt_succ_l.
    rewrite Nnat.Nat2N.inj_succ in H.
    assumption.
Qed.

Lemma CompileTuple_Get:
  forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
    vtup <> vret ->
    vret ∉ ext ->
    Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) ->
    Lifted_MapsTo ext tenv vpos (wrap (Word.natToWord 32 (proj1_sig (Fin.to_nat idx)))) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_get) env ->
    {{ tenv }}
      Call vret fpointer (vtup :: vpos :: nil)
    {{ [[(NTSome (H := FacadeWrapper_SCA) vret) <--
                                                 (match CompileTuple_Get_helper idx in _ = W return _ -> W with
                                                  | eq_refl => fun t => t
                                                  end) (ilist2.ith2 tup idx) as _]]
           :: (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  rewrite <- CompileTuple_get_helper'' by congruence; reflexivity.
  rewrite <- remove_add_comm by congruence.
  setoid_rewrite <- add_redundant_cancel; try eassumption.
  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuple_Get_spec:
  forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
    PreconditionSet tenv ext [[[vtup; vret; vpos]]] ->
    vret ∉ ext ->
    vtup ∉ ext ->
    NotInTelescope vret tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_get) env ->
    {{ [[ `vtup <-- tup as _ ]] :: tenv }}
      (Seq (Assign vpos (Const (Word.natToWord 32 (proj1_sig (Fin.to_nat idx))))) (Call vret fpointer (vtup :: vpos :: nil)))
    {{ [[ `vtup <-- tup  as _]]
         :: [[(NTSome (H := FacadeWrapper_SCA) vret) <-- (match CompileTuple_Get_helper idx in _ = W return _ -> W with
                                                      | eq_refl => fun t => t
                                                      end) (ilist2.ith2 tup idx) as _]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  hoare.
  apply CompileConstant; try compile_do_side_conditions.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.

  remember (match CompileTuple_Get_helper idx in (_ = W) return (Vector.nth (AttrList (MakeWordHeading N)) idx -> W) with
      | eq_refl => fun t : Vector.nth (AttrList (MakeWordHeading N)) idx => t
            end (ilist2.ith2 tup idx)). (* Otherwise Coq crashes *)
  setoid_replace tenv with (DropName vret tenv) using relation (@TelStrongEq QsADTs.ADTValue) at 2.
  computes_to_inv;
    subst; apply CompileTuple_Get; repeat (PreconditionSet_t || compile_do_side_conditions || decide_not_in || Lifted_t).
  apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
  apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
  symmetry; apply DropName_NotInTelescope; assumption.
Qed.
