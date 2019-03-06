Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.
Require Import CertifiedExtraction.Extraction.External.Loops.
Require Import CertifiedExtraction.Extraction.External.FacadeLoops.
Require Import CertifiedExtraction.Extraction.External.Lists.

Lemma map_inj {A B}:
  forall (f: A -> B),
    (forall x y, f x = f y -> x = y) ->
    (forall x y, (map f) x = (map f) y -> x = y).
Proof.
  induction x; destruct y; simpl; intros HH; try congruence.
  inversion' HH; f_equal; eauto.
Qed.

Instance WrapList {A B} {Wrp: FacadeWrapper A B} : FacadeWrapper (list A) (list B).
Proof.
  refine {| wrap x := map wrap x |}.
  eauto using map_inj, wrap_inj.
Qed.

Hint Resolve map_inj : inj_db.

Module Type ADTListCompilationParams (Import Params: ADTListADTSpecParams).
  Parameter TypeIndex : Type.
  Parameter RealElemType : TypeIndex -> Type.
  Parameter RealElemToElem : forall index, (RealElemType index) -> ElemType.
  Axiom RealElemToElem_inj : forall idx, Injective (@RealElemToElem idx).
End ADTListCompilationParams.

Module ADTListCompilation
       (Import Params: ADTListADTSpecParams)
       (Import CompilationParams: ADTListCompilationParams Params).
  Module Import Specs := (ADTListADTSpec Params).

  Hint Resolve map_inj : inj_db.
  Hint Resolve ListConstructor_inj : inj_db.
  Hint Resolve ElemConstructor_inj : inj_db.
  Hint Extern 1 => eapply RealElemToElem_inj : inj_db.

  Instance WrapADTList {index} : FacadeWrapper ADTValue (list (RealElemType index)).
  Proof.
    refine {| wrap ls := ListConstructor (map (RealElemToElem (index := index)) ls);
              wrap_inj := _ |}; eauto with inj_db.
  Defined.

  Instance WrapADTListElement {idx} : FacadeWrapper ADTValue (RealElemType idx).
  Proof.
    refine {| wrap x := ElemConstructor (RealElemToElem x);
              wrap_inj := _ |}; eauto with inj_db.
  Defined.

  Lemma CompileNew {idx} :
      forall vret fpointer (env: Env ADTValue) ext tenv,
        GLabelMap.find fpointer env = Some (Axiomatic New) ->
        vret ∉ ext ->
        Lifted_not_mapsto_adt ext tenv vret ->
        {{ tenv }}
          Call vret fpointer nil
        {{ [[ `vret ->> @nil (RealElemType idx) as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    change (ADT (ListConstructor [])) with (wrap (FacadeWrapper := WrapInstance (H := @WrapADTList idx)) []).
    facade_eauto.
  Qed.

  Ltac injections :=
    match goal with
    | [ H: ListConstructor _ = ListConstructor _ |- _ ] => apply ListConstructor_inj in H
    | [ H: ElemConstructor _ = ElemConstructor _ |- _ ] => apply ElemConstructor_inj in H
    end.

  Lemma CompilePop {idx} :
    forall vret vlst fpointer (env: Env ADTValue) ext tenv
      h (t: list (RealElemType idx)),
      GLabelMap.find fpointer env = Some (Axiomatic Pop) ->
      Lifted_MapsTo ext tenv vlst (wrap (h :: t)) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret <> vlst ->
      vlst ∉ ext ->
      vret ∉ ext ->
      {{ tenv }}
        Call vret fpointer (vlst :: nil)
      {{ [[ `vret ->> h as _ ]] :: [[ `vlst ->> t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || injections);
      facade_eauto.
  Qed.

  Lemma CompilePush {idx} :
    forall vret vhd vlst fpointer (env: Env ADTValue) ext tenv
      h (t: list (RealElemType idx)),
      GLabelMap.find fpointer env = Some (Axiomatic Push) ->
      Lifted_MapsTo ext tenv vhd (wrap h) ->
      Lifted_MapsTo ext tenv vlst (wrap t) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret <> vlst ->
      vret <> vhd ->
      vhd <> vlst ->
      vhd ∉ ext ->
      vlst ∉ ext ->
      vret ∉ ext ->
      {{ tenv }}
        Call vret fpointer (vlst :: vhd :: nil)
      {{ [[ `vret ->> Word.wzero 32 as _ ]]
          :: [[ `vlst ->> h :: t as _ ]]
          :: DropName vlst (DropName vret (DropName vhd tenv)) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || injections).
    facade_eauto.
    facade_eauto.
    facade_eauto.
    repeat apply DropName_remove; congruence.
  Qed.

  Lemma CompileEmpty {idx}:
    forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (fpointer : GLabelMap.key) (lst : list (RealElemType idx)),
      vlst <> vtest ->
      vtest ∉ ext ->
      Lifted_MapsTo ext tenv vlst (wrap lst) ->
      Lifted_not_mapsto_adt ext tenv vtest ->
      GLabelMap.MapsTo fpointer (Axiomatic Empty) env ->
      {{ tenv }}
        Call vtest fpointer (vlst :: nil)
      {{ [[`vtest ->> (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t || injections).

    facade_eauto.
    rewrite add_remove_comm by congruence.
    rewrite <- add_redundant_cancel by assumption.
    facade_eauto.
  Qed.

  Lemma CompileEmpty_spec {idx}:
    forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (fpointer : GLabelMap.key) (lst : list (RealElemType idx)),
      vlst <> vtest ->
      vtest ∉ ext ->
      NotInTelescope vtest tenv ->
      StringMap.MapsTo vlst (wrap lst) ext ->
      GLabelMap.MapsTo fpointer (Axiomatic Empty) env ->
      {{ tenv }}
        Call vtest fpointer (vlst :: nil)
      {{ [[`vtest ->> (bool2w (EqNat.beq_nat (Datatypes.length (rev lst)) 0)) as _]] :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    setoid_rewrite rev_length.
    apply generalized @CompileEmpty; repeat (compile_do_side_conditions || Lifted_t).
  Qed.

  Lemma CompileEmpty_alt {idx}:
    forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (fempty : GLabelMap.key) (lst : Comp (list (RealElemType idx))),
      vlst <> vtest ->
      vtest ∉ ext ->
      Lifted_not_mapsto_adt ext tenv vtest ->
      GLabelMap.MapsTo fempty (Axiomatic Empty) env ->
      {{ [[(NTSome vlst) ~~> lst as _]] :: tenv }}
        Call vtest fempty (vlst :: nil)
      {{ [[(NTSome vlst) ~~> lst as ls]]
          :: [[`vtest ->> (bool2w match ls with
                               | nil => true
                               | _ :: _ => false
                               end) as _]]
          :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || injections);
    facade_eauto.
  Qed.

  Lemma CompileDelete {idx}:
    forall (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (fpointer : GLabelMap.key),
      vlst <> vtmp ->
      vtmp ∉ ext ->
      vlst ∉ ext ->
      Lifted_MapsTo ext tenv vlst (wrap (@nil (RealElemType idx))) ->
      Lifted_not_mapsto_adt ext tenv vtmp ->
      GLabelMap.MapsTo fpointer (Axiomatic Delete) env ->
      {{ tenv }}
        Call vtmp fpointer (vlst :: nil)
      {{ [[`vtmp ->> (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vlst tenv)) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t || injections);
      facade_eauto.
  Qed.

  Lemma CompileDelete_spec {idx}:
    forall (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (fpointer : GLabelMap.key),
      vlst <> vtmp ->
      vtmp ∉ ext ->
      vlst ∉ ext ->
      NotInTelescope vtmp tenv ->
      NotInTelescope vlst tenv ->
      GLabelMap.MapsTo fpointer (Axiomatic Delete) env ->
      {{ [[ (NTSome vlst) ->> @nil (RealElemType idx) as _]] :: tenv }}
        (Call vtmp fpointer (vlst :: nil))
      {{ tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply ProgOk_Remove_Skip_R; hoare.
    apply generalized @CompileDelete; try (compile_do_side_conditions ||  Lifted_t).
    repeat match goal with
           | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
           | _ => setoid_rewrite Propagate_anonymous_ret
           end.
    apply CompileDeallocW_discretely; try compile_do_side_conditions.
    apply CompileSkip.
  Qed.

  Ltac loop_t :=
    repeat (intros || unfold Fold || solve [PreconditionSet_t; Lifted_t] || compile_do_side_conditions || clean_DropName_in_ProgOk || rewrite Propagate_ret || eapply CompileSeq || eauto 2).

  Lemma CompileLoopBase__many {idx} :
    forall {A}
      (lst: list (RealElemType idx)) init vhead vtest vlst
      fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv
      (f: A -> (RealElemType idx) -> A) tenvF,
      GLabelMap.MapsTo fpop (Axiomatic Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic Delete) env ->
      (* (forall tenv a1 a2 b, tenvF tenv (a1, b) = tenvF tenv (a2, b)) -> *)
      PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
      (forall v, NotInTelescope vtest (tenvF tenv v)) ->
      (forall v, NotInTelescope vhead (tenvF tenv v)) ->
      (forall v, NotInTelescope vlst (tenvF tenv v)) ->
      (forall v (h: (RealElemType idx)), TelEq ext ([[ ` vhead ->> h as _]]::tenvF tenv v) (tenvF ([[ ` vhead ->> h as _]]::tenv) v)) ->
      (forall head (acc: A) (s: list (RealElemType idx)),
          {{ tenvF ([[`vhead ->> head as _]] :: tenv) acc }}
            facadeBody
          {{ [[ ret (f acc head) as facc ]] :: tenvF tenv facc }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vlst ->> lst as _]] :: tenvF tenv init }}
        (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
      {{ tenvF tenv (fold_left f lst init) }} ∪ {{ ext }} // env.
  Proof.
    Transparent DummyArgument.
    unfold DummyArgument; loop_t.

    eapply (CompileEmpty_alt); loop_t.
    apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

    2:eapply (CompileDelete_spec); loop_t.

    loop_t.
    generalize dependent init;
      induction lst; loop_t.

    move_to_front vtest;
      apply CompileWhileFalse_Loop; loop_t.

    simpl.
    eapply CompileWhileTrue; [ loop_t.. | ].

    apply generalized @CompilePop; loop_t.
    rewrite <- GLabelMapFacts.find_mapsto_iff; try assumption.
    apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

    move_to_front vtest. (* apply ProgOk_Chomp_Some; loop_t. *)
    move_to_front vlst. (* apply ProgOk_Chomp_Some; loop_t. *)
    match goal with
    | [ H: forall _ _, TelEq _ _ _ |- _ ] => setoid_rewrite H
    end.
    apply ProgOk_Chomp_Some; loop_t.
    apply ProgOk_Chomp_Some; loop_t.
    computes_to_inv; subst; defunctionalize_evar; solve [eauto].

    move_to_front vtest.
    apply ProgOk_Remove_Skip_L; hoare.
    apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
    apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
    apply CompileSkip.

    apply CompileEmpty_alt; loop_t.
    apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

    loop_t.
    setoid_replace (DropName vtest ([[ ret (f init a) as facc ]] :: tenvF tenv facc))
    with (tenvF tenv (f init a)) using relation (TelEq ext); simpl; loop_t.
  Qed.

  Lemma CompileLoop__many {idx}:
    forall {A}
      vhead vtest vlst (tenvF: A -> Telescope ADTValue) tenv'
      (lst: list (RealElemType idx)) init (f: A -> (RealElemType idx) -> A) tenv0 tenv
      env (ext: StringMap.t (Value QsADTs.ADTValue))
      fpop fempty fdealloc facadeBody facadeConclude,
      GLabelMap.MapsTo fpop (Axiomatic Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic Delete) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
      TelEq ext tenv0 ([[`vlst ->> lst as _]] :: TelAppend (tenvF init) tenv) ->
      (forall v, NotInTelescope vtest (TelAppend (tenvF v) tenv)) ->
      (forall v, NotInTelescope vhead (TelAppend (tenvF v) tenv)) ->
      (forall v, NotInTelescope vlst (TelAppend (tenvF v) tenv)) ->
      {{ TelAppend (tenvF (fold_left f lst init)) tenv }}
        facadeConclude
      {{ TelAppend (tenvF (fold_left f lst init)) tenv' }}
      ∪ {{ ext }} // env ->
      (forall head (acc: A) (s: list (RealElemType idx)),
          {{ TelAppend (tenvF acc) ([[`vhead ->> head as _]] :: tenv) }}
            facadeBody
          {{ TelAppend ([[ ret (f acc head) as facc ]] :: tenvF facc) tenv }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ tenv0 }}
        (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody)
                  (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
             facadeConclude)
      {{ TelAppend ([[ ret (fold_left f lst init) as folded ]] :: tenvF folded) tenv' }} ∪ {{ ext }} // env.
  Proof.
    intros.
    rewrite H3.
    setoid_rewrite Propagate_anonymous_ret.
    hoare.
    pose (fun tenv init => TelAppend (tenvF init) tenv) as tenvF'.
    change (TelAppend (tenvF init) tenv) with (tenvF' tenv init).
    change (TelAppend (tenvF (fold_left f lst init)) tenv) with (tenvF' tenv (fold_left f lst init)).
    eapply @CompileLoopBase__many; eauto using TelEq_TelAppend_Cons_Second.
  Qed.
End ADTListCompilation.

Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Tuple.

Module WTupleListCompilation.
  Include (TupleListADTSpec WTupleListADTSpecParams).

  Module Import PR := (ADTListADTSpecParamsFromTupleOnes WTupleListADTSpecParams).

  Module WTupleListADTCompilationParams <: (ADTListCompilationParams PR).
    Definition TypeIndex := nat.
    Definition RealElemType N := FiatWTuple N.
    Definition RealElemToElem N := TupleToListW (N := N).
    Lemma RealElemToElem_inj : forall idx, Injective (@RealElemToElem idx).
    Proof.
      unfold RealElemToElem, Injective.
      eauto using TupleToListW_inj.
    Qed.
  End WTupleListADTCompilationParams.

  (* FIXME make injective a notation *)

  (* This makes no sense: we don't have a bedrock implementation of this! *)
  (* Module FiatWTupleListADTSpecParams <: ADTListADTSpecParams. *)
  (*   Definition N := 1. *)
  (*   Definition ElemType := FiatWTuple N. *)
  (*   Definition ElemConstructor x := WTuple (TupleToListW (N := N) x). *)
  (*   Lemma ElemConstructor_inj : (Injective ElemConstructor). *)
  (*   Admitted. *)
  (*   Definition ListConstructor ls := WTupleList (map (TupleToListW (N := N)) ls). *)
  (*   Lemma ListConstructor_inj : (Injective ListConstructor). *)
  (*   Admitted. *)
  (* End FiatWTupleListADTSpecParams. *)

  Include (ADTListCompilation PR WTupleListADTCompilationParams).

  (* Module Import PR := (ADTListADTSpecParamsFromTupleOnes WTupleListADTSpecParams). *)
  (* Include (ADTListCompilation PR). *)

  (* Instance QS_WrapWTupleList {N} : FacadeWrapper ADTValue (list (FiatWTuple N)). *)
  (* Proof. *)
  (*   refine {| wrap tl := wrap (List.map TupleToListW tl); *)
  (*             wrap_inj := _ |}; Wrapper_t. *)
  (* Defined. *)

  Require Import GLabelMapFacts.

  (* Lemma CompileLoopbase : *)
  (*   forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} (lst: list (FiatWTuple N)) init vhead vtest vlst vret fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv (f: Comp A -> FiatWTuple N -> Comp A), *)
  (*     GLabelMap.MapsTo fpop (Axiomatic Pop) env -> *)
  (*     GLabelMap.MapsTo fempty (Axiomatic Empty) env -> *)
  (*     GLabelMap.MapsTo fdealloc (Axiomatic Delete) env -> *)
  (*     PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] -> *)
  (*     BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) -> *)
  (*     (forall head (acc: Comp A) (s: list (FiatWTuple N)), *)
  (*         {{ [[`vret ~~> acc as _]] :: [[`vhead ->> head as _]] :: tenv }} *)
  (*           facadeBody *)
  (*         {{ [[`vret ~~> (f acc head) as _]] :: tenv }} ∪ *)
  (*         {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) -> *)
  (*     {{ [[`vret ~~> init as _]] :: [[`vlst ->> lst as _]] :: tenv }} *)
  (*       (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) *)
  (*     {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env. *)
  (* Proof. *)
  (*   unfold DummyArgument; loop_t. *)

  (*   rewrite TelEq_swap by loop_t. *)
  (*   unfold  *)
  (*     eapply (CompileEmpty_alt); loop_t. *)

  (*   2:eapply (CompileDelete_spec (N := N)); loop_t. *)

  (*   loop_t. *)
  (*   generalize dependent init; *)
  (*   induction lst; loop_t. *)

  (*   move_to_front vtest; *)
  (*     apply CompileWhileFalse_Loop; loop_t. *)
  (*   simpl. *)

  (*   eapply CompileWhileTrue; [ loop_t.. | ]. *)

  (*   apply generalized @CompilePop; loop_t. *)
  (*   rewrite <- GLabelMapFacts.find_mapsto_iff; assumption. *)
    
  (*   move_to_front vlst; apply ProgOk_Chomp_Some; loop_t. *)
  (*   move_to_front vtest; apply ProgOk_Chomp_Some; loop_t. *)
  (*   move_to_front vret; loop_t. *)
  (*   computes_to_inv; subst; defunctionalize_evar; eauto. *)

  (*   rewrite TelEq_swap. *)
  (*   apply ProgOk_Remove_Skip_L; hoare. *)
  (*   apply CompileDeallocW_discretely; try compile_do_side_conditions. *)
  (*   apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros. *)
  (*   apply CompileSkip. *)
  (*   apply CompileEmpty_alt; loop_t. *)

  (*   loop_t. *)
  (* Qed. *)

  Lemma CompileLoop {N} :
    forall {A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
      lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody facadeConclude
      env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: Comp A -> FiatWTuple N -> Comp A),
      GLabelMap.MapsTo fpop (Axiomatic (Pop)) env ->
      GLabelMap.MapsTo fempty (Axiomatic (Empty)) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic (Delete)) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
      {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv }}
        facadeConclude
      {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      (* BinNat.N.lt (BinNat.N.of_nat 1) (Word.Npow2 32) -> *)
      (forall head (acc: Comp A) (s: list (FiatWTuple N)),
          {{ [[`vret ~~> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
            facadeBody
          {{ [[`vret ~~> (f acc head) as _]] :: tenv }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vret ~~> init as _]] :: [[`vlst ->> lst as _]] :: tenv }}
        (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody)
                  (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
      {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
  Proof.
    hoare. hoare.
    rewrite TelEq_swap.
    set (tenvF := fun tenv init => [[ `vret ~~> init as _ ]] :: tenv).
    change ([[ `vlst ->> lst as _ ]] :: [[ `vret ~~> init as _ ]] :: tenv) with ([[ `vlst ->> lst as _ ]] :: tenvF tenv init).
    change ([[ `vret ~~> fold_left f lst init as _ ]] :: tenv) with (tenvF tenv (fold_left f lst init)).

    eapply CompileLoopBase__many; unfold tenvF in *; loop_t.
    setoid_rewrite Propagate_anonymous_ret; apply H5.
  Qed.

  Lemma CompileLoopalloc :
    forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
      env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: Comp A -> (FiatWTuple N) -> Comp A),
      GLabelMap.MapsTo fpop (Axiomatic (Pop)) env ->
      GLabelMap.MapsTo fempty (Axiomatic (Empty)) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic (Delete)) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      {{ [[`vlst ->> lst as _]] :: tenv }}
        facadeInit
      {{ [[`vret ~~> init as _]] :: [[`vlst ->> lst as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv }}
        facadeConclude
      {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      (forall head (acc: Comp A) (s: list (FiatWTuple N)),
          {{ [[`vret ~~> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
            facadeBody
          {{ [[`vret ~~> (f acc head) as _]] :: tenv }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vlst ->> lst as _]] :: tenv }}
        (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
      {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
  Proof.
    hoare. hoare.
    apply @CompileLoop; try eassumption.
  Qed.

  Require Import Fiat.CertifiedExtraction.Extraction.QueryStructures.CallRules.WordList.

  Lemma CompileMap_TuplesToWords :
    forall {N} (lst: list (FiatWTuple N)) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: FiatWTuple N -> W),
      GLabelMap.MapsTo fpop (Axiomatic (Pop)) env ->
      GLabelMap.MapsTo fempty (Axiomatic (Empty)) env ->
      GLabelMap.MapsTo falloc (Axiomatic (QsADTs.WordListADTSpec.New)) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic (Delete)) env ->
      GLabelMap.MapsTo fcons (Axiomatic (QsADTs.WordListADTSpec.Push)) env ->
      PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret ->> (revmap f lst) as _]] :: tenv }}
        facadeCoda
      {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret ->> (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      (forall head (s: list (FiatWTuple N)) (s': list W),
          {{ [[`vhead ->> head as _]] :: tenv }}
            facadeBody
          {{ [[`vhead' ->> f head as _]] :: tenv }}
          ∪ {{ [vret |> wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) s']
                 :: [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vlst ->> lst as _]] :: tenv }}
        (Seq
           (Call vret falloc nil)
           (Seq
              (Seq
                 (Fold vhead vtest vlst fpop fempty
                       (Seq facadeBody
                            (Call vtmp fcons (vret :: vhead' :: nil))))
                 (Call vtest fdealloc (vlst :: nil)))
              facadeCoda))
      {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret ->> (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
  Proof.
    intros.
    setoid_rewrite <- revmap_fold_comp.
    apply CompileLoopalloc; eauto.
    PreconditionSet_t; eauto.

    eapply CompileWordList_new; compile_do_side_conditions.
    setoid_rewrite revmap_fold_comp; eassumption.
    intros.
    rewrite SameValues_Fiat_Bind_TelEq.
    move_to_front vret.
    apply miniChomp'; intros.
    hoare.
    apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.

    apply CompileWordList_push_spec; try compile_do_side_conditions.
  Qed.

  Lemma CompileLoop_ret :
    forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
      lst init facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatWTuple N) -> A),
      GLabelMap.MapsTo fpop (Axiomatic Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic Delete) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      (forall head acc (s: list (FiatWTuple N)),
          {{ [[`vret ->> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
            facadeBody
          {{ [[`vret ->> (f acc head) as _]] :: tenv }} ∪ {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv }}
        facadeConclude
      {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[`vret ->> init as _]] :: [[(NTSome  vlst) ->> lst as _]] :: tenv }}
        (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
      {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
  Proof.
    intros.
    setoid_replace ([[ `vret ->> fold_left f lst init as _ ]] :: tenv')
    with (TelAppend ([[ ret (fold_left f lst init) as r ]] :: [[ `vret ->> r as _ ]] :: Nil) tenv')
           using relation (TelEq ext) by (rewrite Propagate_anonymous_ret; reflexivity).

    eapply CompileLoop__many; unfold TelAppend; PreconditionSet_t; loop_t.
    rewrite Propagate_anonymous_ret. eauto.
  Qed.

  Lemma CompileLoopalloc_ret :
    forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
      lst init facadeInit facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatWTuple N) -> A),
      GLabelMap.MapsTo fpop (Axiomatic (Pop)) env ->
      GLabelMap.MapsTo fempty (Axiomatic (Empty)) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic (Delete)) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      {{ [[`vlst ->> lst as _]] :: tenv }}
        facadeInit
      {{ [[`vret ->> init as _]] :: [[`vlst ->> lst as _]] :: tenv }} ∪ {{ ext }} // env ->
      (forall head acc (s: list (FiatWTuple N)),
          {{ [[`vret ->> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
            facadeBody
          {{ [[`vret ->> (f acc head) as _]] :: tenv }} ∪ {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv }}
        facadeConclude
      {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[`vlst ->> lst as _]] :: tenv }}
        (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
      {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
  Proof.
    eauto using @CompileSeq, @CompileLoop_ret.
  Qed.

  Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Tuple.

  Lemma CompileDeleteAny_spec:
    forall {N} (vtmp vtmp2 vsize vtest vlst vhead : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
      (fpop fempty fdealloc ftdealloc : GLabelMap.key) (seq: (list (FiatWTuple N))),
      PreconditionSet tenv ext [[[vtmp; vtmp2; vsize; vhead; vtest; vlst]]] ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      GLabelMap.MapsTo fpop (Axiomatic (Pop)) env ->
      GLabelMap.MapsTo fempty (Axiomatic (Empty)) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic (Delete)) env ->
      GLabelMap.MapsTo ftdealloc (Axiomatic (WTupleADTSpec.Delete)) env ->
      {{ [[ `vlst ->> seq as _]] :: tenv }}
        (Seq (Assign vtmp (Const (Word.natToWord 32 0)))
             (Seq (Seq (Fold vhead vtest vlst fpop fempty (Seq (Assign vsize (Const (Word.natToWord 32 N)))
                                                               (Call vtmp2 ftdealloc [[[vhead; vsize]]])))
                       (Call (DummyArgument vtest) fdealloc [[[vlst]]]))
                  Skip))
      {{ tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply ProgOk_Remove_Skip_R.
    apply CompileSeq with ([[ ` vtmp ->> fold_left (fun acc x => acc) seq (Word.natToWord 32 0) as _]]::tenv).
    eapply (CompileLoopalloc_ret (vhead := vhead) (vtest := vtest)); try compile_do_side_conditions.
    apply CompileConstant; try compile_do_side_conditions.
    intros. apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
    apply (WTupleCompilation.CompileDelete_spec (vtmp := vtmp2) (vsize := vsize)); try compile_do_side_conditions.
    apply CompileSkip.
    apply CompileDeallocW_discretely; try compile_do_side_conditions.
    apply CompileSkip.
  Defined.
End WTupleListCompilation.
