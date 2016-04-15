Require Export Fiat.Computation.Notations. (* FIXME remove *)
Require Import Refactor.CallRules.Core.
Require Import CertifiedExtraction.Extraction.External.Loops.
Require Import CertifiedExtraction.Extraction.External.FacadeLoops.

Lemma CompileTupleList_new :
    forall vret fpointer (env: Env ADTValue) ext tenv N,
      GLabelMap.find fpointer env = Some (Axiomatic TupleList_new) ->
      vret ∉ ext ->
      Lifted_not_mapsto_adt ext tenv vret ->
      {{ tenv }}
        Call vret fpointer nil
      {{ [[ `vret <-- @nil (FiatTuple N) as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  change (ADT (TupleList [])) with (wrap (FacadeWrapper := WrapInstance (H := @QS_WrapTupleList N)) []).
  facade_eauto.
Qed.

Lemma CompileTupleList_delete :
  forall vret vlst fpointer (env: Env ADTValue) ext tenv N,
    GLabelMap.find fpointer env = Some (Axiomatic TupleList_delete) ->
    Lifted_MapsTo ext tenv vlst (wrap (@nil (FiatTuple N))) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    vret <> vlst ->
    vlst ∉ ext ->
    vret ∉ ext ->
    {{ tenv }}
      Call vret fpointer (vlst :: nil)
    {{ [[ `vret <-- SCAZero as _ ]] :: DropName vret (DropName vlst tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileTupleList_pop :
  forall vret vlst fpointer (env: Env ADTValue) ext tenv N
    h (t: list (FiatTuple N)),
    GLabelMap.find fpointer env = Some (Axiomatic TupleList_pop) ->
    Lifted_MapsTo ext tenv vlst (wrap (h :: t)) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    vret <> vlst ->
    vlst ∉ ext ->
    vret ∉ ext ->
    {{ tenv }}
      Call vret fpointer (vlst :: nil)
      {{ [[ `vret <-- h as _ ]] :: [[ `vlst <-- t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileTupleList_push :
  forall vret vhd vlst fpointer (env: Env ADTValue) ext tenv N
    h (t: list (FiatTuple N)),
    GLabelMap.find fpointer env = Some (Axiomatic TupleList_push) ->
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
      {{ [[ `vret <-- SCAZero as _ ]] :: [[ `vlst <-- h :: t as _ ]] :: DropName vlst (DropName vret (DropName vhd tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; congruence.
Qed.

Lemma CompileTupleList_Empty_helper:
  forall (N : nat) (lst : list (FiatTuple N)) (x1 : W),
    Programming.propToWord (map TupleToListW lst = nil) x1 ->
    ret (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) ↝ x1.
Proof.
  unfold Programming.propToWord, IF_then_else in *.
  destruct lst; simpl in *; destruct 1; repeat cleanup; try discriminate; fiat_t.
Qed.

Hint Resolve CompileTupleList_Empty_helper : call_helpers_db.

Lemma ListEmpty_helper :
  forall {A} (seq: list A),
    (EqNat.beq_nat (Datatypes.length seq) 0) = match seq with
                                               | nil => true
                                               | _ :: _ => false
                                               end.
Proof.
  destruct seq; reflexivity.
Qed.

Lemma CompileTupleListEmpty_alt_helper :
  forall {N} x w,
    Programming.propToWord (map (TupleToListW (N := N)) x = nil) w ->
    ret (bool2w match x with
                | nil => true
                | _ :: _ => false
                end) ↝ w.
Proof.
  intros * h.
  apply CompileTupleList_Empty_helper in h.
  rewrite <- ListEmpty_helper.
  assumption.
Qed.

Hint Resolve CompileTupleListEmpty_alt_helper : call_helpers_db.

Lemma CompileTupleList_Empty:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (lst : list _),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) lst) ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_empty) env ->
    {{ tenv }}
      Call vtest fpointer (vlst :: nil)
    {{ [[`vtest <-- (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  rewrite add_remove_comm by congruence.
  rewrite <- add_redundant_cancel by assumption.
  facade_eauto.
Qed.

Lemma CompileTupleList_Empty_spec:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (lst : list _),
    vlst <> vtest ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    StringMap.MapsTo vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) lst) ext ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_empty) env ->
    {{ tenv }}
      Call vtest fpointer (vlst :: nil)
    {{ [[`vtest <-- (bool2w (EqNat.beq_nat (Datatypes.length (rev lst)) 0)) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite rev_length.
  apply generalized CompileTupleList_Empty; repeat (compile_do_side_conditions || Lifted_t).
Qed.


Lemma CompileTupleList_Empty_alt:
  forall {N} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
    (fempty : GLabelMap.key) (lst : Comp (list (FiatTuple N))),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env ->
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <~~ lst as _]] :: tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <~~ lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                | nil => true
                                                | _ :: _ => false
                                                end) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileTupleList_Delete:
  forall (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) nil) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vlst :: nil)
    {{ [[`vtmp <-- (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vlst tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileTupleList_Delete_spec:
  forall {N} (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    NotInTelescope vtmp tenv ->
    NotInTelescope vlst tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_delete) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTupleList (N := N)))) vlst) <-- nil as _]] :: tenv }}
      (Call vtmp fpointer (vlst :: nil))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  apply generalized CompileTupleList_Delete; try (compile_do_side_conditions ||  Lifted_t).
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.

Require Import GLabelMapFacts.

Lemma CompileTupleList_LoopBase :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} (lst: list (FiatTuple N)) init vhead vtest vlst vret fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv (f: Comp A -> FiatTuple N -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  unfold DummyArgument; loop_t.

  rewrite TelEq_swap by loop_t;
    eapply (CompileTupleList_Empty_alt (N := N)); loop_t.

  2:eapply (CompileTupleList_Delete_spec (N := N)); loop_t.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.
  simpl.

  eapply CompileWhileTrue; [ loop_t.. | ].

  apply generalized @CompileTupleList_pop; loop_t.
  rewrite <- GLabelMapFacts.find_mapsto_iff; assumption.

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vret; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

  rewrite TelEq_swap.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.
  apply CompileTupleList_Empty_alt; loop_t.

  loop_t.
Qed.

Lemma CompileTupleList_Loop :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody facadeConclude
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: Comp A -> FiatTuple N -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  apply @CompileTupleList_LoopBase; eassumption.
Qed.

Lemma CompileTupleList_LoopAlloc :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: Comp A -> (FiatTuple N) -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  apply @CompileTupleList_Loop; try eassumption.
Qed.

Require Import Fiat.CertifiedExtraction.Extraction.Refactor.CallRules.WordList.

Lemma CompileMap_TuplesToWords :
  forall {N} (lst: list (FiatTuple N)) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: FiatTuple N -> W),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (QsADTs.WordList_new)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    GLabelMap.MapsTo fcons (Axiomatic (QsADTs.WordList_push)) env ->
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list (FiatTuple N)) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }}
        ∪ {{ [vret <-- wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) s']
               :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileTupleList_LoopAlloc; eauto.
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

Lemma CompileTupleList_Loop_ret :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
    lst init facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatTuple N) -> A),
    GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head acc (s: list (FiatTuple N)),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vret <-- init as _]] :: [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite ret_fold_fold_ret.
  eapply CompileSeq.
  apply CompileTupleList_LoopBase; try compile_do_side_conditions.
  2: apply ProkOk_specialize_to_ret; intros * h; apply ret_fold_fold_ret in h; computes_to_inv; subst; eauto.
  intros; rewrite SameValues_Fiat_Bind_TelEq.
  apply miniChomp'; intros; eauto.
Qed.

Lemma CompileTupleList_LoopAlloc_ret :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
    lst init facadeInit facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatTuple N) -> A),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <-- init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc (s: list (FiatTuple N)),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileTupleList_Loop_ret.
Qed.

Require Import CallRules.Tuple.

Lemma CompileTupleList_DeleteAny_spec:
  forall {N} (vtmp vtmp2 vsize vtest vlst vhead : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
    (fpop fempty fdealloc ftdealloc : GLabelMap.key) (seq: (list (FiatTuple N))),
    PreconditionSet tenv ext [[[vtmp; vtmp2; vsize; vhead; vtest; vlst]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    GLabelMap.MapsTo ftdealloc (Axiomatic (QsADTs.Tuple_delete)) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTupleList (N := N)))) vlst) <-- seq as _]] :: tenv }}
      (Seq (Assign vtmp (Const (Word.natToWord 32 0)))
           (Seq (Seq (Fold vhead vtest vlst fpop fempty (Seq (Assign vsize (Const (Word.natToWord 32 N)))
                                                             (Call vtmp2 ftdealloc [[[vhead; vsize]]])))
                     (Call (DummyArgument vtest) fdealloc [[[vlst]]]))
                Skip))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R.
  apply CompileSeq with ([[ ` vtmp <-- fold_left (fun acc x => acc) seq (Word.natToWord 32 0) as _]]::tenv).
  eapply (CompileTupleList_LoopAlloc_ret (vhead := vhead) (vtest := vtest)); try compile_do_side_conditions.
  apply CompileConstant; try compile_do_side_conditions.
  intros. apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply (CompileTuple_Delete_spec (vtmp := vtmp2) (vsize := vsize)); try compile_do_side_conditions.
  apply CompileSkip.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Defined.

