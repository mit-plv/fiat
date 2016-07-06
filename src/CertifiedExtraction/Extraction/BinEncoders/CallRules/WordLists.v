Require Export
        Fiat.CertifiedExtraction.Extraction.Extraction.

Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.

Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

Require Import Bedrock.Platform.Facade.examples.QsADTs.

Lemma CompileCallListSCALength {A}:
  forall {WrpList: FacadeWrapper (Value ADTValue) (BoundedList A (pow2 8))}
    (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : BoundedList A (pow2 8))
    fLength tenv',
    PreconditionSet tenv' ext [[[vlst;varg]]] ->
    (exists sk: _ -> list W,
        (forall ls: BoundedList A (pow2 8),
            wrap ls = ADT (WordList (sk ls))) /\
        (forall ls: BoundedList A (pow2 8),
            List.length (sk ls) = List.length (`ls))) ->
    GLabelMap.MapsTo fLength (Axiomatic WordListADTSpec.Length) env ->
    TelEq ext tenv ([[`vlst ->> lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg fLength [vlst]
    {{ [[ ` varg ->> BoundedListLength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? (? & wrap_eq & length_eq) ? Heq; setoid_rewrite Heq; PreconditionSet_t;
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || rewrite wrap_eq in *).
  facade_eauto.
  facade_eauto.
  repeat match goal with
         | [ H: ?a = ?a |- _ ] => clear dependent H
         | [ H: ADT (WordList (_ _)) = ADT _ |- _ ] => inversion' H
         end; rewrite length_eq; reflexivity.
  facade_eauto.
  rewrite remove_remove_comm by assumption; facade_eauto.
Qed.

Lemma CompileCallListBoundedNatLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : BoundedList (BoundedNat 8) (pow2 8))
    fLength tenv',
    PreconditionSet tenv' ext [[[vlst;varg]]] ->
    GLabelMap.MapsTo fLength (Axiomatic WordListADTSpec.Length) env ->
    TelEq ext tenv ([[`vlst ->> lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg fLength [vlst]
    {{ [[ ` varg ->> BoundedListLength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileCallListSCALength; eauto.
  eexists; split.
  - reflexivity.
  - setoid_rewrite map_length; reflexivity.
Qed.

Lemma CompileWordListEmpty_alt:
  forall {A} {Wrp: FacadeWrapper W A}
    (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
    (tenv: Telescope QsADTs.ADTValue) ext
    (fempty : GLabelMap.key) (lst : Comp (list A)),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic WordListADTSpec.Empty) env ->
    {{ [[(NTSome (H := WrapSCAList) vlst) ~~> lst as _]] :: tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[(NTSome (H := WrapSCAList) vlst) ~~> lst as ls]]
        :: [[`vtest ->> (bool2w match ls with
                             | nil => true
                             | _ :: _ => false
                             end) as _]]
        :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
    facade_eauto.
Qed.

Lemma CompileWordListDelete:
  forall {A} {Wrp: FacadeWrapper W A}
    (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
    (tenv: Telescope QsADTs.ADTValue) ext
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (@nil A)) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    GLabelMap.MapsTo fpointer (Axiomatic WordListADTSpec.Delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vlst :: nil)
    {{ [[`vtmp ->> (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vlst tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t);
    facade_eauto.
Qed.

Lemma CompileWordListDelete_spec:
  forall {A} {Wrp: FacadeWrapper W A},
    let Wrapper := WrapSCAList : FacadeWrapper (Value ADTValue) (list A) in
    forall (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
      (tenv: Telescope QsADTs.ADTValue) ext
      (fpointer : GLabelMap.key),
      vlst <> vtmp ->
      vtmp ∉ ext ->
      vlst ∉ ext ->
      NotInTelescope vtmp tenv ->
      NotInTelescope vlst tenv ->
      GLabelMap.MapsTo fpointer (Axiomatic WordListADTSpec.Delete) env ->
      {{ [[ (NTSome vlst) ->> @nil A as _]] :: tenv }}
        (Call vtmp fpointer (vlst :: nil))
      {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  apply generalized @CompileWordListDelete; try (compile_do_side_conditions || Lifted_t).
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocW_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.

Lemma CompileWordListPop :
  forall {A} {Wrp: FacadeWrapper W A},
    let Wrapper := WrapSCAList : FacadeWrapper (Value ADTValue) (list A) in
    forall vret vlst fpointer (env: Env ADTValue) ext tenv
      h (t: list A),
      GLabelMap.find fpointer env = Some (Axiomatic WordListADTSpec.Pop) ->
      Lifted_MapsTo ext tenv vlst (wrap (h :: t)) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret <> vlst ->
      vlst ∉ ext ->
      vret ∉ ext ->
      {{ tenv }}
        Call vret fpointer (vlst :: nil)
      {{ [[ `vret ->> h as _ ]] :: [[ `vlst ->> t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
    facade_eauto.
Qed.

Lemma firstn_length {A} :
  forall (l l': list A), l = (firstn (length l) (l ++ l')).
Proof.
  induction l.
  - reflexivity.
  - simpl; intros; rewrite <- IHl; reflexivity.
Qed.

Lemma app_cons_app_app_cons {A} :
  forall (a c: list A) b, (a ++ b :: nil) ++ c = a ++ b :: c.
Proof.
  intros; rewrite <- app_assoc; reflexivity.
Qed.

Lemma skip_S_length {A} :
  forall (l l': list A) a, l' = (skipn (S (length l)) (l ++ a :: l')).
Proof.
  intros; rewrite <- app_cons_app_app_cons, ListFacts.rw_skipn_app.
  - reflexivity.
  - rewrite app_length; simpl; try omega.
Qed.

Lemma CompileLoopBase__many :
  forall {A B} {Wrp: FacadeWrapper W B},
    let Wrapper := WrapSCAList : FacadeWrapper (Value ADTValue) (list B) in
    forall (lst: list B) init vhead vtest vlst
      fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv
      (f: A -> B -> A) tenvF,
      GLabelMap.MapsTo fpop (Axiomatic QsADTs.WordListADTSpec.Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic QsADTs.WordListADTSpec.Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.WordListADTSpec.Delete) env ->
      (* (forall tenv a1 a2 b, tenvF tenv (a1, b) = tenvF tenv (a2, b)) -> *)
      PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
      (forall v, NotInTelescope vtest (tenvF tenv v)) ->
      (forall v, NotInTelescope vhead (tenvF tenv v)) ->
      (forall v, NotInTelescope vlst (tenvF tenv v)) ->
      (forall v (h: B), TelEq ext ([[ ` vhead ->> h as _]]::tenvF tenv v) (tenvF ([[ ` vhead ->> h as _]]::tenv) v)) ->
      (forall head n,
          Some head = List.nth_error lst n ->
          n < length lst ->
          let acc := (fold_left f (List.firstn n lst) init) in
          let s := (List.skipn (S n) lst) in
          {{ tenvF ([[`vhead ->> head as _]] :: tenv) acc }}
            facadeBody
          {{ [[ ret (f acc head) as facc ]] :: tenvF tenv facc }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vlst ->> lst as _]] :: tenvF tenv init }}
        (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
      {{ tenvF tenv (fold_left f lst init) }} ∪ {{ ext }} // env.
Proof.
  intros.
  Transparent DummyArgument.
  unfold DummyArgument; loop_t.

  (* Start by calling empty *)
  eapply (CompileWordListEmpty_alt); loop_t.
  apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

  (* End by calling Delete *)
  2:eapply (CompileWordListDelete_spec); loop_t.

  (* The loop itself *)
  loop_t.

  change init with (fold_left f nil init).

  rewrite <- (app_nil_l lst) in H7.
  set (nil ++ lst) in H7.
  set nil in l.
  change (@nil B) with l0 at -2.
  clearbody l0.
  unfold l in *; clear l.
  generalize dependent l0.

  induction lst; intros.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.

  (* * :: list *)
  simpl.
  eapply CompileWhileTrue; [ loop_t.. | ].

  (* * * Pop *)
  apply generalized @CompileWordListPop; loop_t.
  rewrite <- GLabelMapFacts.find_mapsto_iff; try assumption.
  apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

  Opaque skipn.
  (* * * Body of folding function *)
  move_to_front vtest. (* apply ProgOk_Chomp_Some; loop_t. *)
  move_to_front vlst. (* apply ProgOk_Chomp_Some; loop_t. *)
  match goal with
  | [ H: forall _ _, TelEq _ _ _ |- _ ] => setoid_rewrite H
  end.
  apply ProgOk_Chomp_Some; loop_t.
  apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar.
  specialize (H7 a (length l0)).
  change (length l0) with (0 + length l0) in H7.
  rewrite Expr.nth_error_length in H7.
  specialize (H7 eq_refl).
  rewrite app_length in H7.
  simpl in H7.
  assert (length l0 < length l0 + S (length v)) as lt by omega.
  specialize (H7 lt).

  replace (firstn (length l0) (l0 ++ a :: v)) with l0 in * by apply firstn_length.
  replace (skipn (S (length l0)) (l0 ++ a :: v)) with (v) in * by apply skip_S_length.
  simpl.
  apply H7.

  (* * * Check for emptyness *)
  move_to_front vtest.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.

  apply CompileWordListEmpty_alt; loop_t.
  apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

  (* * * Conclusion *)
  loop_t.
  
  setoid_replace (DropName vtest ([[ ret (f (fold_left f l0 init) a) as facc ]] :: tenvF tenv facc))
  with (tenvF tenv (f (fold_left f l0 init) a)) using relation (TelEq ext); simpl; loop_t.

  specialize (IHlst (l0 ++ a :: nil)).
  rewrite fold_left_app in IHlst.
  apply IHlst.
  intros.
  replace ((l0 ++ a :: nil) ++ lst) with (l0 ++ a :: lst) in * by (symmetry; apply app_cons_app_app_cons).
  apply H7.
  assumption.
  assumption.
Qed.

Lemma CompileLoop__many :
  forall {A B} {Wrp: FacadeWrapper W B},
    let Wrapper := WrapSCAList : FacadeWrapper (Value ADTValue) (list B) in
    forall vhead vtest vlst (tenvF: A -> Telescope ADTValue) tenv'
      (lst: list B) init (f: A -> B -> A) tenv0 tenv
      env (ext: StringMap.t (Value QsADTs.ADTValue))
      fpop fempty fdealloc facadeBody facadeConclude,
      GLabelMap.MapsTo fpop (Axiomatic QsADTs.WordListADTSpec.Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic QsADTs.WordListADTSpec.Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.WordListADTSpec.Delete) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
      TelEq ext tenv0 ([[`vlst ->> lst as _]] :: TelAppend (tenvF init) tenv) ->
      (forall v, NotInTelescope vtest (TelAppend (tenvF v) tenv)) ->
      (forall v, NotInTelescope vhead (TelAppend (tenvF v) tenv)) ->
      (forall v, NotInTelescope vlst (TelAppend (tenvF v) tenv)) ->
      {{ TelAppend (tenvF (fold_left f lst init)) tenv }}
        facadeConclude
      {{ TelAppend (tenvF (fold_left f lst init)) tenv' }}
      ∪ {{ ext }} // env ->
      (forall head n,
          Some head = List.nth_error lst n ->
          n < length lst ->
          let acc := (fold_left f (List.firstn n lst) init) in
          let s := (List.skipn (S n) lst) in
          {{ TelAppend (tenvF acc) ([[`vhead ->> head as _]] :: tenv) }}
            facadeBody
          {{ TelAppend ([[ ret (f acc head) as facc ]] :: tenvF facc) tenv }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ tenv0 }}
        (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
      {{ TelAppend ([[ ret (fold_left f lst init) as folded ]] :: tenvF folded) tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  match goal with
  | [ H: TelEq _ _ _ |- _ ] => rewrite H
  end; setoid_rewrite Propagate_anonymous_ret.
  hoare.
  pose (fun tenv init => TelAppend (tenvF init) tenv) as tenvF'.
  change (TelAppend (tenvF init) tenv) with (tenvF' tenv init).
  change (TelAppend (tenvF (fold_left f lst init)) tenv) with (tenvF' tenv (fold_left f lst init)).
  eapply @CompileLoopBase__many; eauto using TelEq_TelAppend_Cons_Second.
Qed.

Lemma OriginalCompileLoopBase__many :
  forall {A B} {Wrp: FacadeWrapper W B},
    let Wrapper := WrapSCAList : FacadeWrapper (Value ADTValue) (list B) in
    forall (lst: list B) init vhead vtest vlst
      fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv
      (f: A -> B -> A) tenvF,
      GLabelMap.MapsTo fpop (Axiomatic QsADTs.WordListADTSpec.Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic QsADTs.WordListADTSpec.Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.WordListADTSpec.Delete) env ->
      (* (forall tenv a1 a2 b, tenvF tenv (a1, b) = tenvF tenv (a2, b)) -> *)
      PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
      (forall v, NotInTelescope vtest (tenvF tenv v)) ->
      (forall v, NotInTelescope vhead (tenvF tenv v)) ->
      (forall v, NotInTelescope vlst (tenvF tenv v)) ->
      (forall v (h: B), TelEq ext ([[ ` vhead ->> h as _]]::tenvF tenv v) (tenvF ([[ ` vhead ->> h as _]]::tenv) v)) ->
      (forall head (acc: A) (s: list B),
          {{ tenvF ([[`vhead ->> head as _]] :: tenv) acc }}
            facadeBody
            {{ [[ ret (f acc head) as facc ]] :: tenvF tenv facc }} ∪
            {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ [[`vlst ->> lst as _]] :: tenvF tenv init }}
        (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
      {{ tenvF tenv (fold_left f lst init) }} ∪ {{ ext }} // env.
Proof.
  intros.
  Transparent DummyArgument.
  unfold DummyArgument; loop_t.

  (* Start by calling empty *)
  eapply (CompileWordListEmpty_alt); loop_t.
  apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

  (* End by calling Delete *)
  2:eapply (CompileWordListDelete_spec); loop_t.

  (* The loop itself *)
  loop_t.

  generalize dependent init;
    induction lst; loop_t.

  (* * [] list *)
  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.

  (* * :: list *)
  simpl.
  eapply CompileWhileTrue; [ loop_t.. | ].

  (* * * Pop *)
  apply generalized @CompileWordListPop; loop_t.
  rewrite <- GLabelMapFacts.find_mapsto_iff; try assumption.
  apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

  (* * * Body of folding function *)
  move_to_front vtest. (* apply ProgOk_Chomp_Some; loop_t. *)
  move_to_front vlst. (* apply ProgOk_Chomp_Some; loop_t. *)
  match goal with
  | [ H: forall _ _, TelEq _ _ _ |- _ ] => setoid_rewrite H
  end.
  apply ProgOk_Chomp_Some; loop_t.
  apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; solve [eauto].

  (* * * Check for emptyness *)
  move_to_front vtest.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.

  apply CompileWordListEmpty_alt; loop_t.
  apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; loop_t.

  (* * * Conclusion *)
  loop_t.
  setoid_replace (DropName vtest ([[ ret (f init a) as facc ]] :: tenvF tenv facc))
  with (tenvF tenv (f init a)) using relation (TelEq ext); simpl; loop_t.
Qed.

Lemma OriginalCompileLoop__many :
  forall {A B} {Wrp: FacadeWrapper W B},
    let Wrapper := WrapSCAList : FacadeWrapper (Value ADTValue) (list B) in
    forall vhead vtest vlst (tenvF: A -> Telescope ADTValue) tenv'
      (lst: list B) init (f: A -> B -> A) tenv0 tenv
      env (ext: StringMap.t (Value QsADTs.ADTValue))
      fpop fempty fdealloc facadeBody facadeConclude,
      GLabelMap.MapsTo fpop (Axiomatic QsADTs.WordListADTSpec.Pop) env ->
      GLabelMap.MapsTo fempty (Axiomatic QsADTs.WordListADTSpec.Empty) env ->
      GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.WordListADTSpec.Delete) env ->
      PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
      TelEq ext tenv0 ([[`vlst ->> lst as _]] :: TelAppend (tenvF init) tenv) ->
      (forall v, NotInTelescope vtest (TelAppend (tenvF v) tenv)) ->
      (forall v, NotInTelescope vhead (TelAppend (tenvF v) tenv)) ->
      (forall v, NotInTelescope vlst (TelAppend (tenvF v) tenv)) ->
      {{ TelAppend (tenvF (fold_left f lst init)) tenv }}
        facadeConclude
      {{ TelAppend (tenvF (fold_left f lst init)) tenv' }}
      ∪ {{ ext }} // env ->
      (forall head (acc: A) (s: list B),
          {{ TelAppend (tenvF acc) ([[`vhead ->> head as _]] :: tenv) }}
            facadeBody
          {{ TelAppend ([[ ret (f acc head) as facc ]] :: tenvF facc) tenv }} ∪
          {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
      {{ tenv0 }}
        (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
      {{ TelAppend ([[ ret (fold_left f lst init) as folded ]] :: tenvF folded) tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  match goal with
  | [ H: TelEq _ _ _ |- _ ] => rewrite H
  end; setoid_rewrite Propagate_anonymous_ret.
  hoare.
  pose (fun tenv init => TelAppend (tenvF init) tenv) as tenvF'.
  change (TelAppend (tenvF init) tenv) with (tenvF' tenv init).
  change (TelAppend (tenvF (fold_left f lst init)) tenv) with (tenvF' tenv (fold_left f lst init)).
  eapply @CompileLoopBase__many; eauto using TelEq_TelAppend_Cons_Second.
Qed.

Ltac _compile_CallListLength :=
  match_ProgOk
    ltac:(fun _ _ post _ _ =>
            match post with
            | [[ _ ->> BoundedListLength ?lst as _]] :: _ =>
              let vlst := find_name_in_precondition lst in
              (* FIXME use this instead of explicit continuations in every lemma *)
              compile_do_use_transitivity_to_handle_head_separately;
              [ eapply (CompileCallListBoundedNatLength vlst) | ]
            end).

Ltac _compile_LoopMany vlst :=
  change_post_into_TelAppend;
  let vhead := gensym "head" in
  let vtest := gensym "test" in
  eapply (CompileLoop__many vhead vtest vlst).

