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

Lemma CompileLoopBase__many :
  forall {A B}
    `{FacadeWrapper (Value QsADTs.ADTValue) B}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list B)}
    (lst: list B) init vhead vtest vlst
    fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv
    (f: A -> B -> A) tenvF,
    (* GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env -> *)
    (* (forall tenv a1 a2 b, tenvF tenv (a1, b) = tenvF tenv (a2, b)) -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
    (forall v, NotInTelescope vtest (tenvF tenv v)) ->
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

  instantiate (1 := [[`vlst ->> lst as ls]] :: [[`vtest ->> (bool2w match ls with
                                                              | nil => true
                                                              | _ :: _ => false
                                                              end) as _]]
                                         :: tenvF tenv init); admit.
  (* eapply (CompileTupleList_Empty_alt (N := N)); loop_t. *)

  2:instantiate (1 := [[ ` vlst ->> nil as _]] :: tenvF tenv (fold_left f lst init)); admit.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.

  simpl.
  eapply CompileWhileTrue; [ loop_t.. | ].

  instantiate (1 := [[ `vhead ->> a as _ ]] :: [[ `vlst ->> lst as _ ]] :: [[ ` vtest ->> Word.natToWord 32 0 as _]] :: tenvF tenv init); admit.

  (* rewrite <- GLabelMapFacts.find_mapsto_iff; assumption. *)

  move_to_front vtest. (* apply ProgOk_Chomp_Some; loop_t. *)
  move_to_front vlst. (* apply ProgOk_Chomp_Some; loop_t. *)
  setoid_rewrite H3.
  apply ProgOk_Chomp_Some; loop_t.
  apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; solve [eauto].

  move_to_front vtest.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.

  instantiate (1 := [[ ` vlst ->> lst as ls]]
                     :: [[`vtest ->> (bool2w match ls with
                                          | nil => true
                                          | _ :: _ => false
                                          end) as _]]
                     :: tenvF tenv (f init a)); admit.
  (* apply CompileTupleList_Empty_alt; loop_t. *)

  loop_t.
Qed.

Lemma CompileLoop__many :
  forall {A B}
    `{FacadeWrapper (Value QsADTs.ADTValue) B}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list B)}
    vhead vtest vlst (tenvF: A -> Telescope ADTValue) tenv'
    (lst: list B) init (f: A -> B -> A) tenv0 tenv
    env (ext: StringMap.t (Value QsADTs.ADTValue))
    fpop fempty fdealloc facadeBody facadeConclude,
    (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
    TelEq ext tenv0 ([[`vlst ->> lst as _]] :: TelAppend (tenvF init) tenv) ->
    (forall v, NotInTelescope vtest (TelAppend (tenvF v) tenv)) ->
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
  rewrite H2.
  setoid_rewrite Propagate_anonymous_ret.
  hoare.
  pose (fun tenv init => TelAppend (tenvF init) tenv) as tenvF'.
  change (TelAppend (tenvF init) tenv) with (tenvF' tenv init).
  change (TelAppend (tenvF (fold_left f lst init)) tenv) with (tenvF' tenv (fold_left f lst init)).
  eapply @CompileLoopBase__many; eauto using TelEq_TelAppend_Cons_Second.
Qed.

Lemma CompileCompose :
  forall {av} E B B' (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B') (stream: B) (cache: E)
    (tenv t1 t2: Telescope av) f (g: B -> B') ext env p1 p2,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ [[ vstream  ->> g stream as _ ]]
         :: tenv }}
      p1
    {{ TelAppend ([[ NTNone ->> enc1 cache as encoded1 ]]
                    :: [[ vstream ->> g (Transformer.transform stream (fst encoded1)) as _ ]]
                    :: f encoded1)
                 t1 }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ TelAppend ([[ vstream ->> g stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ TelAppend ([[ NTNone ->> enc2 (snd encoded1) as encoded2 ]]
                     :: [[ vstream ->> g (Transformer.transform stream1 (fst encoded2)) as _ ]]
                     :: f encoded2) t2 }}
     ∪ {{ ext }} // env) ->
    {{ [[ vstream ->> g stream as _ ]] :: tenv }}
      (Seq p1 p2)
    {{ TelAppend ([[ NTNone ->> @Compose.compose E B transformer enc1 enc2 cache as composed ]]
                    :: [[ vstream ->> g (Transformer.transform stream (fst composed)) as _ ]]
                    :: f composed) t2 }}
    ∪ {{ ext }} // env.
Proof.
  intros.
  repeat hoare.
  setoid_rewrite Compose_compose_acc.
  unfold compose_acc, encode_continue.
  cbv zeta in *.
  setoid_rewrite Propagate_anonymous_ret.
  setoid_rewrite Propagate_anonymous_ret in H0.
  setoid_rewrite Propagate_anonymous_ret in H1.
  destruct (enc1 _); simpl in *.
  destruct (enc2 _); simpl in *.
  erewrite (H (Transformer.transform _ _)); rewrite Transformer.transform_assoc; eassumption.
Qed.

Lemma CompileCompose_init :
  forall {av} E B B' (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B') (cache: E)
    (tenv t1 t2: Telescope av) f (g : B -> B') ext env p1 p2 pAlloc,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ tenv }}
      pAlloc
    {{ [[ vstream ->> g Transformer.transform_id as _ ]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ vstream ->> g Transformer.transform_id as _ ]] :: tenv }}
      p1
    {{ TelAppend ([[ NTNone ->> enc1 cache as encoded1 ]]
                    :: [[ vstream ->> g (Transformer.transform (Transformer.transform_id) (fst encoded1)) as _ ]]
                    :: f encoded1)
                 t1 }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform Transformer.transform_id (fst encoded1) in
     {{ TelAppend ([[ vstream ->> g stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ TelAppend ([[ NTNone ->> enc2 (snd encoded1) as encoded2 ]]
                     :: [[ vstream ->> g (Transformer.transform stream1 (fst encoded2)) as _ ]]
                     :: f encoded2) t2 }} ∪ {{ ext }} // env) ->
    {{ tenv }}
      (Seq pAlloc (Seq p1 p2))
    {{ TelAppend ([[ NTNone ->> @Compose.compose E B transformer enc1 enc2 cache as composed ]]
                    :: [[ vstream ->> g (fst composed) as _ ]]
                    :: f composed) t2 }}
    ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eauto using CompileCompose.
Qed.

(* Lemma CompileCallAllocOffset: *)
(*   forall (vtmp voffset: string) (tenv tenv' : Telescope ADTValue) *)
(*     ext env pNext fAllocCache, *)
(*     {{ [[ ` voffset ->> 0%N as _]]::tenv }} *)
(*       pNext *)
(*     {{ [[ ` voffset ->> 0%N as _]]::tenv' }} ∪ {{ ext }} // env -> *)
(*     {{ tenv }} *)
(*       Seq (Call vtmp fAllocCache [voffset]) pNext *)
(*     {{ [[ ` voffset ->> 0%N as _]]::tenv' }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   hoare; hoare. *)
(* Admitted. *)

(* (* FIXME there should be a generic wrapper for list of SCA-injected things *) *)
(* Lemma CompileCallListSCALength {A} {W: FacadeWrapper (Value ADTValue) (list A)}: *)
(*   forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue)) *)
(*     env (lst : FixList.FixList 8 A) *)
(*     fLength tenv', *)
(*     GLabelMap.MapsTo fLength (Axiomatic WordListADTSpec.Length) env -> *)
(*     TelEq ext tenv ([[`vlst ->> `lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *) *)
(*     {{ tenv }} *)
(*       Call varg fLength [vlst] *)
(*     {{ [[ ` varg ->> FixList.FixList_getlength lst as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(* Admitted. *)

Ltac _encode_FixInt :=
  match_ProgOk                  (* FIXME check when this is needed *)
    ltac:(fun prog pre post ext env =>
            match post with
            | [[ret (FixInt.FixInt_encode _ _) as _]] :: _ =>
              rewrite FixInt_encode_is_copy; (* FIXME make this an autorewrite *)
              setoid_rewrite Propagate_anonymous_ret; simpl;
              apply ProgOk_Transitivity_First
            end).

Ltac _compile_CallListLength :=
  match_ProgOk
    ltac:(fun _ _ post _ _ =>
            match post with
            | [[ _ ->> FixList.FixList_getlength ?lst as _]] :: _ =>
              let vlst := find_name_in_precondition (` lst) in
              (* FIXME use this instead of explicit continuations in every lemma *)
              compile_do_use_transitivity_to_handle_head_separately;
              [ eapply (CompileCallListSCALength vlst)
              (* FIXME || eapply (CompileCallListResourceLength vlst) ||
                          eapply (CompileCallListQuestionLength vlst) *)
              | ]
            end).

(* Lemma CompileCallAdd16 : *)
(*   forall `{FacadeWrapper (Value av) N} (tenv : Telescope av) (n : N) vn *)
(*     ext env, *)
(*     {{ [[`vn ->> n as _]]::tenv }} *)
(*       (Assign vn (Binop IL.Plus (Var vn) 16)) *)
(*     {{ [[`vn ->> (n + 16)%N as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(* Admitted. *)

(* Ltac _compile_CallAdd16 := *)
(*   compile_do_use_transitivity_to_handle_head_separately; *)
(*   [ apply CompileCallAdd16 | ]. *)

Ltac _compile_LoopMany vlst :=
  change_post_into_TelAppend;
  let vhead := gensym "head" in
  let vtest := gensym "test" in
  eapply (CompileLoop__many vhead vtest vlst).

(* Ltac _compile_CallAllocOffset := *)
(*   may_alloc_head; *)
(*   let vtmp := gensym "tmp" in *)
(*   eapply (CompileCallAllocOffset vtmp). *)

(* Require Import Bedrock.Word. *)

Lemma not_adt_is_sca :
  forall {A} `{FacadeWrapper (Value av) A},
    (forall (a: A), is_adt (wrap a) = false) ->
    exists w, (forall a, wrap a = SCA _ (w a)).
Proof.
  intros.
  exists (fun a => match wrap a with SCA x => x | _ => Word.wzero 32 end).
  intros; specialize (H0 a);
    destruct (wrap a); unfold is_adt in *; congruence.
Qed.

Lemma CompileRead':
  forall {A} `{FacadeWrapper (Value av) A}
    (vfrom vto : string) (a: A)
    (tenv tenv0: Telescope av) ext env,
    (* vfrom ∉ ext -> *)
    vto ∉ ext ->
    vfrom <> vto ->
    NotInTelescope vto tenv0 ->
    (forall a, is_adt (wrap a) = false) ->
    TelEq ext tenv ([[` vfrom ->> a as _]] :: tenv0) ->
    {{ tenv }}
      Assign vto (Var vfrom)
    {{ [[ ` vto ->> a as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? ? ? H; setoid_rewrite H.
  destruct (not_adt_is_sca H4).
  SameValues_Facade_t.
  f_equal; auto.
  match goal with
  | [ H: wrap _ = wrap _ |- _ ] => rewrite H
  end; SameValues_Facade_t.
Qed.

Ltac _compile_Read :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun _ pre post _ _ =>
            lazymatch post with
            | [[ _ ->> ?bs as _]] :: _ =>
              let k := find_name_in_precondition bs in
              eapply (CompileRead' k)
            end).

(* Lemma CompileConstantN : *)
(*   forall {av} {W: FacadeWrapper (Value av) N} *)
(*     N (vto : string) *)
(*     (tenv tenv': Telescope av) pNext ext env, *)
(*     {{ [[ ` vto ->> N as _]]::tenv }} *)
(*       pNext *)
(*     {{ [[ ` vto ->> N as _]]::tenv' }} ∪ {{ ext }} // env -> *)
(*     {{ tenv }} *)
(*       Seq (Assign vto (Const (@Word.NToWord _ N))) pNext *)
(*     {{ [[ ` vto ->> N as _]]::tenv' }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   hoare. *)
(*   hoare. *)
(* Admitted. *)

(* Ltac _compile_ReadConstantN := *)
(*   may_alloc_head; *)
(*   eapply CompileConstantN. *)
