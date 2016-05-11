Require Import CertifiedExtraction.Benchmarks.MicrobenchmarksSetup.
Require Import BinEncoders.Env.Examples.Dns.
Require Import BinEncodersProperties.

Unset Implicit Arguments.

Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.
Require Import CertifiedExtraction.Extraction.External.Loops.
Require Import CertifiedExtraction.Extraction.External.FacadeLoops.

(* FIXME Rename SameValues_remove_SCA to SameValues_remove_W *)

(* FIXME merge these general lemmas about non-adts, renaming the existing versions to _W *)

Lemma SameValues_remove_SCA:
  forall (av : Type) {A} (Wrapper: FacadeWrapper (Value av) A),
    (forall a, is_adt (wrap a) = false) ->
    forall (tenv' : Telescope av)
    (ext : StringMap.t (Value av)) (k : StringMap.key)
    (final_state : State av) (x : A),
    StringMap.MapsTo k (wrap x) final_state ->
    StringMap.remove (elt:=Value av) k final_state ≲ tenv' ∪ ext ->
    final_state ≲ tenv' ∪ ext.
Proof.
  induction tenv'; simpl; intros.
  - rewrite (add_redundant_cancel H0).
    rewrite <- add_remove_cancel; try reflexivity.
    pose proof (H x) as p; destruct (wrap x); simpl in p; try congruence; clear p.
    apply WeakEq_pop_SCA.
    apply StringMap.remove_1; reflexivity.
    assumption.
  - destruct key; repeat cleanup.
    + eauto.
    + SameValues_Fiat_t.
      StringMap_t.
      rewrite remove_mapsto_iff in *.
      cleanup.
      StringMap_t.
      eexists; repeat cleanup; eauto.
      eapply H0.
      rewrite remove_mapsto_iff in *; eauto.
      rewrite remove_remove_comm; eauto.
Qed.

Hint Resolve SameValues_remove_SCA : SameValues_db.

Lemma CompileDeallocSCA_discretely :
  forall {av} {A} (H: FacadeWrapper (Value av) A) (tenv tenv': Telescope av) ext env k (v: Comp A) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    (forall a, is_adt (wrap a) = false) ->
    {{ [[`k ~~> v as _]] :: tenv }} prog {{ [[`k ~~> v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma SameValues_add_SCA:
  forall av {A} (Wrp: FacadeWrapper (Value av) A)
    tel (st: StringMap.t (Value av)) k ext (v: A),
    (forall a, is_adt (wrap a) = false) ->
    k ∉ st ->
    st ≲ tel ∪ ext ->
    (StringMap.add k (wrap v) st) ≲ tel ∪ ext.
Proof.
  induction tel;
  repeat (t_Morphism || SameValues_Facade_t).
  pose proof (H v); destruct (wrap v); try (simpl in *; congruence); SameValues_Facade_t.
  apply H; repeat (t_Morphism || SameValues_Facade_t).
Qed.

Lemma SameValues_Dealloc_SCA :
  forall {av} {A} (Wrp: FacadeWrapper (Value av) A)
    st k (v: Comp A) tail ext,
    (forall a, is_adt (wrap a) = false) ->
    st ≲ Cons (av := av) (NTSome k) v tail ∪ ext ->
    st ≲ Cons NTNone v tail ∪ ext.
Proof.
  SameValues_Fiat_t.
  StringMap_t.
  repeat match goal with
         | [ H: StringMap.MapsTo _ _ ?st |- ?st ≲ _ ∪ _ ] => rewrite (MapsTo_add_remove H)
         | [ H: is_adt ?v = false |- _ ] => destruct v; simpl in H; try congruence
         | [ H: match ?x with _ => _ end = _ |- _ ] => destruct x; try congruence
         end.
  apply SameValues_add_SCA; eauto using StringMap.remove_1.
Qed.

Lemma CompileDeallocSCA:
  forall {av} {A} (Wrp: FacadeWrapper (Value av) A) (env : Env av) k (compSCA: Comp A) tail tail' ext prog,
    (forall a, is_adt (wrap a) = false) ->
    {{ [[compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  learn (SameValues_Dealloc_SCA _ _ _ _ _ _ H H1);
  SameValues_Facade_t.
Qed.

Lemma CompileDeallocSCA_discretely_anonymous:
  forall {av} {A} (Wrp: FacadeWrapper (Value av) A) (env : Env av) k (compSCA: Comp A) tail tail' ext prog,
    (forall a, is_adt (wrap a) = false) ->
    {{ [[compSCA as _]]::tail}}
      prog
    {{ [[compSCA as _]]::tail' }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> compSCA as _]]::tail}}
      prog
    {{ tail' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  learn (SameValues_Dealloc_SCA _ _ _ _ _ _ H H1);
  SameValues_Facade_t.
Qed.

Fixpoint TelAppend {av} (t1 t2: Telescope av) :=
  match t1 with
  | Nil => t2
  | Cons T key val tail => Cons (T := T) key val (fun v => TelAppend (tail v) t2)
  end.

Lemma TelAppend_Nil {av} :
  forall t: Telescope av,
    TelStrongEq (TelAppend t Nil) t.
Proof.
  induction t; simpl.
  + reflexivity.
  + econstructor; eauto with typeclass_instances.
Qed.

Lemma TelEq_TelAppend_Cons_Second {av A B}:
  forall {H : FacadeWrapper (Value av) B} (t1: Telescope av) t2 k (v : Comp A) ext,
    TelEq ext
          ([[ k ~~> v as vv]] :: TelAppend t1 (t2 vv))
          (TelAppend t1 ([[ k ~~> v as vv]] :: (t2 vv))).
Proof.
  intros.
  induction t1; simpl.
  + reflexivity.
  + rewrite TelEq_swap.
    setoid_rewrite H0.
    reflexivity.
Qed.

Add Parametric Morphism {av} : (@TelAppend av)
    with signature ((TelStrongEq) ==> (TelStrongEq) ==> (TelStrongEq))
      as TelAppend_TelStrongEq_morphism.
Proof.
  induction 1; simpl.
  + eauto with typeclass_instances.
  + intros.
    econstructor; eauto.
Qed.

Add Parametric Morphism {av} ext : (@TelAppend av)
    with signature (TelStrongEq ==> (TelEq ext) ==> (TelEq ext))
      as TelAppend_TelStrongEq_TelEq_morphism.
Proof.
  intros.
  rewrite H; clear H.
  induction y; simpl; intros.
  + assumption.
  + apply Cons_TelEq_pointwise_morphism; red; eauto.
Qed.

Add Parametric Morphism {av} ext : (@TelAppend av)
    with signature (TelEq ext ==> TelEq ext ==> (TelEq ext))
      as TelAppend_TelEq_morphism.
Proof.
  intros.
  rewrite H0; clear H0.
  induction y0.
  + rewrite !TelAppend_Nil; assumption.
  + setoid_rewrite <- TelEq_TelAppend_Cons_Second.
    setoid_rewrite H0.
    reflexivity.
Qed.

Lemma CompileCallWrite16:
  forall {av} {W: FacadeWrapper av (list bool)} {W': FacadeWrapper (Value av) (BitArray 16)}
    (vtmp varg vstream : string) (stream : list bool) (tenv tenv' tenv'': Telescope av)
    (n : BitArray 16) ext env
    pArg pNext fWrite16,
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream ++ ` n as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> stream ++ ` n as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite16 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> stream ++ ` n as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  hoare.
  hoare.
  hoare.
Admitted.

Lemma TelEq_same_wrap :
  forall {av A1 A2} {W1: FacadeWrapper (Value av) A1} {W2: FacadeWrapper (Value av) A2}
    (x1: A1) (x2: A2),
    wrap x1 = wrap x2 ->
    forall (t: Telescope av) ext k,
      TelEq ext (Cons (NTSome k) (ret x1) (fun _ => t)) (Cons (NTSome k) (ret x2) (fun _ => t)).
Proof.
  split; SameValues_Fiat_t.
Qed.

Lemma CompileCallWrite16_EncodeAndPad:
  forall {av} {W: FacadeWrapper av (list bool)}
    {W': FacadeWrapper (Value av) (BitArray 16)}
    {W': FacadeWrapper (Value av) (BoundedN 16)}
    (vtmp varg vstream : string) (stream : list bool) (tenv tenv' tenv'': Telescope av)
    (n : BoundedN 16) ext env
    pArg pNext fWrite16,
    wrap n = wrap (EncodeAndPad n) ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream ++ ` (EncodeAndPad n) as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> stream ++ ` (EncodeAndPad n) as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite16 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> stream ++ ` (EncodeAndPad n) as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  intros * Heq H ?.
  setoid_rewrite (TelEq_same_wrap _ _ Heq) in H.
  eapply CompileCallWrite16; eauto.
Qed.

Ltac rewrite_posed term equation :=
  let head := fresh in
  let eqn := fresh in
  remember term as head eqn:eqn;
  rewrite equation in eqn;
  rewrite eqn; clear dependent head.

Ltac _compile_CallWrite16 :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let post' := (eval simpl in post) in
            lazymatch post' with
            | Cons _ (ret (_ ++ ` ?arg)) _ =>
              let vtmp := gensym "tmp" in
              let varg := gensym "arg" in
              match arg with
              | EncodeAndPad _ => eapply (CompileCallWrite16_EncodeAndPad vtmp varg)
              | _ => eapply (CompileCallWrite16 vtmp varg)
              end
            end).

(* Ltac instantiate_tail_of_post term := *)
(*   match_ProgOk *)
(*     ltac:(fun prog pre post ext env => *)
(*             match constr:post with *)
(*             | context[?x] => *)
(*               is_evar x; *)
(*               match type of x with *)
(*               | @Telescope _ => unify x term *)
(*               end *)
(*             end). *)

Ltac standalone_tail tail :=
  (* Recurse down the TAIL of telescope (of type (a: A) → Telescope) to find the
     first subtelescope that doesn't depend on ‘a’. *)
  lazymatch tail with (* This is a really cute piece of code *)
  | (fun a => Cons _ _ (fun _ => ?tail)) => constr:(tail)
  | (fun a => Cons _ _ (fun _ => @?tail a)) => standalone_tail tail
  end.

Ltac function_surrounding_standalone_tail tail :=
  (* Recurse down the TAIL of telescope (of type (a: A) → Telescope) to find the
     first subtelescope that doesn't depend on ‘a’, and construct a function
     plugging an arbitrary argument instead of that subtelescope. *)
  lazymatch tail with
  | (fun a: ?A => Cons ?k ?v (fun _ => ?tail)) =>
    let _t := constr:(tail) in (* Fails if ‘tail’ depends on a *)
    constr:(fun plug => fun a: A => (Cons k v (fun _ => plug)))
  | (fun a: ?A => Cons ?k ?v (fun _ => @?tail a)) =>
    let fn := function_surrounding_standalone_tail tail in
    eval cbv beta in (fun plug => fun a: A => (Cons k v (fun _ => fn plug a)))
  end.

Ltac split_tail_of_telescope tel :=
  (* Split the tail TEL (a function) into two parts, using ‘standalone_tail’ and
     ‘function_surrounding_standalone_tail’. *)
  match tel with
  | Cons ?k ?v ?tail =>
    let tl := standalone_tail tail in
    let tenvF := function_surrounding_standalone_tail tail in
    (* let tenvF := (eval cbv beta in (fun plug => Cons k v (tenvF plug))) in *)
    constr:(tenvF, tl)
  end.

Ltac make_TelAppend tel :=
  (** Change the tail of TEL into a ‘TelAppend’ of two parts: one depending on
      the head value of tail, and the other independent of it. *)
  match tel with
  | Cons ?k ?v ?tail =>
    let appTl := standalone_tail tail in
    let tenvF := function_surrounding_standalone_tail tail in
    let appHead := (eval cbv beta in (Cons k v (tenvF Nil))) in
    constr:(TelAppend appHead appTl)
  end.

Ltac change_post_into_TelAppend :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       let pp := fresh in
                       set post as pp; (* Otherwise change sometimes fails *)
                       let post' := make_TelAppend post in
                       change pp with post'; clear pp).


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

  instantiate (1 := [[ `vhead ->> a as _ ]] :: [[ `vlst ->> lst as _ ]] :: [[ ` vtest ->> W0 as _]] :: tenvF tenv init); admit.

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
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (stream: B) (cache: E)
    (tenv t1 t2: Telescope av) f ext env p1 p2,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ [[ vstream  ->>  stream as _ ]]
         :: tenv }}
      p1
    {{ TelAppend ([[ NTNone  ->>  enc1 cache as encoded1 ]]
                    :: [[ vstream  ->>  Transformer.transform stream (fst encoded1) as _ ]]
                    :: f encoded1)
                 t1 }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ TelAppend ([[ vstream  ->>  stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ TelAppend ([[ NTNone  ->>  enc2 (snd encoded1) as encoded2 ]]
                     :: [[ vstream  ->>  Transformer.transform stream1 (fst encoded2) as _ ]]
                     :: f encoded2) t2 }}
     ∪ {{ ext }} // env) ->
    {{ [[ vstream  ->>  stream as _ ]] :: tenv }}
      (Seq p1 p2)
    {{ TelAppend ([[ NTNone  ->>  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
                    :: [[ vstream  ->>  Transformer.transform stream (fst composed) as _ ]]
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
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (cache: E)
    (tenv t1 t2: Telescope av) f ext env p1 p2 pAlloc,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ tenv }}
      pAlloc
    {{ [[ vstream  ->>  Transformer.transform_id as _ ]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ vstream  ->>  Transformer.transform_id as _ ]] :: tenv }}
      p1
    {{ TelAppend ([[ NTNone  ->>  enc1 cache as encoded1 ]]
                    :: [[ vstream  ->>  Transformer.transform (Transformer.transform_id) (fst encoded1) as _ ]]
                    :: f encoded1)
                 t1 }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform Transformer.transform_id (fst encoded1) in
     {{ TelAppend ([[ vstream  ->>  stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ TelAppend ([[ NTNone  ->>  enc2 (snd encoded1) as encoded2 ]]
                     :: [[ vstream  ->>  Transformer.transform stream1 (fst encoded2) as _ ]]
                     :: f encoded2) t2 }} ∪ {{ ext }} // env) ->
    {{ tenv }}
      (Seq pAlloc (Seq p1 p2))
    {{ TelAppend ([[ NTNone  ->>  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
                    :: [[ vstream  ->>  (fst composed) as _ ]]
                    :: f composed) t2 }}
    ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eauto using CompileCompose.
Qed.

Lemma Propagate_anonymous_ret__fast:
  forall {av A} (v : A) (tenv : Telescope av) tenv' env ext p,
    {{ tenv }} p {{ tenv' v }} ∪ {{ ext }} // env ->
    {{ tenv }} p {{ Cons NTNone (ret v) tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; rewrite Propagate_anonymous_ret; assumption.
Qed.

Lemma CompileCallAllocString:
  forall {av} {W: FacadeWrapper av (list bool)}
    (vtmp vstream : string) (tenv tenv' : Telescope av)
    ext (env : GLabelMap.t (FuncSpec av))
    pNext fAllocString,
    {{ [[ ` vstream ->> @nil bool as _]]::tenv }}
      pNext
    {{ [[ ` vstream ->> @nil bool as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocString [vstream]) pNext
    {{ [[ ` vstream ->> @nil bool as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Instance WrapListResources : FacadeWrapper ADTValue (list resource_t). Admitted.
Instance WrapListQuestions : FacadeWrapper ADTValue (list question_t). Admitted.
Instance WrapQuestion : (FacadeWrapper ADTValue question_t). Admitted.
Instance WrapResource : (FacadeWrapper ADTValue resource_t). Admitted.
(* Instance WrapCache : (FacadeWrapper ADTValue DnsMap.CacheT). Admitted. *)
Instance WrapDMapT : FacadeWrapper ADTValue DnsMap.DMapT. Admitted.
Instance WrapEMapT : FacadeWrapper ADTValue DnsMap.EMapT. Admitted.
Instance WrapN : FacadeWrapper (Value ADTValue) N. Admitted.
Instance WrapListBool : FacadeWrapper ADTValue (list bool). Admitted.


Lemma BoundedN_below_pow2_1632:
  forall v : BoundedN 16,
    (lt (N.to_nat (` v)) (Word.pow2 32)).
Proof.
  intros; eapply Lt.lt_trans;
    eauto using BoundedN_below_pow2, Array.pow2_monotone, nat_16_lt_32.
Qed.

Lemma WrapN16_inj {av} {W: FacadeWrapper (Value av) (Word.word 32)}:
  forall v v' : BoundedN 16,
    wrap (FacadeWrapper := W) (Word.NToWord (sz := 32) (` v)) =
    wrap (FacadeWrapper := W) (Word.NToWord (sz := 32) (` v')) ->
    v = v'.
Proof.
  intros; rewrite !Word.NToWord_nat in H.
  apply wrap_inj, Word.natToWord_inj, N2Nat.inj in H;
  eauto using exist_irrel', UipComparison.UIP, BoundedN_below_pow2_1632.
Qed.

Instance WrapN16 : FacadeWrapper (Value ADTValue) (BoundedN 16) :=
  {| wrap x := wrap (Word.NToWord (sz := 32) (` x));
     wrap_inj := WrapN16_inj |}.

Require Import Word.

Lemma WrapListBool16_inj {av} {W: FacadeWrapper (Value av) (Word.word 32)}:
  forall v v' : BitArray 16,
    wrap (FacadeWrapper := W) (Word16ToWord32 (FixListBoolToWord v)) =
    wrap (FacadeWrapper := W) (Word16ToWord32 (FixListBoolToWord v')) ->
    v = v'.
Proof.
  eauto using FixListBoolToWord_inj, Word16ToWord32_inj, wrap_inj.
Qed.

Instance WrapListBool16 : FacadeWrapper (Value ADTValue) (BitArray 16).
Proof.
  refine {| wrap x := wrap (Word16ToWord32 (FixListBoolToWord x));
            wrap_inj := WrapListBool16_inj |}.
Defined.

Lemma CompileCallAllocEMap:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap ->> DnsMap.EMap.empty DnsMap.position_t as _]]::tenv }}
      pNext
    {{ [[ ` veMap ->> DnsMap.EMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap ->> DnsMap.EMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallAllocDMap:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap ->> DnsMap.DMap.empty (list DnsMap.word_t) as _]]::tenv }}
      pNext
    {{ [[ ` veMap ->> DnsMap.DMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap ->> DnsMap.DMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallAllocOffset:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap ->> 0%N as _]]::tenv }}
      pNext
    {{ [[ ` veMap ->> 0%N as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap ->> 0%N as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallListResourceLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : FixList.FixList 16 resource_t)
    flength tenv',
    TelEq ext tenv ([[`vlst ->> `lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg flength [vlst]
    {{ [[ ` varg ->> FixList.FixList_getlength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Lemma CompileCallListQuestionLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : FixList.FixList 16 question_t)
    flength tenv',
    TelEq ext tenv ([[`vlst ->> `lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg flength [vlst]
    {{ [[ ` varg ->> FixList.FixList_getlength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac match_ProgOk_constr continuation :=
  lazymatch goal with
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] =>
    let ret := continuation prog pre post ext env in
    constr:ret
  end.

Ltac find_in_tenv tenv v :=
  lazymatch tenv with
  | context[Cons ?k (ret v) _] => constr:k
  end.

Ltac find_in_precondition v :=
  match_ProgOk_constr
    ltac:(fun prog pre post ext env => find_in_tenv pre v).

Ltac NameTag_name v :=
  match v with
  | NTSome ?name => constr:name
  end.

Ltac find_name_in_precondition v :=
  let nt := find_in_precondition v in
  let v := NameTag_name nt in
  constr:v.

Ltac may_alloc k :=
  (* Fail if ‘k’ is bound in precondition. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match pre with
            | context[Cons k _ _] => fail 1 "Precondition contains" k
            | context[Cons (NTSome k) _ _] => fail 1 "Precondition contains" k
            | _ => idtac
            end).

Ltac may_alloc_head :=
  (* Fail if pre-condition contains key of head of post-condition. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons ?k _ _ => may_alloc k
            end).

Lemma CompileCallGetQuestionType:
  forall (vtmp vquestion vtype : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (question : question_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vquestion ->> question as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 1)) (Call vtype fget [vtmp; vquestion])
    {{ [[ ` vtype ->> FixInt_of_type (qtype question) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Ltac _packet_encodeQuestionType :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | Cons _ (ret (FixInt_of_type (qtype ?question))) _ =>
              let vtmp := gensym "tmp" in
              let vquestion := find_name_in_precondition question in
              compile_do_use_transitivity_to_handle_head_separately;
              [ eapply (CompileCallGetQuestionType vtmp vquestion) | ]
            end).

Lemma CompileCallGetResourceType:
  forall (vtmp vresource vtype : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (resource : resource_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vresource ->> resource as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 1)) (Call vtype fget [vtmp; vresource])
    {{ [[ ` vtype ->> FixInt_of_type (rtype resource) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Ltac _packet_encodeType :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | Cons _ (ret (FixInt_of_type (_ ?question))) _ =>
              let vtmp := gensym "tmp" in
              let vquestion := find_name_in_precondition question in
              compile_do_use_transitivity_to_handle_head_separately;
              [ (eapply (CompileCallGetQuestionType vtmp vquestion) ||
                 eapply (CompileCallGetResourceType vtmp vquestion))
              | ]
            end).

Lemma CompileCallGetQuestionClass: (* FIXME merge into a single lemma once encoding of questions and answers is decided upon *)
  forall (vtmp vquestion vclass : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (question : question_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vquestion ->> question as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 2)) (Call vclass fget [vtmp; vquestion])
    {{ [[ ` vclass ->> FixInt_of_class (qclass question) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Lemma CompileCallGetResourceClass: (* FIXME merge into a single lemma once encoding of questions and answers is decided upon *)
  forall (vtmp vresource vclass : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (resource : resource_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vresource ->> resource as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 2)) (Call vclass fget [vtmp; vresource])
    {{ [[ ` vclass ->> FixInt_of_class (rclass resource) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Ltac _packet_encodeClass :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | Cons _ (ret (FixInt_of_class (_ ?question))) _ =>
              let vtmp := gensym "tmp" in
              let vquestion := find_name_in_precondition question in
              compile_do_use_transitivity_to_handle_head_separately;
              [ ( eapply (CompileCallGetQuestionClass vtmp vquestion) ||
                  eapply (CompileCallGetResourceClass vtmp vquestion) )
              | ]
            end).

Lemma CompileCallDeallocQuestion: (* FIXME merge with other lemmas regarding deallocation of tuple-encoded structures *)
  forall (vtmp vquestion: string) (q: question_t) (tenv: Telescope ADTValue)
    ext env fDealloc,
    NotInTelescope vquestion tenv ->
    {{ [[ ` vquestion ->> q as _]]::tenv }}
      (Call vtmp fDealloc [vquestion])
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac _compile_CallDeallocQuestion :=
  let vtmp := gensym "tmp" in
  eapply (CompileCallDeallocQuestion vtmp).

Lemma CompileCallDeallocResource: (* FIXME merge with other lemmas regarding deallocation of tuple-encoded structures *)
  forall (vtmp vresource: string) (q: resource_t) (tenv: Telescope ADTValue)
    ext env fDealloc,
    NotInTelescope vresource tenv ->
    {{ [[ ` vresource ->> q as _]]::tenv }}
      (Call vtmp fDealloc [vresource])
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac _compile_CallDeallocResource :=
  let vtmp := gensym "tmp" in
  eapply (CompileCallDeallocResource vtmp).

Ltac _packet_encode_FixInt :=
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
              [ (eapply (CompileCallListResourceLength vlst) ||
                 eapply (CompileCallListQuestionLength vlst))
              | ]
            end).

Lemma WrapN16_WrapListBool16:
  forall s : BoundedN 16,
    wrap (FacadeWrapper := WrapN16) s = wrap (FacadeWrapper := WrapListBool16) (EncodeAndPad s).
Proof.
Admitted.

Lemma CompileCallAdd16 :
  forall `{FacadeWrapper (Value av) N} (tenv : Telescope av) (n : N) vn
    ext env,
    {{ [[`vn ->> n as _]]::tenv }}
      (Assign vn (Binop IL.Plus (Var vn) 16))
    {{ [[`vn ->> (n + 16)%N as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac _compile_CallAdd16 :=
  compile_do_use_transitivity_to_handle_head_separately;
  [ apply CompileCallAdd16 | ].

Ltac _compile_CallAllocString :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocString vtmp).

Ltac _packet_encode_IList__rewrite_as_fold :=
  lazymatch goal with         (* FIXME make this an autorewrite *)
  | [  |- appcontext[fold_left (IList.IList_encode'_body ?cache ?transformer _)] ] =>
    setoid_rewrite (IList_post_transform_TelEq cache transformer); [ | reflexivity ]
  end.

Ltac specialize_body hyp term :=
  let new := fresh in
  pose (hyp term) as fresh;
  unfold hyp in *;
  clear hyp;
  rename fresh into hyp.

Ltac _compile_LoopMany vlst :=
  change_post_into_TelAppend;
  let vhead := gensym "head" in
  let vtest := gensym "test" in
  eapply (CompileLoop__many vhead vtest vlst).

Ltac _packet_encode_IList__compile_loop :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | appcontext[fold_left (IList.IList_encode'_body _ _ _) ?lst] =>
              match pre with
              | context[Cons (NTSome ?vlst) (ret lst) _] =>
                _compile_LoopMany vlst
              end
            end).

Ltac _packet_encode_IList_compile :=
  _packet_encode_IList__rewrite_as_fold;
  _packet_encode_IList__compile_loop.

Ltac _compile_CallAllocEMap :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocEMap vtmp).

Ltac _compile_CallAllocDMap :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocDMap vtmp).

Ltac _compile_CallAllocOffset :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocOffset vtmp).

Lemma ProgOk_Add_snd_ret :
  forall {A B av} (f: B -> Telescope av) (kfst: NameTag av _) (cpair: A * B) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
    {{ [[ NTNone  ->>  cpair as pair ]]
         :: [[ kfst  ->>  fst pair as p1 ]]
         :: TelAppend (f (snd pair)) tenv' }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  ->>  cpair as pair ]]
         :: [[ kfst  ->>  fst pair as p1 ]]
         :: TelAppend (f (snd pair)) tenv' }}
      p2
    {{ [[ NTNone  ->>  cpair as pair ]]
         :: [[ kfst  ->>  fst pair as p1 ]]
         :: TelAppend (Nil) tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
    {{ [[ kfst  ->>  fst cpair as p1 ]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
Qed.

Ltac mod_first :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match pre with
            | (Cons _ _ (fun _ => ?tail)) =>
              match post with
              | context[?e] => is_evar e; (unify e tail)
              end
            end).

Ltac keep_first :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | context[?e] => is_evar e; (unify e pre)
            end).

Lemma IList_encode'_body_as_compose {HD bin : Type} :
  forall (cache : Cache.Cache) (transformer : Transformer.Transformer bin) f acc (head: HD),
    (IList.IList_encode'_body cache transformer f acc head) = (* Cache parameter isn't used *)
    Compose.compose transformer (fun c => (fst acc, c)) (f head) (snd acc).
Proof.
  intros; unfold IList.IList_encode'_body, Compose.compose; simpl.
  destruct acc; simpl; destruct (f _ _); reflexivity.
Qed.

Lemma let_ret2 {A1 A2 B av}:
  forall (xy: A1 * A2) (f: A1 -> A2 -> B) tenv (ext: StringMap.t (Value av)),
    TelEq ext
          ([[ ret (let (x, y) := xy in f x y) as fxy ]] :: tenv fxy)
          ([[ ret xy as xy ]] :: tenv (f (fst xy) (snd xy))).
Proof.
  intros (? & ?) *.
  rewrite !Propagate_anonymous_ret; simpl.
  reflexivity.
Qed.

Lemma IList_encode'_body_simpl :
  forall (cache : Cache.Cache) {av HD bin : Type} (transformer : Transformer.Transformer bin)
    f acc (head: HD) (tail: _ -> Telescope av) ext,
    TelEq ext
          ([[ ret (IList.IList_encode'_body cache transformer f acc head) as v ]] :: tail v)
          ([[ ret (f head (snd acc)) as v ]] :: tail (Transformer.transform (fst acc) (fst v), (snd v))).
Proof.
  intros; unfold IList.IList_encode'_body; destruct acc.
  rewrite let_ret2; reflexivity.
Qed.

Lemma CompileRead16:
  forall {av} {W: FacadeWrapper (Value av) (BitArray 16) }
    (vfrom vto : string) (bs: {s : list bool | Datatypes.length s = 16})
    (tenv tenv0 tenv': Telescope av) pNext  ext env,
    TelEq ext tenv ([[` vfrom ->> bs as _]] :: tenv0) ->
    {{ [[ ` vto ->> bs as _]]::tenv }}
      pNext
    {{ [[ ` vto ->> bs as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Assign vto (Var vfrom)) pNext
    {{ [[ ` vto ->> bs as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  intros * H; rewrite H.
  hoare.
  hoare.
Admitted.

Ltac _compile_Read16 :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun _ pre post _ _ =>
            match post with
            | [[ _ ->> ?bs as _]] :: _ =>
              let k := find_name_in_precondition bs in
              eapply (CompileRead16 k)
            end).

Lemma CompileConstantN :
  forall {av} {W: FacadeWrapper (Value av) N}
    N (vto : string)
    (tenv tenv': Telescope av) pNext ext env,
    {{ [[ ` vto ->> N as _]]::tenv }}
      pNext
    {{ [[ ` vto ->> N as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Assign vto (Const (Word.NToWord N))) pNext
    {{ [[ ` vto ->> N as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare.
  hoare.
Admitted.

Ltac _compile_ReadConstantN :=
  may_alloc_head;
  eapply CompileConstantN.

Opaque Transformer.transform_id.

Definition PacketAsCollectionOfVariables
           {av} vid vmask vquestion vanswer vauthority vadditional (p: packet_t)
  : Telescope av :=
  [[ vid ->> p.(pid) as _ ]]
    :: [[ vmask ->> p.(pmask) as _ ]]
    :: [[ vquestion ->> ` p.(pquestion) as _ ]]
    :: [[ vanswer ->> ` p.(panswer) as _ ]]
    :: [[ vauthority ->> ` p.(pauthority) as _ ]]
    :: [[ vadditional ->> ` p.(padditional) as _ ]]
    :: Nil.

Definition DnsCacheAsCollectionOfVariables
           {av} veMap vdMap voffs (c: DnsMap.CacheT)
  : Telescope av :=
  [[ veMap ->> c.(DnsMap.eMap) as _ ]]
    :: [[ vdMap ->> c.(DnsMap.dMap) as _ ]]
    :: [[ voffs ->> c.(DnsMap.offs) as _ ]]
    :: Nil.

Create HintDb packet_autorewrite_db.
Hint Rewrite @NToWord_of_nat : packet_autorewrite_db.
Hint Rewrite @NToWord_WordToN : packet_autorewrite_db.
Hint Rewrite @length_of_fixed_length_list : packet_autorewrite_db.
Hint Rewrite @IList.IList_encode'_as_foldl : packet_autorewrite_db.
Hint Rewrite @FixInt_encode_is_copy : packet_autorewrite_db.
Hint Rewrite @IList_encode_bools_is_copy : packet_autorewrite_db.
Hint Rewrite @FixList_is_IList : packet_autorewrite_db.
Hint Rewrite app_nil_r : packet_autorewrite_db.
Hint Rewrite (@IList_encode'_body_simpl DnsMap.cache) : packet_autorewrite_db.
Hint Unfold IList.IList_encode : packet_autorewrite_db.
Hint Unfold FixList.FixList_encode : packet_autorewrite_db.
Hint Unfold TelAppend : packet_autorewrite_db.
Hint Unfold PacketAsCollectionOfVariables : packet_autorewrite_db.
Hint Unfold DnsCacheAsCollectionOfVariables : packet_autorewrite_db.
Hint Unfold Enum.Enum_encode : packet_autorewrite_db.
Hint Unfold encode_question : packet_autorewrite_db.
Hint Unfold encode_resource : packet_autorewrite_db.

Ltac simpl_without_uncaught_exception :=
  (* Avoids an “Uncaught exception: not found” *)
  set_evars; simpl; subst_evars.

Ltac _packet_encode_cleanup :=
  match goal with
  | _ => match_ProgOk
          ltac:(fun prog pre post ext env =>
                  match post with
                  | [[ ret (_, _) as _]] :: _ =>
                    apply Propagate_anonymous_ret__fast
                  end)
  | _ => progress simpl
  | _ => progress autounfold with packet_autorewrite_db
  | _ => progress autorewrite with packet_autorewrite_db
  end.

(*  Disable the propagation of rets for this file, since we use them for structure *)
Ltac _compile_rewrite_bind ::= fail.
(*  Disable automatic decompilation for this file (it only works for simple examples with no evars in the post) *)
Ltac _compile_destructor ::= fail.

Arguments NotInTelescope: simpl never.

Tactic Notation "apply_in_body" hyp(H) constr(f) :=
  let H' := fresh in
  pose (f H) as H';
  unfold H in *; clear H;
  rename H' into H.

Definition CompositionDepth (n: nat) := S n.

Ltac packet_compile_compose :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | [[ ret _ as _ ]] :: [[ ?k ->> _ as _ ]] :: _ =>
              change_post_into_TelAppend;
              first [ eapply CompileCompose |
                      may_alloc k; eapply CompileCompose_init ];
              [ try match goal with
                    | [ H := CompositionDepth _ |- _ ] => apply_in_body H CompositionDepth
                    end.. | ];
              intros
            end).

Ltac _packet_prepare_cache :=
  may_alloc_head; (* Only create bindings for the cache once. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons (NTSome _) (ret (fst (Compose.compose _ _ _ _))) _ =>
              let veMap := gensym "eMap" in
              let vdMap := gensym "dMap" in
              let voffs := gensym "offs" in
              apply (ProgOk_Add_snd_ret
                       (DnsCacheAsCollectionOfVariables
                          (NTSome veMap) (NTSome vdMap) (NTSome voffs)))
            end).

Ltac packet_start_compiling :=
  repeat match goal with
         | [ p: packet_t |- _ ] => destruct p
         | _ => progress unfold packet_encode, encode_packet; simpl
         end.

Hint Resolve WrapN16_WrapListBool16 : compile_do_side_conditions_db.

Definition Counted {A} (x: A) := x.

Ltac count_instances head_symbol counter_var :=
  pose 0 as counter_var;
  repeat match goal with
         | [  |- appcontext C [head_symbol ?x] ] =>
           apply_in_body counter_var S;
           let C' := context C[(Counted head_symbol) x] in change C'
         end;
  change (Counted head_symbol) with (head_symbol).

Ltac last_argument fun_appl :=
  lazymatch fun_appl with
  | _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ ?x => x
  | _ _ _ _ ?x => x
  | _ _ _ ?x => x
  | _ _ ?x => x
  | _ ?x => x
  | ?x => x
  end.

Fixpoint MakeString base ncopies :=
  match ncopies with
  | O => ""%string
  | S n => String.append base (MakeString base n)
  end.

Ltac _packet_show_progress :=
  try match_ProgOk
      ltac:(fun prog pre post ext env =>
              lazymatch pre with
              | context[@Compose.compose] => fail "In final (deallocation) goals"
              | _ => lazymatch post with
                    | Cons NTNone (ret (Compose.compose _ ?action _ _)) _ =>
                      lazymatch goal with
                      | H := Counted action |- _ => fail "Already counted"
                      | _ => pose (Counted action);
                            let counter := fresh in
                            count_instances @Compose.compose counter;
                            let arg := last_argument action in
                            let steps_left := (eval unfold counter in counter) in
                            (try pose (CompositionDepth 0) as CompositionDepth);
                            lazymatch goal with
                            | H := CompositionDepth _ |- _ =>
                              let indent := (eval compute in (MakeString """" (pred H))) in
                              match steps_left with
                              | 1 => idtac "<infomsg>" indent "-" steps_left "step left:"
                                          "compiling encoder for" arg "...</infomsg>"
                              | _ => idtac "<infomsg>" indent "-" steps_left "steps left:"
                                          "compiling encoder for" arg "...</infomsg>"
                              end
                            end;
                            clear counter
                      end
                    end
              end).

Ltac _packet_trace_progress :=
  debug "--------------------------------------------------------------------------------";
  match goal with
  | |- ?g => debug g
  end.

Ltac _packet_encode_step :=
  (* try _packet_show_progress; *)
  match goal with
  | _ => _packet_encode_cleanup
  | _ => _packet_prepare_cache
  | _ => _packet_encode_FixInt
  | _ => _packet_encode_IList_compile
  | _ => _packet_encodeType
  | _ => _packet_encodeClass
  | _ => _compile_CallWrite16
  | _ => _compile_Read16
  | _ => _compile_ReadConstantN
  | _ => _compile_CallAdd16
  | _ => _compile_CallListLength
  | _ => _compile_CallAllocString
  | _ => _compile_CallAllocEMap
  | _ => _compile_CallAllocDMap
  | _ => _compile_CallAllocOffset
  | _ => _compile_CallDeallocQuestion
  | _ => _compile_CallDeallocResource
  | _ => packet_compile_compose
  | _ => _compile_step
  end.

Ltac _packet_encode_t :=
  progress (repeat _packet_encode_step).

Opaque EncodeAndPad. (* FIXME move *)

Example encode :
  ParametricExtraction
    #vars      p
    #program   ret (packet_encode p)
    #arguments (PacketAsCollectionOfVariables
                  (NTSome "id") (NTSome "mask") (NTSome "question")
                  (NTSome "answer") (NTSome "authority") (NTSome "additional")
                  p)
    #env       (GLabelMap.empty (FuncSpec ADTValue)).
Proof.
  start_compiling.
  packet_start_compiling.

  Start Profiling.
  Time repeat _packet_encode_t. (* 411s *)
  Show Profile.

  (* FIXME remove compile_do_use_transitivity_to_handle_head_separately? Or
       add a case with [fun _ => _] as the function for [ProgOk_Transitivity_First] *)

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "answer" ->> ` panswer as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode name") nil); admit. }


  { _packet_encode_t. }

  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode resource name") nil); admit. }

  { _packet_encode_t. }
  
  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode resource ttl") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode length of resource data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode resource data") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority name") nil); admit. }

  { _packet_encode_t. }

  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority ttl") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode length of authority data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority data") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional name") nil); admit. }

  { _packet_encode_t. }

  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                     ::[[ ` "id" ->> pid as _]]
                     ::[[ ` "mask" ->> pmask as _]]
                     ::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional ttl") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode length of additional data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Deallocate pid and mask") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Deallocate cache") nil); admit. }

  Grab Existential Variables.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  exact "AAAAAA".
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
Defined.

Eval lazy in (extract_facade encode).

(*  *)