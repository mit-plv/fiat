Require Import CertifiedExtraction.Benchmarks.MicrobenchmarksSetup.
Require Import BinEncoders.Env.Examples.Dns.
Require Import BinEncodersProperties.

Unset Implicit Arguments.

Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.
Require Import CertifiedExtraction.Extraction.External.Loops.
Require Import CertifiedExtraction.Extraction.External.FacadeLoops.

Check miniChomp.
(* FIXME Rename SameValues_remove_SCA to SameValues_remove_W *)

Ltac decide_NotInTelescope ::=  (* FIXME merge *)
  progress repeat match goal with
                  | _ => cleanup
                  | _ => congruence
                  | [  |- NotInTelescope _ Nil ] => reflexivity
                  | [  |- NotInTelescope ?k (Cons _ _ _) ] => simpl
                  | _ => auto 1  (* Added for tricky cases like CompileLoopBase2 *)
                  end.

Ltac compile_simple_inplace ::=
  match_ProgOk                (* FIXME merge this upstream (made it faster in the failing case) *)
  ltac:(fun prog pre post ext env =>
          match post with
          | Cons (NTSome ?s) (ret (?op ?a' ?b)) ?tenv' =>
            match pre with
            | context[Cons (NTSome ?s) (ret ?a) _] =>
              unify a a';
              is_word (op a b);
              let facade_op := translate_op op in
              move_to_front s;
              first [ apply (CompileBinopOrTest_right_inPlace_tel facade_op)
                    | apply (CompileBinopOrTest_right_inPlace_tel_generalized facade_op) ]
            end
          end).

Ltac decide_TelEq_instantiate_step ::= (* FIXME merge  *)
  match goal with
  | [  |- TelEq _ ?from ?to ] =>
    match constr:((from, to)) with
    | _ => rewrite DropName_Cons_Some_eq by congruence
    | _ => rewrite DropName_Cons_Some_neq by congruence
    | _ => (is_evar from || is_evar to); apply TelEq_refl
    | (Cons NTNone _ _, _) => apply TelEq_chomp_None_left; [ eexists; reflexivity | red; intros ]
    | (_, Cons NTNone _ _) => apply TelEq_chomp_None_right; [ eexists; reflexivity | red; intros ]
    | (Cons ?k _ _, ?t) => decide_TelEq_instantiate_do_swaps k t; apply TelEq_chomp_head; red; intros
    | (?t, Cons ?k _ _) => decide_TelEq_instantiate_do_swaps k t; apply TelEq_chomp_head; red; intros
    | context [DropName ?k ?tenv] => first [ is_dirty_telescope tenv; fail 1 |
                                            rewrite (DropName_NotInTelescope tenv k) by eauto ]
    | _ => apply TelEq_refl
    end
  end.

(* FIXME merge thee general lemmas about non-adts, renaming the existing versions to _W *)

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
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ [[`k <~~ v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
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
    {{ [[`k <~~ compSCA as kk]]::(tail kk)}}
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
    {{ [[`k <~~ compSCA as _]]::tail}}
      prog
    {{ tail' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  learn (SameValues_Dealloc_SCA _ _ _ _ _ _ H H1);
  SameValues_Facade_t.
Qed.

Lemma CompileCompose :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (stream: B) (cache: E)
    cacheF (tenv tenv' tenv'': Telescope av) ext env p1 p2,
    {{ [[ vstream  <--  stream as _ ]]
         :: cacheF tenv cache }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform stream (fst encoded1) as stream1 ]]
         :: cacheF tenv' (snd encoded1) }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ [[ vstream  <--  stream1 as _ ]]
          :: cacheF tenv' (snd encoded1) }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform stream1 (fst encoded2) as stream2 ]]
          :: cacheF tenv'' (snd encoded2) }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: cacheF tenv cache }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  Transformer.transform stream (fst composed) as stream ]]
         :: cacheF tenv'' (snd composed) }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  setoid_rewrite Compose_compose_acc.
  unfold compose_acc, encode_continue.
  cbv zeta in H0.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  destruct (enc1 _); simpl in *.
  destruct (enc2 _); simpl in *.
  rewrite Transformer.transform_assoc; assumption.
Qed.

Lemma CompileCompose_init :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (cache: E)
    cacheF (tenv tenv' tenv'': Telescope av) ext env p1 p2,
    {{ [[ vstream  <--  Transformer.transform_id as _ ]]
         :: cacheF tenv cache }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform Transformer.transform_id (fst encoded1) as stream1 ]]
         :: cacheF tenv' (snd encoded1) }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     {{ [[ vstream  <--  (fst encoded1) as _ ]]
          :: cacheF tenv' (snd encoded1) }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform (fst encoded1) (fst encoded2) as stream2 ]]
          :: cacheF tenv'' (snd encoded2) }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  Transformer.transform_id as _ ]]
         :: cacheF tenv cache }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  (fst composed) as stream ]]
         :: cacheF tenv'' (snd composed) }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eapply CompileCompose; cbv zeta.
  eassumption.
  setoid_rewrite Transformer.transform_id_left; eassumption.
Qed.

Lemma ProgOk_Add_snd_ret :
  forall {A B av} encodeSecond (kfst: NameTag av _) (cpair: A * B) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
    {{ [[ NTNone  <--  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: encodeSecond tenv' (snd pair) }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <--  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: encodeSecond tenv' (snd pair) }}
      p2
    {{ [[ NTNone  <--  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
    {{ [[ kfst  <--  fst cpair as p1 ]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
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

Definition PacketAsCollectionOfVariables
           {av} vid vmask vquestion vanswer vauthority vadditional (p: packet_t)
  : Telescope av :=
  [[ vid <-- ` p.(pid) as _ ]]
    :: [[ vmask <-- ` p.(pmask) as _ ]]
    :: [[ vquestion <-- ` p.(pquestion) as _ ]]
    :: [[ vanswer <-- ` p.(panswer) as _ ]]
    :: [[ vauthority <-- ` p.(pauthority) as _ ]]
    :: [[ vadditional <-- ` p.(padditional) as _ ]]
    :: Nil.

Definition DnsCacheAsCollectionOfVariables
           {av} veMap vdMap voffs (c: DnsMap.CacheT)
  : Telescope av :=
  [[ veMap <-- c.(DnsMap.eMap) as _ ]]
    :: [[ vdMap <-- c.(DnsMap.dMap) as _ ]]
    :: [[ voffs <-- c.(DnsMap.offs) as _ ]]
    :: Nil.

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
      as TelAppend_TelEq_morphism.
Proof.
  intros.
  rewrite H; clear H.
  induction y; simpl; intros.
  + assumption.
  + apply Cons_TelEq_pointwise_morphism; red; eauto.
Qed.

(* FIXME I suspect that a stronger version of this morphism holds, where the
   telescopes being appended to are only TelEq, but the proof looks painful. *)

(* Add Parametric Morphism {av} ext : (@PacketAsCollectionOfVariables av) *)
(*     with signature (eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> (TelEq ext) ==> eq ==> (TelEq ext)) *)
(*       as PacketAsCollectionOfVariables_TelEq_morphism. *)
(* Proof. *)
(*   unfold PacketAsCollectionOfVariables; intros * teq **. *)
(*   repeat (apply TelEq_chomp_head; red; intros). *)
(*   assumption. *)
(* Qed. *)

(* Add Parametric Morphism {av} ext : (@DnsCacheAsCollectionOfVariables av) *)
(*     with signature (eq ==> eq ==> eq ==> (TelEq ext) ==> eq ==> (TelEq ext)) *)
(*       as DnsCacheAsCollectionOfVariables_TelEq_morphism. *)
(* Proof. *)
(*   unfold DnsCacheAsCollectionOfVariables; intros * teq **. *)
(*   repeat (apply TelEq_chomp_head; red; intros). *)
(*   assumption. *)
(* Qed. *)

Lemma ProgOk_Transitivity_First :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v1 v2: Comp A),
    {{ [[k <~~ v1 as _]]::t1 }}       prog1      {{ [[k <~~ v2 as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k <~~ v2 as _]]::t1 }}       prog2      {{ [[k <~~ v2 as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[k <~~ v1 as _]]::t1 }}  Seq prog1 prog2 {{ [[k <~~ v2 as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  eauto using CompileSeq.
Qed.

Lemma CompileCallWrite16:
  forall {av} {W: FacadeWrapper av (list bool)}
    (vtmp varg vstream : string) (stream : list bool) (tenv tenv': Telescope av)
    (n : N) ext env
    pArg pNext fWrite16,
    {{ [[ ` vstream <-- stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream <-- stream as _]]::[[ ` varg <-- Word.NToWord n as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream <-- stream ++ EncodeAndPad n 16 as _]]::tenv }}
      pNext
    {{ [[ ` vstream <-- stream ++ EncodeAndPad n 16 as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream <-- stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite16 [vstream; varg]) pNext)
    {{ [[ ` vstream <-- stream ++ EncodeAndPad n 16 as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare.
  hoare.
  hoare.
Admitted.

Ltac _compile_callWrite16 :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let post' := eval simpl in post in
            match post' with
            | [[ _ <-- _ ++ ?arg as _]] :: _ =>
              let vtmp := gensym "tmp" in
              let varg := gensym "arg" in
              (* try match arg with ` ?arg => rewrite (EncodeAndPad_ListAsWord arg) end; *)
              eapply (CompileCallWrite16 vtmp varg)
            end).

Ltac instantiate_tail_of_post term :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:post with
            | context[?x] =>
              is_evar x;
              match type of x with
              | @Telescope _ => unify x term
              end
            end).

Ltac find_packet :=
  lazymatch goal with
  (* Use an explicit match, since match_ProgOk returns tactics, not terms *)
  | [  |- {{ ?pre }} _ {{ _ }} ∪ {{ _ }} // _ ] =>
    match pre with
    | context[@PacketAsCollectionOfVariables ?av ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7] =>
      constr:(@PacketAsCollectionOfVariables av x0 x1 x2 x3 x4 x5 x6 x7)
    end
  end.

Ltac keep_unmodified_packet :=
  instantiate_tail_of_post find_packet.

Ltac compile_compose :=
  (eapply CompileCompose || eapply CompileCompose_init); intros.

Ltac packet_start_compiling :=
  repeat match goal with
         | [ p: packet_t |- _ ] => destruct p
         | _ => progress unfold packet_encode, encode_packet; simpl
         end.

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
    {{ [[ ` vstream <-- @nil bool as _]]::tenv }}
      pNext
    {{ [[ ` vstream <-- @nil bool as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocString [vstream]) pNext
    {{ [[ ` vstream <-- @nil bool as _]]::tenv' }} ∪ {{ ext }} // env.
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
Instance WrapPacket : FacadeWrapper ADTValue (packet_t). Admitted.

Lemma CompileCallAllocEMap:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap <-- DnsMap.EMap.empty DnsMap.position_t as _]]::tenv }}
      pNext
    {{ [[ ` veMap <-- DnsMap.EMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap <-- DnsMap.EMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallAllocDMap:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap <-- DnsMap.DMap.empty (list DnsMap.word_t) as _]]::tenv }}
      pNext
    {{ [[ ` veMap <-- DnsMap.DMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap <-- DnsMap.DMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallAllocOffset:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap <-- 0%N as _]]::tenv }}
      pNext
    {{ [[ ` veMap <-- 0%N as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap <-- 0%N as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallListResourceLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : list resource_t)
    flength tenv',
    TelEq ext tenv ([[`vlst <-- lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg flength [vlst]
    {{ [[ ` varg <-- Word.natToWord 32 (Datatypes.length lst) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Lemma CompileCallListQuestionLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : list question_t)
    flength tenv',
    TelEq ext tenv ([[`vlst <-- lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg flength [vlst]
    {{ [[ ` varg <-- Word.natToWord 32 (Datatypes.length lst) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac _packet_encode_FixInt :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | [[ret (FixInt.FixInt_encode _ _) as _]] :: _ =>
              rewrite FixInt_encode_is_copy;
              setoid_rewrite Propagate_anonymous_ret; simpl;
              apply ProgOk_Transitivity_First
            end).

Ltac _compile_CallListLength :=
  match_ProgOk
    ltac:(fun _ _ post _ _ =>
            match post with
            | [[ _ <-- Word.natToWord 32 (Datatypes.length ?lst) as _]] :: _ =>
              (* FIXME this should be an equivalent of find_in_ext *)
              (* FIXME this shoud be more principled *)
              unfold PacketAsCollectionOfVariables; simpl;
              match_ProgOk
                ltac:(fun _ pre _ _ _ =>
                        match pre with
                        | context[Cons (NTSome ?k) (ret lst) _] =>
                          (eapply (CompileCallListResourceLength k) ||
                           eapply (CompileCallListQuestionLength k));
                          [ unfold DnsCacheAsCollectionOfVariables; (* FIXME autounfold *)
                            decide_TelEq_instantiate ]
                        end)
            end).

Ltac may_alloc_head :=
  (* Fail if pre-condition contains identifier in head of post-condition. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons ?k _ _ =>
              match pre with
              | context[Cons k _ _] => fail 1
              | _ => idtac
              end
            end).

Ltac _compile_CallAllocString :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocString vtmp).

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
    (forall head (acc: A) (s: list B),
        {{ [[`vhead <-- head as _]] :: tenvF tenv acc }}
          facadeBody
        {{ [[ ret (f acc head) as facc ]] :: tenvF tenv facc }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenvF tenv init }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ tenvF tenv (fold_left f lst init) }} ∪ {{ ext }} // env.
Proof.
  Transparent DummyArgument.
  unfold DummyArgument; loop_t.

  instantiate (1 := [[`vlst <-- lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                              | nil => true
                                                              | _ :: _ => false
                                                              end) as _]]
                                         :: tenvF tenv init); admit.
  (* eapply (CompileTupleList_Empty_alt (N := N)); loop_t. *)

  2:instantiate (1 := [[ ` vlst <-- nil as _]] :: tenvF tenv (fold_left f lst init)); admit.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.

  simpl.
  eapply CompileWhileTrue; [ loop_t.. | ].

  instantiate (1 := [[ `vhead <-- a as _ ]] :: [[ `vlst <-- lst as _ ]] :: [[ ` vtest <-- W0 as _]] :: tenvF tenv init); admit.

  (* rewrite <- GLabelMapFacts.find_mapsto_iff; assumption. *)

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; solve [eauto].

  move_to_front vtest.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.

  instantiate (1 := [[ ` vlst <-- lst as ls]]
                     :: [[`vtest <-- (bool2w match ls with
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
    vhead vtest vlst tenvF tenv'
    (lst: list B) init (f: A -> B -> A) tenv0 tenv
    env (ext: StringMap.t (Value QsADTs.ADTValue))
    fpop fempty fdealloc facadeBody facadeConclude,
    (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst]]] ->
    TelEq ext tenv0 ([[`vlst <-- lst as _]] :: tenvF tenv init) ->
    (forall v, NotInTelescope vtest (tenvF tenv v)) ->
    {{ tenvF tenv (fold_left f lst init) }}
      facadeConclude
    {{ tenvF tenv' (fold_left f lst init) }}
    ∪ {{ ext }} // env ->
    (forall head (acc: A) (s: list B),
        {{ [[`vhead <-- head as _]] :: tenvF tenv acc }}
          facadeBody
        {{ [[ ret (f acc head) as facc ]] :: tenvF tenv facc }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ tenv0 }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[ ret (fold_left f lst init) as folded ]] :: tenvF tenv' folded }} ∪ {{ ext }} // env.
Proof.
  intros.
  rewrite H2.
  setoid_rewrite Propagate_anonymous_ret.
  hoare.
  eapply @CompileLoopBase__many; eassumption.
Qed.

Inductive EvarTag {T A} (a: A) (t: T) := __EvarTag.

Ltac _packet_encode__clear_EvarTags :=
  repeat match goal with
         | [ H: EvarTag ?v ?tag |- _ ] => try unify v tag; clear H
         end.

Ltac specialize_function_with_evar f tag :=
  lazymatch type of f with
  | ?A -> _ => let a := fresh in
             let old_f := fresh "old" in
             evar (a: A);
             rename f into old_f;
             pose (old_f a) as f;
             lazymatch constr:tag with
             | Some ?t => pose proof (__EvarTag a t)
             | _ => idtac
             end;
             unfold old_f, a in *;
             clear old_f; clear a
  end.

Ltac specialize_function_with_evars f :=
  repeat (specialize_function_with_evar f None).

Ltac create_packet_evar name :=
  pose @Build_packet_t as name;
  specialize_function_with_evars name.

Ltac _packet_encode_IList__rewrite_as_fold :=
  lazymatch goal with         (* FIXME make this an autorewrite *)
  | [  |- appcontext[IList.IList_encode' ?cache] ] =>
    rewrite IList.IList_encode'_as_foldl;
    rewrite (IList_post_transform_TelEq cache) by reflexivity
  end.

Ltac specialize_body hyp term :=
  let new := fresh in
  pose (hyp term) as fresh;
  unfold hyp in *;
  clear hyp;
  rename fresh into hyp.

Ltac _packet__havoc_packet_in_postcondition :=
  let p := find_packet in
  let p' := fresh in
  lazymatch constr:p with
  | @PacketAsCollectionOfVariables ?av ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?tail ?p =>
    let tail' := fresh in
    create_packet_evar p';
    pose (@PacketAsCollectionOfVariables av) as tail';
    (* FIXME generalize this *)
    specialize_function_with_evar tail' (Some x0);
    specialize_function_with_evar tail' (Some x1);
    specialize_function_with_evar tail' (Some x2);
    specialize_function_with_evar tail' (Some x3);
    specialize_function_with_evar tail' (Some x4);
    specialize_function_with_evar tail' (Some x5);
    specialize_body tail' tail;
    specialize_body tail' p';
    instantiate_tail_of_post tail';
    unfold p', tail' in *; clear p'; clear tail'
  end.

Ltac delete_tagged_var_from_post var :=
  (* Delete VAR from post-condition.
     Since VAR doesn't appear litteraly in the post-condition, use an EvarTag
     to find which evar to remove in the post instead. *)
  lazymatch goal with
  | [ H: EvarTag ?k (@NTSome ?av ?T var ?wrp) |- _ ] =>
    let kk := fresh in
    set (kk := k); (* Otherwise the match below fails *)
    lazymatch goal with
    | [  |- context[Cons (@NTSome av T var wrp) (ret ?old_val) _] ] =>
      lazymatch goal with
      | [  |- context[Cons kk ?new_val ?tenv] ] =>
        unify k (@NTNone av T); unfold kk; clear kk;
        unify (ret old_val) new_val;
        setoid_rewrite (@Propagate_anonymous_ret _ _ tenv _ old_val)
      end
    end
  end.

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

Ltac _compile_Loop2 vlst :=
  match_ProgOk (* FIXME replace this with a lemma specialized to 3 cache variables? *)
    ltac:(fun prog pre post ext env =>
            let tenvF_tl := split_tail_of_telescope post in
            match tenvF_tl with
            | (?tenvF, ?tl) =>
              let vhead := gensym "head" in
              let vtest := gensym "test" in
              eapply (CompileLoop__many vhead vtest vlst tenvF tl);
              [ | unfold DnsCacheAsCollectionOfVariables; simpl; decide_TelEq_instantiate | idtac.. ]
            end).

Ltac _packet_encode_IList__compile_loop :=
  unfold PacketAsCollectionOfVariables; simpl;
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | appcontext[fold_left (IList.IList_encode'_body _ _ _) ?lst] =>
              match pre with
              | context[Cons (NTSome ?vlst) (ret lst) _] =>
                delete_tagged_var_from_post vlst;
                _packet_encode__clear_EvarTags;
                _compile_Loop2 vlst
              end
            end).

Ltac _packet_encode_IList_compile :=
  _packet_encode_IList__rewrite_as_fold;
  _packet__havoc_packet_in_postcondition;
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

Create HintDb packet_autorewrite_db.
Hint Rewrite -> @NToWord_of_nat : packet_autorewrite_db.
Hint Rewrite -> @NToWord_WordToN : packet_autorewrite_db.
Hint Rewrite -> @length_of_fixed_length_list : packet_autorewrite_db.
Hint Rewrite -> @FixInt_encode_is_copy : packet_autorewrite_db.
Hint Rewrite -> @IList_encode_bools_is_copy : packet_autorewrite_db.
Hint Rewrite -> @FixList_is_IList : packet_autorewrite_db.
Hint Unfold IList.IList_encode : packet_autorewrite_db.
Hint Unfold FixList.FixList_encode : packet_autorewrite_db.

Opaque Transformer.transform_id.

Ltac _packet_encode_cleanup :=
  match goal with
  | _ => match_ProgOk
          ltac:(fun prog pre post ext env =>
                  match post with
                  | [[ ret (_, _) as _]] :: _ =>
                    apply Propagate_anonymous_ret__fast
                  end)
  | [  |- context[fst (?a, ?b)] ] => change (fst (a, b)) with a
  | [  |- context[snd (?a, ?b)] ] => change (snd (a, b)) with b
  | _ => progress autounfold with packet_autorewrite_db
  | _ => progress autorewrite with packet_autorewrite_db
  end.

(*  Disable the propagation of rets for this file, since we use them for structure *)
Ltac _compile_rewrite_bind ::= fail.
(*  Disable automatic decompilation for this file (it only orks for simple examples with no evars in the post) *)
Ltac _compile_destructor ::= fail.

Ltac _packet_encode_step :=
  match goal with
  | _ => _packet_encode_cleanup
  | _ => _packet_encode_FixInt
  | _ => _packet_encode_IList_compile
  | _ => _compile_callWrite16
  | _ => _compile_CallListLength
  | _ => _compile_CallAllocString
  | _ => _compile_CallAllocEMap
  | _ => _compile_CallAllocDMap
  | _ => _compile_CallAllocOffset
  | _ => _compile_step
  end.

Ltac _packet_encode_t :=
  repeat _packet_encode_step.

Lemma CompileCompose' :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (stream: B) (cache: E)
    (tenv: Telescope av) tenv' tenv'' ext env p1 p2,
    (forall a1 a2 b, tenv'' (a1, b) = tenv'' (a2, b)) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform stream (fst encoded1) as stream1 ]]
         :: tenv' encoded1 }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ [[ vstream  <--  stream1 as _ ]]
          :: tenv' encoded1 }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform stream1 (fst encoded2) as stream2 ]]
          :: tenv'' encoded2 }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  Transformer.transform stream (fst composed) as stream ]]
         :: tenv'' composed }} ∪ {{ ext }} // env.
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

Lemma CompileCompose'' :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (stream: B) (cache: E)
    (tenv: Telescope av) tenv' ext env p1 p2,
    (forall a1 a2 b, tenv' (a1, b) = tenv' (a2, b)) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform stream (fst encoded1) as stream1 ]]
         :: tenv' encoded1 }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ [[ vstream  <--  stream1 as _ ]]
          :: tenv' encoded1 }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform stream1 (fst encoded2) as stream2 ]]
          :: tenv' encoded2 }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  Transformer.transform stream (fst composed) as stream ]]
         :: tenv' composed }} ∪ {{ ext }} // env.
Proof.
  intros; eapply CompileCompose'; try eassumption.
Qed.

Lemma CompileCompose'_init :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (cache: E)
    tenv tenv' tenv'' ext env p1 p2,
    (forall (a1 a2 : B) (b : E), tenv'' (a1, b) = tenv'' (a2, b)) ->
    {{ [[ vstream  <--  Transformer.transform_id as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform Transformer.transform_id (fst encoded1) as stream1 ]]
         :: tenv' encoded1 }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     {{ [[ vstream  <--  (fst encoded1) as _ ]]
          :: tenv' encoded1 }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform (fst encoded1) (fst encoded2) as stream2 ]]
          :: tenv'' encoded2 }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  Transformer.transform_id as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  (fst composed) as _ ]]
         :: tenv'' composed }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eapply CompileCompose'; eauto.
  cbv zeta in *. setoid_rewrite Transformer.transform_id_left. eassumption.
Qed.


Lemma ProgOk_Add_snd_ret' :
  forall {A B av} (f: B -> Telescope av) (kfst: NameTag av _) (cpair: A * B) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
    {{ [[ NTNone  <--  cpair as pair ]]
         :: TelAppend ([[ kfst  <--  fst pair as p1 ]] :: f (snd pair)) tenv' }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <--  cpair as pair ]]
         :: TelAppend ([[ kfst  <--  fst pair as p1 ]] :: f (snd pair)) tenv' }}
      p2
    {{ [[ NTNone  <--  cpair as pair ]]
         :: TelAppend ([[ kfst  <--  fst pair as p1 ]] :: Nil) tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
    {{ [[ kfst  <--  fst cpair as p1 ]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
Qed.


Lemma CompileCompose2 :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (stream: B) (cache: E)
    (tenv t1 t2: Telescope av) f ext env p1 p2,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: TelAppend ([[ vstream  <--  Transformer.transform stream (fst encoded1) as _ ]]
                        :: f encoded1) t1 }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ TelAppend ([[ vstream  <--  stream1 as _ ]] :: f encoded1) t1 }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: TelAppend ([[ vstream  <--  Transformer.transform stream1 (fst encoded2) as _ ]]
                         :: f encoded2) t2 }}
     ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: TelAppend ([[ vstream  <--  Transformer.transform stream (fst composed) as _ ]]
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

Lemma CompileCompose3 :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (stream: B) (cache: E)
    (tenv t1 t2: Telescope av) f ext env p1 p2,
    (forall a1 a2 b, f (a1, b) = f (a2, b)) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform stream (fst encoded1) as _ ]]
         :: TelAppend (f encoded1) t1 }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ [[ vstream  <--  stream1 as _ ]] :: TelAppend (f encoded1) t1 }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform stream1 (fst encoded2) as _ ]]
          :: TelAppend (f encoded2) t2 }}
     ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  Transformer.transform stream (fst composed) as _ ]]
         :: TelAppend (f composed) t2 }}
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
  Opaque TelAppend.

  start_compiling.
  packet_start_compiling.

Lemma ProgOk_Add_snd_ret'' :
  forall {A B av} (f: B -> Telescope av) (kfst: NameTag av _) (cpair: A * B) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
    {{ [[ NTNone  <--  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: TelAppend (f (snd pair)) tenv' }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <--  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: TelAppend (f (snd pair)) tenv' }}
      p2
    {{ [[ NTNone  <--  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: TelAppend (Nil) tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
    {{ [[ kfst  <--  fst cpair as p1 ]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
Qed.

  apply (ProgOk_Add_snd_ret'' (DnsCacheAsCollectionOfVariables (NTSome "eMap") (NTSome "dMap") (NTSome "offs"))).

  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eapply CompileSeq; [ | eapply CompileCompose3 ].

  Focus.
  _packet_encode_t.
  Unfocused.

  Focus.
  _packet_encode_t.
  Unfocused.

  Focus.
  _packet_encode_t.
  instantiate (1 := Assign "arg" (Var "pid")); admit.
  Transparent TelAppend. simpl.
  _packet_encode_t.
  Ltac keep_pre :=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match post with
              | context[?x] => is_evar x; (unify x pre)
              end).
  keep_pre.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment counter in cache") nil); admit.
  Unfocused.

  intros.

  repeat (eapply CompileCompose3; intros; try reflexivity).

  Ltac tsimpl :=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              let pre' := eval simpl in pre in
                  change pre with pre').

  Focus.
  tsimpl.
  _packet_encode_t.
  instantiate (1 := Assign "arg" (Var "mask")); admit.
  Ltac mod_first :=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons _ _ (fun _ => ?tail), Cons _ _ (fun _ => ?f)) => is_evar f; (unify f tail)
              end).
  mod_first.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment counter in cache") nil); admit.
  Unfocused.

  Focus.
  tsimpl.
  _packet_encode_t.
  mod_first.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment counter in cache") nil); admit.
  Unfocused.

  Focus.
  tsimpl.
  _packet_encode_t.
  mod_first.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment cache counter") nil); admit.
  Unfocused.

  Focus.
  tsimpl.
  _packet_encode_t.
  mod_first.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment cache counter") nil); admit.
  Unfocused.

  Focus.
  tsimpl.
  _packet_encode_t.
  mod_first.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment cache counter") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  _packet_encode_IList__rewrite_as_fold.
  unfold DnsCacheAsCollectionOfVariables; simpl (TelAppend _ _).
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let tenvF_tl := split_tail_of_telescope post in
            match tenvF_tl with
            | (?tenvF, ?tl) =>
              let vhead := gensym "head" in
              let vtest := gensym "test" in
              eapply (CompileLoop__many vhead vtest "question" tenvF tl)
            end).

  2:unfold PacketAsCollectionOfVariables; simpl; decide_TelEq_instantiate.

  _packet_encode_t.
  _packet_encode_t.
  _packet_encode_t.

  Lemma IList_encode'_body_as_compose :
    forall {A HD bin : Type}
      (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
      (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
      (xs : list A) (base : bin) (env : Cache.CacheEncode) acc (head: HD) f,
      (IList.IList_encode'_body cache transformer f acc head) = (* Cache parameter isn't used *)
      Compose.compose transformer (fun c => (fst acc, c)) (f head) (snd acc).
  Proof.
    intros; unfold IList.IList_encode'_body, Compose.compose; simpl.
    destruct acc; simpl; destruct (f _ _); reflexivity.
  Qed.

  _packet_encode_t.
  unfold IList.IList_encode'_body; destruct acc.

  simpl (fst (_, _)).
  simpl (snd (_, _)).

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

  rewrite let_ret2.

  move_to_front "out".
  Opaque Transformer.transform.
  simpl.
  Transparent Transformer.transform.

Lemma CompileExtendLifetime':
  forall {av A} {env ext} (k: NameTag av A) comp tenv tenv' prog dealloc,
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      prog
    {{ [[k <~~ comp as _]] :: tenv' }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as _]] :: tenv' }}
      dealloc
    {{ [[comp as _]] :: tenv' }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      (Seq prog dealloc)
    {{ tenv' }} ∪ {{ext}} // env.
Proof.
  SameValues_Facade_t.
Qed.

  (* move_to_front "head". *)
  (* apply CompileExtendLifetime'. *)
(* _packet_encode_t. *)

change ( [[ret (encode_question head c) as xy]]
      ::[[ ` "out" <-- Transformer.transform l (fst xy) as _]]
        ::[[ ` "eMap" <-- DnsMap.eMap (snd xy) as _]]
          ::[[ ` "dMap" <-- DnsMap.dMap (snd xy) as _]]
            ::[[ ` "offs" <-- DnsMap.offs (snd xy) as _]]
            ::[[ ` "id" <-- ` pid as _]]
                ::[[ ` "mask" <-- ` pmask as _]]
                  ::[[ ` "answer" <-- ` panswer as _]]
                  ::[[ ` "authority" <-- ` pauthority as _]]::[[ ` "additional" <-- ` padditional as _]]::Nil)
               with ([[ret (encode_question head c) as xy]]
                       ::[[ ` "out" <-- Transformer.transform l (fst xy) as _]]
                       :: (TelAppend ([[ ` "eMap" <-- DnsMap.eMap (snd xy) as _]]
                                       ::[[ ` "dMap" <-- DnsMap.dMap (snd xy) as _]]
                                       ::[[ ` "offs" <-- DnsMap.offs (snd xy) as _]]::Nil)
                                    ([[ ` "id" <-- ` pid as _]]
                                       ::[[ ` "mask" <-- ` pmask as _]]
                                       ::[[ ` "answer" <-- ` panswer as _]]
                                       ::[[ ` "authority" <-- ` pauthority as _]]
                                       ::[[ ` "additional" <-- ` padditional as _]]::Nil))).

repeat (eapply CompileCompose3; intros; try reflexivity); simpl (TelAppend _ _).

  unfold SteppingCacheList.SteppingList_encode.
  instantiate (1 := [[ ` "head" <-- head as _]]
                     ::[[ ` "id" <-- ` pid as _]]
                     ::[[ ` "mask" <-- ` pmask as _]]
                     ::[[ ` "answer" <-- ` panswer as _]]
                     ::[[ ` "authority" <-- ` pauthority as _]]
                     ::[[ ` "additional" <-- ` padditional as _]]::Nil).
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode name") nil); admit.

  _packet_encode_t.
  repeat lazymatch goal with
         | [  |- context[Transformer.transform _ nil] ] => setoid_rewrite @Transformer.transform_id_right
         end.
  apply CompileSkip.

  Stmt
  
  _packet_encode_t.
  change ([[ ` "eMap" <-- DnsMap.eMap (snd encoded8) as _]]
      ::[[ ` "dMap" <-- DnsMap.dMap (snd encoded8) as _]]
        ::[[ ` "offs" <-- DnsMap.offs (snd encoded8) as _]]
          ::[[ ` "id" <-- ` pid as _]]
            ::[[ ` "mask" <-- ` pmask as _]]
              ::[[ ` "answer" <-- ` panswer as _]]
              ::[[ ` "authority" <-- ` pauthority as _]]::[[ ` "additional" <-- ` padditional as _]]::Nil)
         with ((fun encoded8 => [[ ` "eMap" <-- DnsMap.eMap (snd encoded8) as _]]
      ::[[ ` "dMap" <-- DnsMap.dMap (snd encoded8) as _]]
        ::[[ ` "offs" <-- DnsMap.offs (snd encoded8) as _]]
          ::[[ ` "id" <-- ` pid as _]]
            ::[[ ` "mask" <-- ` pmask as _]]
              ::[[ ` "answer" <-- ` panswer as _]]
              ::[[ ` "authority" <-- ` pauthority as _]]::[[ ` "additional" <-- ` padditional as _]]::Nil) encoded8).
  apply CompileSkip.

  Focus 5.
  cbv beta.
  
  reflexivity.

  reflexivity.
  reflexivity.
  
    
  erewrite IList_encode'_body_as_compose.
  destruct acc; _packet_encode_t.

  
  (* rewrite Compose_compose_acc. *)
  (* unfold compose_acc, encode_continue. *)
  unfold Compose.compose.
  Lemma IList_encode'_body_with_compose :
    forall {A HD bin : Type}
      (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
      subtransformer encode1 encode2
      (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
      (xs : list A) (base : bin) (env : Cache.CacheEncode) acc (head: HD),
      Some (IList.IList_encode'_body
         cache transformer
         (fun x => @Compose.compose _ _ subtransformer (encode1 x) encode2)
         acc head) = encode_continue transformer (fun x => @Compose.compose _ _ subtransformer (encode1 x) encode2) acc.
  Proof.
    intros; unfold IList.IList_encode'_body, Compose.compose.
    destruct acc as (prev_stream & prev_cache) eqn:?.
    destruct (encode1 _ _) as (new_stream1 & new_cache1) eqn:?.
    destruct (encode2 _) as (new_stream2 & new_cache2) eqn:?.
    
    
    unfold .
 as (? & [? ? ?]). _packet_encode_t.
  simpl. destruct head; simpl.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode question") nil); admit.
  Unfocused.

  (* Note: One could also never unfold PacketAsCollectionOfVariables and
     DnsCacheAsCollectionOfVariables (and instead find the variable to loop on
     by copying the precondition into the context and unfolding locally. *)

  Focus.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode answer") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional") nil); admit.
  Unfocused.

  repeat lazymatch goal with
         | [  |- context[Transformer.transform nil _] ] => setoid_rewrite @Transformer.transform_id_left
         | [  |- context[Transformer.transform _ nil] ] => setoid_rewrite @Transformer.transform_id_right
         end.

  _packet_encode_t.
  unfold PacketAsCollectionOfVariables; simpl.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Deallocate packet") nil); admit.

  _packet_encode_t.
  unfold DnsCacheAsCollectionOfVariables, PacketAsCollectionOfVariables; simpl.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Deallocate cache") nil); admit.

  Grab Existential Variables.
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

Example encode :
  ParametricExtraction
    #vars      p
    #program   ret (packet_encode p)
    #arguments [[`"p" <-- (proj1_sig (pid p)) as _ ]] :: Nil
    #env       (GLabelMap.empty (FuncSpec ADTValue)).
Proof.
  assert (FacadeWrapper (Value ADTValue) DnsMap.CacheT) by admit.

  _compile.
  unfold packet_encode, encode_packet.
  unfold Compose.compose, Transformer.transform, Core.btransformer.

  rewrite (push_function_into_destructuring_let2 fst).
  unfold IList.IList_encode; rewrite IList.IList_encode'_as_foldl.

  set (` (pid p)).
  set ((IList.IList_encode'_body DnsMap.cache
              {|
              Transformer.transform := app (A:=bool);
              Transformer.transform_id := nil;
              Transformer.transform_id_left := app_nil_l (A:=bool);
              Transformer.transform_id_right := app_nil_r (A:=bool);
              Transformer.transform_assoc := app_assoc (A:=bool) |} Bool.Bool_encode)).
  lazymatch goal with
  | [  |- context C[let (a1, a2) := ?x in (@?f a1 a2)] ] =>
    let ff := fresh in
    pose f as ff;
      let ctx_new := context C[let (a1, a2) := x in (ff a1 a2)] in
      change ctx_new
  end.

  eapply CompileDestructuringLet2_ret with (k1 := NTSome "fst") (k2 := NTSome "snd").
  eapply (CompileLoop2_Alloc "vhead" "vtest"); [ compile_do_side_conditions | .. ].

  simpl.
  instantiate (1 := Call (DummyArgument "tmp") ("Initialization", "code") nil); admit.
  Focus 2.

  (* Loop body *)
  intros; unfold p0, IList.IList_encode'_body.
  rewrite (push_function_into_destructuring_let2 fst), (push_function_into_destructuring_let2 snd); simpl.

  setoid_rewrite (TelEq_swap (NTSome "snd")).
  eapply CompileAppendBool.
  _compile.
  apply CompileExtendLifetime'.
  _compile.
  instantiate (1 := (Call "ignore" ("DNS", "UpdateCache") (cons "snd" nil))); admit.

  _compile.

  eapply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  _compile.

  unfold H.
  setoid_rewrite (push_function_into_destructuring_let2 fst _ _); unfold fst.

  



  eapply (@CompileDeallocSCA_discretely _ ([[ ` "snd" <--
        {| DnsMap.eMap := DnsMap.eMap acc2; DnsMap.dMap := DnsMap.dMap acc2; DnsMap.offs := DnsMap.offs acc2 + 1 |}
        as _]]::Nil) ([[ ` "snd" <--
      {| DnsMap.eMap := DnsMap.eMap acc2; DnsMap.dMap := DnsMap.dMap acc2; DnsMap.offs := DnsMap.offs acc2 + 1 |}
      as _]]::Nil) (["fst" <-- wrap (acc1 ++ (cons vv nil))]::["vtest" <-- wrap W0]::["p" <-- wrap s]::∅) (GLabelMap.empty (FuncSpec ADTValue)) "vhead").


  eapply CompileExtendLifetime.
  compile_do_use_transitivity_to_handle_head_separately.

Example decode :
  ParametricExtraction
    #vars      p
    #program   ret (packet_decode p)
    #arguments [[`"p" <-- p as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
  unfold packet_decode, packet_decoder', IList.IList_decode.

  (* Goal { f | forall p, f p = packet_decode p }. *)
  (* Proof. *)
  (*   eexists; intros. *)
  (*   unfold packet_decode, packet_decoder', IList.IList_decode. *)

  (*   setoid_replace IList.IList_decode' with IList.IList_decode_hack. *)
  (*   Axiom aa: IList.IList_decode_hack = IList.IList_decode'. *)
  (*   setoid_rewrite <- aa. *)
  (*   setoid_rewrite (IList.IList_decode'_as_fold DnsMap.cache (Bool.Bool_decode DnsMap.cacheAddN) 16 p empty). *)

  rewrite (push_function_into_destructuring_let2 fst).
  rewrite (push_function_into_destructuring_let2 fst).
  (* setoid_rewrite (push_function_into_destructuring_let2 fst _ _). *)

  lazymatch goal with
  | [  |- context C[let (a1, a2) := ?x in fst (@?f a1 a2)] ] =>
    let ff := fresh in
    pose f as ff;
      let ctx_new := context C[let (a1, a2) := x in fst (ff a1 a2)] in
      change ctx_new
  end.

  eapply CompileDestructuringLet23'_ret.
  unfold IList.IList_decode, fst, snd.

  pose proof (IList.IList_decode'_as_fold DnsMap.cache (Bool.Bool_decode DnsMap.cacheAddN) 16 p empty).
  rewrite H0.
  setoid_replace (IList.IList_decode' DnsMap.cache (Bool.Bool_decode DnsMap.cacheAddN) 16 p empty)
  with (IList.DoTimes 16 (IList.IList_decode'_body DnsMap.cache (Bool.Bool_decode DnsMap.cacheAddN))
                      (nil, p, empty)).
