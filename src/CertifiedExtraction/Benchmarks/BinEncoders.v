Require Import CertifiedExtraction.Benchmarks.MicrobenchmarksSetup.
Require Import BinEncoders.Env.Examples.Dns.

Unset Implicit Arguments.

Lemma push_function_into_destructuring_let2 {A1 A2 B C} :
  forall (f: B -> C) (p: A1 * A2) (g : A1 -> A2 -> B),
    f (match p with (a1, a2) => g a1 a2 end) =
    match p with (a1, a2) => f (g a1 a2) end.
Proof.
  destruct p; reflexivity.
Qed.

Lemma push_function_into_destructuring_let3 {A1 A2 A3 B C} :
  forall (f: B -> C) (p: A1 * A2 * A3) (g : A1 -> A2 -> A3 -> B),
    f (match p with (a1, a2, a3) => g a1 a2 a3 end) =
    match p with (a1, a2, a3) => f (g a1 a2 a3) end.
Proof.
  repeat destruct p; reflexivity.
Qed.

Lemma CompileDestructuringLet2 {A1 A2 B av: Type} :
  forall tenv1 tenv2 (k: NameTag av B) k1 k2 (pair: A1 * A2) ext env (g: A1 -> A2 -> Comp B) prog cleanup,
    {{ tenv1 }}
      prog
    {{ [[k1 <-- fst pair as a1]]::[[k2 <-- snd pair as a2]]::[[k <~~ g a1 a2 as v]] :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ [[k1 <-- fst pair as a1]]::[[k2 <-- snd pair as a2]]::[[k <~~ g a1 a2 as v]] :: tenv2 v }}
      cleanup
    {{ [[k <~~ g (fst pair) (snd pair) as v]] :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ tenv1 }}
      Seq prog cleanup
    {{ [[k <~~ let (a1, a2) := pair in g a1 a2 as v]] :: tenv2 v }} ∪ {{ ext }} // env.
Proof.
  destruct pair; simpl; SameValues_Facade_t.
Qed.

Lemma CompileDestructuringLet2_ret {A1 A2 B av: Type} :
  forall tenv1 tenv2 (k: NameTag av B) k1 k2 (pair: A1 * A2) ext env (g: A1 -> A2 -> B) prog cleanup,
    {{ tenv1 }}
      prog
    {{ [[k1 <-- fst pair as a1]]::[[k2 <-- snd pair as a2]]::[[k <-- g a1 a2 as v]] :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ [[k1 <-- fst pair as a1]]::[[k2 <-- snd pair as a2]]::[[k <-- g a1 a2 as v]] :: tenv2 v }}
      cleanup
    {{ [[k <-- g (fst pair) (snd pair) as v]] :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ tenv1 }}
      Seq prog cleanup
    {{ [[k <-- let (a1, a2) := pair in g a1 a2 as v]] :: tenv2 v }} ∪ {{ ext }} // env.
Proof.
  destruct pair; simpl; SameValues_Facade_t.
Qed.

Lemma CompileDestructuringLet23_ret {A11 A12 A2 B av: Type} :
  forall tenv1 tenv2 (k: NameTag av B) k11 k12 k2 (pair: A11 * A12 * A2) ext env (g: A11 * A12 -> A2 -> B) prog cleanup,
    {{ tenv1 }}
      prog
    {{ [[k11 <-- fst (fst pair) as a11]]
         ::[[k12 <-- snd (fst pair) as a12]]
         ::[[k2 <-- snd pair as a2]]
         ::[[k <-- g (a11, a12) a2 as v]]
         :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ [[k11 <-- fst (fst pair) as a11]]
         ::[[k12 <-- snd (fst pair) as a12]]
         ::[[k2 <-- snd pair as a2]]
         ::[[k <-- g (a11, a12) a2 as v]]
         :: tenv2 v }}
      cleanup
    {{ [[k <-- g (fst pair) (snd pair) as v]] :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ tenv1 }}
      Seq prog cleanup
    {{ [[k <-- let (a1, a2) := pair in g a1 a2 as v]] :: tenv2 v }} ∪ {{ ext }} // env.
Proof.
  destruct pair; simpl; SameValues_Facade_t.
Qed.

Lemma CompileDestructuringLet23'_ret {A11 A12 A2 B av: Type} :
  forall tenv1 tenv2 (k: NameTag av B) k12 k2 (pair: A11 * A12 * A2) ext env (g: A11 * A12 -> A2 -> B) prog cleanup,
    {{ tenv1 }}
      prog
    {{ [[k12 <-- snd (fst pair) as a12]]
         ::[[k2 <-- snd pair as a2]]
         ::[[k <-- g (fst (fst pair), a12) a2 as v]]
         :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ [[k12 <-- snd (fst pair) as a12]]
         ::[[k2 <-- snd pair as a2]]
         ::[[k <-- g (fst (fst pair), a12) a2 as v]]
         :: tenv2 v }}
      cleanup
    {{ [[k <-- g (fst pair) (snd pair) as v]] :: tenv2 v }} ∪ {{ ext }} // env ->
    {{ tenv1 }}
      Seq prog cleanup
    {{ [[k <-- let (a1, a2) := pair in g a1 a2 as v]] :: tenv2 v }} ∪ {{ ext }} // env.
Proof.
  destruct pair; simpl; SameValues_Facade_t.
Qed.

(* Remove Printing Let prod. *)

Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.
Require Import CertifiedExtraction.Extraction.External.Loops.
Require Import CertifiedExtraction.Extraction.External.FacadeLoops.
Require Import CallRules.TupleList.

Check miniChomp.

Lemma miniChomp_0:
  forall {A av} (k k': NameTag av _) (v: Comp A) tenv tenv' ext prog env,
    (forall vv: A, v ↝ vv ->
           {{ [[k  <--  vv as vv]] :: tenv vv }} prog {{ [[k' <--  vv as vv]] :: tenv' vv }} ∪ {{ ext }} // env) ->
    {{ [[k <~~ v as vv]] :: (tenv vv) }} prog {{ [[k' <~~ v as vv]] :: tenv' vv }} ∪ {{ ext }} // env.
Proof.
  miniChomp_t; destruct k, k'; simpl; miniChomp_t;
  match goal with
  | [ H: context[NTNone] |- _ ] => rewrite Propagate_anonymous_ret in H
  end; miniChomp_t.
Qed.

Lemma CompileLoopBase2 :
  forall {A1 A2 C}
    `{FacadeWrapper (Value QsADTs.ADTValue) A1}
    `{FacadeWrapper (Value QsADTs.ADTValue) A2}
    `{FacadeWrapper (Value QsADTs.ADTValue) C}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
    (lst: list C) init vhead vtest vlst vret1 vret2
    fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv
    (f: A1 * A2 -> C -> A1 * A2),
    (* GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1; vret2]]] ->
    (forall head (acc1: A1) (acc2: A2) (s: list C),
        {{ [[`vret1 <-- acc1 as _]] :: [[`vret2 <-- acc2 as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: [[`vret2 <-- snd (f (acc1, acc2) head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret1 <-- fst init as _]] :: [[`vret2 <-- snd init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: [[`vret2 <-- snd (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  Transparent DummyArgument.
  unfold DummyArgument; loop_t.

  move_to_front vlst.
  instantiate (1 := [[`vlst <-- lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                              | nil => true
                                                              | _ :: _ => false
                                                              end) as _]] :: [[ ` vret1 <-- fst init as _]]::[[ ` vret2 <-- snd init as _]]::tenv); admit.
  (* eapply (CompileTupleList_Empty_alt (N := N)); loop_t. *)

  2:instantiate (1 := [[ ` vlst <-- nil as _]]::[[ ` vret1 <-- fst (fold_left f lst init) as _]]::[[ ` vret2 <-- snd (fold_left f lst init) as _]]::tenv); admit.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.
  simpl.

  eapply CompileWhileTrue; [ loop_t.. | ].

  instantiate (1 := [[ `vhead <-- a as _ ]] :: [[ `vlst <-- lst as _ ]] :: [[ ` vtest <-- W0 as _]]::[[ ` vret1 <-- fst init as _]]::[[ ` vret2 <-- snd init as _]]::tenv); admit.

  (* rewrite <- GLabelMapFacts.find_mapsto_iff; assumption. *)

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vret2; loop_t.
  move_to_front vret1; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

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
                     ::[[ ` vret1 <-- fst (f (fst init, snd init) a) as _]]
                     ::[[ ` vret2 <-- snd (f (fst init, snd init) a) as _]]::tenv); admit.
  (* apply CompileTupleList_Empty_alt; loop_t. *)

  rewrite <- surjective_pairing.
  loop_t.
Qed.

Lemma CompileLoop2 :
  forall {A1 A2 C}
    `{FacadeWrapper (Value QsADTs.ADTValue) A1}
    `{FacadeWrapper (Value QsADTs.ADTValue) A2}
    `{FacadeWrapper (Value QsADTs.ADTValue) C}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
    (lst: list C) init vhead vtest vlst vret1 vret2
    fpop fempty fdealloc facadeBody facadeConclude
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv'
    (f: A1 * A2 -> C -> A1 * A2),
    (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1; vret2]]] ->
    {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: [[`vret2 <-- snd (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: [[`vret2 <-- snd (fold_left f lst init) as v2]] :: tenv' v1 v2}} ∪ {{ ext }} // env ->
    (forall head (acc1: A1) (acc2: A2) (s: list C),
        {{ [[`vret1 <-- acc1 as _]] :: [[`vret2 <-- acc2 as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: [[`vret2 <-- snd (f (acc1, acc2) head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret1 <-- fst init as _]] :: [[`vret2 <-- snd init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: [[`vret2 <-- snd (fold_left f lst init) as v2]] :: tenv' v1 v2 }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  eapply @CompileLoopBase2; eassumption.
Qed.

Lemma CompileLoop2_Alloc :
  forall {A1 A2 C}
    `{FacadeWrapper (Value QsADTs.ADTValue) A1}
    `{FacadeWrapper (Value QsADTs.ADTValue) A2}
    `{FacadeWrapper (Value QsADTs.ADTValue) C}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
    vhead vtest (lst: list C) init vlst vret1 vret2
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv'
    (f: A1 * A2 -> C -> A1 * A2)
    fpop fempty fdealloc facadeInit facadeBody facadeConclude,
    (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1; vret2]]] ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret1 <-- fst init as _]] :: [[`vret2 <-- snd init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: [[`vret2 <-- snd (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: [[`vret2 <-- snd (fold_left f lst init) as v2]] :: tenv' v1 v2 }} ∪ {{ ext }} // env ->
    (forall head (acc1: A1) (acc2: A2) (s: list C),
        {{ [[`vret1 <-- acc1 as _]] :: [[`vret2 <-- acc2 as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: [[`vret2 <-- snd (f (acc1, acc2) head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: [[`vret2 <-- snd (fold_left f lst init) as v2]] :: tenv' v1 v2 }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  eapply @CompileLoop2; try eassumption.
Qed.

Lemma CompileAppendBool :
  forall {av} {W: FacadeWrapper av (list bool)} vout vbools vbool
    (tenv: Telescope av) tenv' ext env fappend facadeConclude bools b,
    {{ [[ ` vbools <-- bools ++ b :: nil as _]] :: [[ ` vbool <-- b as _]] :: tenv }}
      facadeConclude
    {{ [[ ` vbools <-- bools ++ b :: nil as vbls]] :: tenv' vbls }} ∪ {{ ext }} // env ->
    {{ [[ ` vbools <-- bools as _]] :: [[ ` vbool <-- b as _]] :: tenv }}
      Seq (Call (DummyArgument vout) fappend (vbools :: nil)) facadeConclude
    {{ [[ ` vbools <-- bools ++ b :: nil as bls]] :: tenv' bls }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  admit.
Qed.

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

(* (* This code gets the TC resolution in a loop *)

Instance FacadeWrapper_bool : FacadeWrapper W bool.
Proof.
  refine {| wrap v := (bool2w v) |};
    abstract (intros * H; inversion H; eauto using bool2w_inj).
Defined.

Instance FacadeWrapper_trans {A B C} :
  FacadeWrapper C B ->
  FacadeWrapper B A ->
  FacadeWrapper C A.
Proof.
  intros; refine {| wrap := fun (a : A) => wrap (wrap a: B): C |}.
  intros; do 2 apply wrap_inj; assumption.
Qed.

(* Typeclasses eauto := debug dfs. *)

Lemma CompileDeallocSCA_discretely :
  forall {av} {A} (H: FacadeWrapper W A) (tenv tenv': Telescope av) ext env k (v: Comp A) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ [[`k <~~ v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed. *)

(* Rename SameValues_remove_SCA to SameValues_remove_W *)

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

Definition encode_continue {E B}
           (transformer : Transformer.Transformer B)
           (encode : E -> B * E)
           acc :=
  let (p, e') := encode (snd acc) in
  (Transformer.transform (fst acc) p, e').

Definition compose_acc {E B}
           (transformer : Transformer.Transformer B)
           (encode1 : E -> B * E)
           (encode2 : E -> B * E) e0 :=
  encode_continue transformer encode2 (encode1 e0).

Lemma Compose_compose_acc {E B} :
  forall transformer encode1 encode2 e0,
    @Compose.compose E B transformer encode1 encode2 e0 =
    @compose_acc E B transformer encode1 encode2 e0.
Proof.
  intros; unfold compose_acc, Compose.compose, encode_continue.
  destruct (encode1 _); simpl; destruct (encode2 _); reflexivity.
Qed.

Lemma CompileCompose :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2 (vstream: NameTag av B) (vcache: NameTag av E) (cstream_cache: B * E) tenv ext env p1 p2,
    {{ [[ NTNone  <--  cstream_cache as stream_cache ]]
         :: [[ vstream  <--  (fst stream_cache) as stream ]]
         :: [[ vcache  <--  (snd stream_cache) as cache ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  cstream_cache as stream_cache ]]
         :: [[ NTNone  <--  enc1 (snd cstream_cache) as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform (fst stream_cache) (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
         :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <--  cstream_cache as stream_cache ]]
         :: [[ NTNone  <--  enc1 (snd cstream_cache) as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform (fst stream_cache) (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
         :: tenv }}
      p2
    {{ [[ NTNone  <--  cstream_cache as stream_cache ]]
         :: [[ NTNone  <--  enc1 (snd cstream_cache) as encoded1 ]]
         :: [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
         :: [[ vstream  <--  Transformer.transform (Transformer.transform (fst stream_cache) (fst encoded1)) (fst encoded2) as stream2 ]]
         :: [[ vcache  <--  (snd encoded2) as cache2 ]]
         :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <--  cstream_cache as stream_cache ]]
         :: [[ vstream  <--  (fst stream_cache) as stream ]]
         :: [[ vcache  <--  (snd stream_cache) as cache ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  cstream_cache as stream_cache ]]
         :: [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 (snd stream_cache) as composed ]]
         :: [[ vstream  <--  Transformer.transform (fst stream_cache) (fst composed) as stream ]]
         :: [[ vcache  <--  (snd composed) as cache ]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  setoid_rewrite Compose_compose_acc.
  unfold compose_acc, encode_continue.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  destruct cstream_cache; simpl in *.
  destruct (enc1 _); simpl in *.
  destruct (enc2 _); simpl in *.
  rewrite Transformer.transform_assoc; assumption.
Qed.

Lemma CompileCompose_spec :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2 (vstream: NameTag av B) (vcache: NameTag av E) (stream_cache: B * E) tenv ext env p1 p2,
    {{ [[ vstream  <--  (fst stream_cache) as stream ]]
         :: [[ vcache  <--  (snd stream_cache) as cache ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 (snd stream_cache) as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform (fst stream_cache) (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
         :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <--  enc1 (snd stream_cache) as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform (fst stream_cache) (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
         :: tenv }}
      p2
    {{ [[ NTNone  <--  enc1 (snd stream_cache) as encoded1 ]]
         :: [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
         :: [[ vstream  <--  Transformer.transform (Transformer.transform (fst stream_cache) (fst encoded1)) (fst encoded2) as stream2 ]]
         :: [[ vcache  <--  (snd encoded2) as cache2 ]]
         :: tenv }} ∪ {{ ext }} // env ->
    {{ [[ vstream  <--  (fst stream_cache) as stream ]]
         :: [[ vcache  <--  (snd stream_cache) as cache ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 (snd stream_cache) as composed ]]
         :: [[ vstream  <--  Transformer.transform (fst stream_cache) (fst composed) as stream ]]
         :: [[ vcache  <--  (snd composed) as cache ]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  setoid_rewrite Compose_compose_acc.
  unfold compose_acc, encode_continue.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  destruct stream_cache; simpl in *.
  destruct (enc1 _); simpl in *.
  destruct (enc2 _); simpl in *.
  rewrite Transformer.transform_assoc; assumption.
Qed.

Lemma CompileCompose_spec' :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (vcache: NameTag av E) (stream: B) (cache: E)
    tenv tenv' tenv'' ext env p1 p2,
    {{ [[ vstream  <--  stream as _ ]]
         :: [[ vcache  <--  cache as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform stream (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
         :: tenv' }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ [[ vstream  <--  stream1 as _ ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
          :: tenv' }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform stream1 (fst encoded2) as stream2 ]]
          :: [[ vcache  <--  (snd encoded2) as cache2 ]]
          :: tenv'' }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  stream as _ ]]
         :: [[ vcache  <--  cache as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  Transformer.transform stream (fst composed) as stream ]]
         :: [[ vcache  <--  (snd composed) as cache ]]
         :: tenv'' }} ∪ {{ ext }} // env.
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

Lemma ProgOk_Add_snd :
  forall {A B av} (kfst: NameTag av _) (ksnd: NameTag av _) (cpair: Comp (A * B)) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
    {{ [[ NTNone  <~~  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: [[ ksnd  <--  snd pair as p2 ]]
         :: tenv' pair }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  <~~  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: [[ ksnd  <--  snd pair as p2 ]]
         :: tenv' pair }}
      p2
    {{ [[ NTNone  <~~  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]]
         :: tenv' pair }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <~~  cpair as pair ]]
         :: [[ kfst  <--  fst pair as p1 ]] :: tenv' pair }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
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

Ltac compile_compose_internal :=
  eapply CompileCompose_spec';
  [ | intros;
      let stream := fresh "stream" in
      set (Transformer.transform _ _) as stream ].

Definition PacketAsCollectionOfVariables
           {av} vid vmask vquestion vanswer vauthority vadditional tail (p: packet_t)
  : Telescope av :=
  [[ vid <-- ` p.(pid) as _ ]]
    :: [[ vmask <-- ` p.(pmask) as _ ]]
    :: [[ vquestion <-- ` p.(pquestion) as _ ]]
    :: [[ vanswer <-- ` p.(panswer) as _ ]]
    :: [[ vauthority <-- ` p.(pauthority) as _ ]]
    :: [[ vadditional <-- ` p.(padditional) as _ ]]
    :: tail.

Definition DnsCacheAsCollectionOfVariables
           {av} veMap vdMap voffs tail (c: DnsMap.CacheT)
  : Telescope av :=
  [[ veMap <-- c.(DnsMap.eMap) as _ ]]
    :: [[ vdMap <-- c.(DnsMap.dMap) as _ ]]
    :: [[ voffs <-- c.(DnsMap.offs) as _ ]]
    :: tail.

Lemma CompileLoop2_destructed :
  forall {A1 A2 C}
    `{FacadeWrapper (Value QsADTs.ADTValue) A1}
    `{FacadeWrapper (Value QsADTs.ADTValue) A2}
    `{FacadeWrapper (Value QsADTs.ADTValue) C}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
    vhead vtest vlst vret1 vret2
    (lst: list C) init1 init2 (init := (init1, init2))
    fpop fempty fdealloc facadeBody facadeConclude
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv'
    (f: A1 * A2 -> C -> A1 * A2),
    (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1; vret2]]] ->
    {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: [[`vret2 <-- snd (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: [[`vret2 <-- snd (fold_left f lst init) as v2]] :: tenv' v1 v2}} ∪ {{ ext }} // env ->
    (forall head (acc1: A1) (acc2: A2) (s: list C),
        {{ [[`vret1 <-- acc1 as _]] :: [[`vret2 <-- acc2 as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: [[`vret2 <-- snd (f (acc1, acc2) head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: [[`vret1 <-- init1 as _]] :: [[`vret2 <-- init2 as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[ ret (fold_left f lst init) as folded ]]
         :: [[`vret1 <-- fst folded as v1]]
         :: [[`vret2 <-- snd folded as v2]]
         :: tenv' v1 v2 }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite Propagate_anonymous_ret.
  hoare.
  move_to_front vret2.
  move_to_front vret1.
  change init1 with (fst init).
  change init2 with (snd init).
  eapply @CompileLoopBase2; eassumption.
Qed.

Lemma CompileCompose_init :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (vstream: NameTag av B) (vcache: NameTag av E) (cache: E)
    tenv tenv' tenv'' ext env p1 p2,
    {{ [[ vstream  <--  Transformer.transform_id as _ ]]
         :: [[ vcache  <--  cache as _ ]]
         :: tenv }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: [[ vstream  <--  Transformer.transform Transformer.transform_id (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
         :: tenv' }} ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     {{ [[ vstream  <--  (fst encoded1) as stream1 ]]
         :: [[ vcache  <--  (snd encoded1) as cache1 ]]
          :: tenv' }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: [[ vstream  <--  Transformer.transform (fst encoded1) (fst encoded2) as stream2 ]]
          :: [[ vcache  <--  (snd encoded2) as cache2 ]]
          :: tenv'' }} ∪ {{ ext }} // env) ->
    {{ [[ vstream  <--  Transformer.transform_id as _ ]]
         :: [[ vcache  <--  cache as _ ]]
         :: tenv }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: [[ vstream  <--  (fst composed) as stream ]]
         :: [[ vcache  <--  (snd composed) as cache ]]
         :: tenv'' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eapply CompileCompose_spec'; cbv zeta.
  eassumption.
  setoid_rewrite Transformer.transform_id_left; eassumption.
Qed.

Lemma ProgOk_Transitivity_DropName :
  forall {av A} {W: FacadeWrapper (Value av) A} env ext (t1: Telescope av) t2 prog1 prog2 (k: string) (v: Comp A),
    {{ t1 }}                     prog1      {{ [[`k <~~ v as _]]::DropName k t1 }}     ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as _]]::DropName k t1 }}      prog2      {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                Seq prog1 prog2 {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  eauto using CompileSeq.
Qed.

Lemma ProgOk_Transitivity_First :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v1 v2: Comp A),
    {{ [[k <~~ v1 as _]]::t1 }}       prog1      {{ [[k <~~ v2 as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k <~~ v2 as _]]::t1 }}       prog2      {{ [[k <~~ v2 as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[k <~~ v1 as _]]::t1 }}  Seq prog1 prog2 {{ [[k <~~ v2 as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  eauto using CompileSeq.
Qed.

Lemma IList_encode_bools_is_copy:
  forall bits cache,
    (IList.IList_encode' DnsMap.cache Core.btransformer Bool.Bool_encode bits cache) =
    (bits, {| DnsMap.eMap := DnsMap.eMap cache;
              DnsMap.dMap := DnsMap.dMap cache;
              DnsMap.offs := DnsMap.offs cache + (N.of_nat (List.length bits)) |}).
Proof.
  Opaque N.of_nat.
  induction bits; destruct cache; simpl in *.
  + rewrite N.add_0_r; reflexivity.
  + rewrite IHbits; simpl.
    rewrite <- N.add_assoc, N.add_1_l, Nat2N.inj_succ; reflexivity.
    Transparent N.of_nat.
Qed.

Definition EncodeAndPad n length :=
  let encoded := FixInt.encode' n in
  FixInt.pad encoded (length - Datatypes.length encoded).

Lemma FixInt_encode_is_copy {size}:
  forall num cache,
    (FixInt.FixInt_encode (size := size) num cache) =
    (EncodeAndPad (`num) size, {| DnsMap.eMap := DnsMap.eMap cache;
                                  DnsMap.dMap := DnsMap.dMap cache;
                                  DnsMap.offs := DnsMap.offs cache + (N.of_nat size) |}).
Proof.
  destruct cache; reflexivity.
Qed.

Lemma CompileCallWrite16:
  forall {av} {W: FacadeWrapper av (list bool)}
    (vtmp varg vstream : string) (stream : list bool) (tenv tenv': Telescope av)
    (n : N) (ext : GLabelMap.t (FuncSpec av))
    pArg pNext fWrite16,
    {{ [[ ` vstream <-- stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream <-- stream as _]]::[[ ` varg <-- Word.NToWord n as _]]::tenv }} ∪ {{ ∅ }} // ext ->
    {{ [[ ` vstream <-- stream ++ EncodeAndPad n 16 as _]]::tenv }}
      pNext
    {{ [[ ` vstream <-- stream ++ EncodeAndPad n 16 as _]]::tenv' }} ∪ {{ ∅ }} // ext ->
    {{ [[ ` vstream <-- stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite16 [vstream; varg]) pNext)
    {{ [[ ` vstream <-- stream ++ EncodeAndPad n 16 as _]]::tenv' }} ∪ {{ ∅ }} // ext.
Proof.
  hoare.
  hoare.
  hoare.
Admitted.

Definition List16AsWord (ls: {s : list bool | Datatypes.length s = 16}) : W.
Admitted.

Lemma EncodeAndPad_ListAsWord : forall ls, `ls = EncodeAndPad (Word.wordToN (List16AsWord ls)) 16.
Admitted.

Ltac _compile_callWrite16 :=
  simpl;
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:post with
            | [[ _ <-- _ ++ ?arg as _]] :: _ =>
              let vtmp := gensym "tmp" in
              let varg := gensym "arg" in
              try match arg with ` ?arg => rewrite (EncodeAndPad_ListAsWord arg) end;
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
  (eapply CompileCompose_spec' || eapply CompileCompose_init); intros.

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

Ltac _packet_encode_FixInt :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:post with
            | [[ret (FixInt.FixInt_encode _ _) as _]] :: _ =>
              rewrite FixInt_encode_is_copy;
              setoid_rewrite Propagate_anonymous_ret; simpl;
              apply ProgOk_Transitivity_First
            end).

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

Ltac _compile_CallListLength :=
  match_ProgOk
    ltac:(fun _ _ post _ _ =>
            match constr:post with
            | [[ _ <-- Word.natToWord 32 (Datatypes.length ?lst) as _]] :: _ =>
              (* FIXME this should be an equivalent of find_in_ext *)
              (* FIXME this shoud be more principled *)
              unfold PacketAsCollectionOfVariables; simpl;
              match_ProgOk
                ltac:(fun _ pre _ _ _ =>
                        match constr:pre with
                        | context[Cons (NTSome ?k) (ret lst) _] =>
                          (eapply (CompileCallListResourceLength k) ||
                           eapply (CompileCallListQuestionLength k));
                          [ decide_TelEq_instantiate ]
                        end)
            end).

Ltac _compile_CallAllocString :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:post with
            | Cons _ (ret Transformer.transform_id) _ =>
              let vtmp := gensym "tmp" in
              eapply (CompileCallAllocString vtmp)
            end).

Lemma NToWord_of_nat:
  forall (sz : nat) (n : nat),
    Word.NToWord (N.of_nat n) = Word.natToWord sz n.
Proof.
  intros; rewrite Word.NToWord_nat, Nat2N.id; reflexivity.
Qed.

Lemma NToWord_WordToN:
  forall (sz : nat) (w : Word.word sz),
    Word.NToWord (Word.wordToN w) = w.
Proof.
  intros; rewrite Word.NToWord_nat, Word.wordToN_nat, Nat2N.id.
  apply Word.natToWord_wordToNat.
Qed.

Lemma length_of_fixed_length_list :
  forall {size} (ls: {s : list bool | Datatypes.length s = size}),
    List.length (`ls) = size.
Proof.
  destruct ls; auto.
Qed.

Lemma FixList_is_IList :
  forall (A bin : Type) (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (env : Cache.CacheEncode),
    @FixList.FixList_encode' A bin cache transformer A_encode xs env =
    @IList.IList_encode' A bin cache transformer A_encode xs env.
Proof.
  induction xs; simpl; intros.
  + reflexivity.
  + destruct (A_encode _ _).
    rewrite IHxs; reflexivity.
Qed.

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
                  match constr:post with
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

Ltac _packet_encode_step :=
  match goal with
  | _ => _packet_encode_cleanup
  | _ => _packet_encode_FixInt
  | _ => _compile_callWrite16
  | _ => _compile_CallListLength
  | _ => _compile_CallAllocString
  | _ => _compile_step
  end.

Ltac _packet_encode_t :=
  repeat _packet_encode_step.


Lemma CompileCompose_spec'' :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (stream: B) (cache: E) (tenv tenv' tenv'': B -> E -> Telescope av) ext env p1 p2,
    {{ tenv stream cache }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: tenv' (Transformer.transform stream (fst encoded1)) (snd encoded1) }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     let stream1 := Transformer.transform stream (fst encoded1) in
     {{ tenv' stream1 (snd encoded1) }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: tenv'' (Transformer.transform stream1 (fst encoded2)) (snd encoded2) }}
     ∪ {{ ext }} // env) ->
    {{ tenv stream cache }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: tenv'' (Transformer.transform stream (fst composed)) (snd composed) }}
    ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  setoid_rewrite Compose_compose_acc.
  unfold compose_acc, encode_continue.
  cbv zeta in *.
  repeat rewrite @Propagate_anonymous_ret in *.
  destruct (enc1 _); simpl in *; destruct (enc2 _); simpl in *;
    rewrite Transformer.transform_assoc; assumption.
Qed.

Lemma CompileCompose_spec''' :
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

(* Lemma CompileCompose_init' : *)
(*   forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2 *)
(*     (cache: E) (tenv tenv' tenv'': B -> E -> Telescope av) ext env p1 p2, *)
(*     {{ tenv Transformer.transform_id cache }} *)
(*       p1 *)
(*     {{ [[ NTNone  <--  enc1 cache as encoded1 ]] *)
(*          :: tenv' (Transformer.transform Transformer.transform_id (fst encoded1)) (snd encoded1) }} *)
(*     ∪ {{ ext }} // env -> *)
(*     (let encoded1 := enc1 cache in *)
(*      {{ tenv' (fst encoded1) (snd encoded1) }} *)
(*        p2 *)
(*      {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]] *)
(*           :: tenv'' (Transformer.transform (fst encoded1) (fst encoded2)) (snd encoded2) }} *)
(*      ∪ {{ ext }} // env) -> *)
(*     {{ tenv Transformer.transform_id cache }} *)
(*       (Seq p1 p2) *)
(*     {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]] *)
(*          :: tenv'' (fst composed) (snd composed) }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   intros. *)
(*   setoid_rewrite <- (Transformer.transform_id_left (fst _)). *)
(*   eapply CompileCompose_spec''; cbv zeta. *)
(*   eassumption. *)
(*   setoid_rewrite Transformer.transform_id_left; eassumption. *)
(* Qed. *)

Lemma CompileCompose_init'' :
  forall {av} E B (transformer: Transformer.Transformer B) enc1 enc2
    (cache: E) (tenv tenv' tenv'': B -> E -> Telescope av) ext env p1 p2,
    {{ tenv Transformer.transform_id cache }}
      p1
    {{ [[ NTNone  <--  enc1 cache as encoded1 ]]
         :: tenv' (Transformer.transform Transformer.transform_id (fst encoded1)) (snd encoded1) }}
    ∪ {{ ext }} // env ->
    (let encoded1 := enc1 cache in
     {{ tenv' (fst encoded1) (snd encoded1) }}
       p2
     {{ [[ NTNone  <--  enc2 (snd encoded1) as encoded2 ]]
          :: tenv'' (Transformer.transform (fst encoded1) (fst encoded2)) (snd encoded2) }}
     ∪ {{ ext }} // env) ->
    {{ tenv Transformer.transform_id cache }}
      (Seq p1 p2)
    {{ [[ NTNone  <--  @Compose.compose E B transformer enc1 enc2 cache as composed ]]
         :: tenv'' (fst composed) (snd composed) }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- (Transformer.transform_id_left (fst _)).
  eapply CompileCompose_spec''; cbv zeta.
  eassumption.
  setoid_rewrite Transformer.transform_id_left; eassumption.
Qed.

Lemma CompileCompose_init''' :
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
  eapply CompileCompose_spec'''; cbv zeta.
  eassumption.
  setoid_rewrite Transformer.transform_id_left; eassumption.
Qed.


Lemma CompileLoopBase2' :
  forall {A1 A2 C}
    `{FacadeWrapper (Value QsADTs.ADTValue) A1}
    `{FacadeWrapper (Value QsADTs.ADTValue) C}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
    (lst: list C) init vhead vtest vlst vret1
    fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv
    (f: A1 * A2 -> C -> A1 * A2) tenvF,
    (* GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1]]] ->
    (forall v, NotInTelescope vtest (tenvF tenv v)) ->
    (forall head (acc1: A1) (acc2: A2) (s: list C),
        {{ [[`vhead <-- head as _]] :: [[`vret1 <-- acc1 as _]] :: tenvF tenv acc2 }}
          facadeBody
        {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: tenvF tenv (snd (f (acc1, acc2) head)) }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: [[`vret1 <-- fst init as _]] :: tenvF tenv (snd init) }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: tenvF tenv (snd (fold_left f lst init)) }} ∪ {{ ext }} // env.
Proof.
  Transparent DummyArgument.
  unfold DummyArgument; loop_t.

  instantiate (1 := [[`vlst <-- lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                              | nil => true
                                                              | _ :: _ => false
                                                              end) as _]] :: [[ ` vret1 <-- fst init as _]]
                                         :: tenvF tenv (snd init)); admit.
  (* eapply (CompileTupleList_Empty_alt (N := N)); loop_t. *)

  2:instantiate (1 := [[ ` vlst <-- nil as _]]::[[ ` vret1 <-- fst (fold_left f lst init) as _]]:: tenvF tenv (snd (fold_left f lst init))); admit.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

Ltac decide_NotInTelescope ::=
  progress repeat match goal with
                  | _ => cleanup
                  | _ => congruence
                  | [  |- NotInTelescope _ Nil ] => reflexivity
                  | [  |- NotInTelescope ?k (Cons _ _ _) ] => simpl
                  | _ => auto 1  (* Added for tricky cases like CompileLoopBase2 *)
                  end.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.

  simpl.

  eapply CompileWhileTrue; [ loop_t.. | ].

  instantiate (1 := [[ `vhead <-- a as _ ]] :: [[ `vlst <-- lst as _ ]] :: [[ ` vtest <-- W0 as _]]::[[ ` vret1 <-- fst init as _]]::tenvF tenv (snd init)); admit.

  (* rewrite <- GLabelMapFacts.find_mapsto_iff; assumption. *)

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

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
                     ::[[ ` vret1 <-- fst (f (fst init, snd init) a) as _]]
                     :: tenvF tenv (snd (f (fst init, snd init) a))); admit.
  (* apply CompileTupleList_Empty_alt; loop_t. *)

  rewrite <- surjective_pairing.
  loop_t.
Qed.

Lemma CompileLoop2_destructed' :
  forall {A1 A2 C}
    `{FacadeWrapper (Value QsADTs.ADTValue) A1}
    `{FacadeWrapper (Value QsADTs.ADTValue) C}
    `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
    vhead vtest vlst vret1
    (lst: list C) init1 init2 (init := (init1, init2))
    tenvF (f: A1 * A2 -> C -> A1 * A2) tenv tenv'
    env (ext: StringMap.t (Value QsADTs.ADTValue))
    fpop fempty fdealloc facadeBody facadeConclude,
    (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
    (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
    (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1]]] ->
    (forall v, NotInTelescope vtest (tenvF tenv v)) ->
    {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: tenvF tenv (snd (fold_left f lst init)) }}
      facadeConclude
    {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: tenvF tenv' (snd (fold_left f lst init)) }}
    ∪ {{ ext }} // env ->
    (forall head (acc1: A1) (acc2: A2) (s: list C),
        {{ [[`vhead <-- head as _]] :: [[`vret1 <-- acc1 as _]] :: tenvF tenv acc2 }}
          facadeBody
        {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: tenvF tenv (snd (f (acc1, acc2) head)) }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: [[`vret1 <-- init1 as _]] :: tenvF tenv init2 }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[ ret (fold_left f lst init) as folded ]]
         :: [[`vret1 <-- fst folded as v1]]
         :: tenvF tenv' (snd folded) }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite Propagate_anonymous_ret.
  hoare.
  change init1 with (fst init).
  change init2 with (snd init).
  eapply @CompileLoopBase2'; eassumption.
Qed.

Example encode :
  ParametricExtraction
    #vars      p
    #program   ret (packet_encode p)
    #arguments (PacketAsCollectionOfVariables
                  (NTSome "id") (NTSome "mask") (NTSome "question")
                  (NTSome "answer") (NTSome "authority") (NTSome "additional")
                  Nil p)
    #env       (GLabelMap.empty (FuncSpec ADTValue)).
Proof.
  start_compiling.
  packet_start_compiling.

  (* FIXME use multiple variables for the cache *)
  eapply (ProgOk_Add_snd_ret (DnsCacheAsCollectionOfVariables (NTSome "eMap") (NTSome "dMap") (NTSome "offs"))).

  eapply CompileSeq; [ | repeat compile_compose]; _packet_encode_t.

  Focus 2.
  repeat ((eapply CompileCompose_spec''' || eapply CompileCompose_init'''); intros); _packet_encode_t.
  Unfocus.

  Focus.
  _packet_encode_t.
  unfold DnsCacheAsCollectionOfVariables.
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocEMap vtmp).
  _packet_encode_t.
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocDMap vtmp).
  _packet_encode_t.
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocOffset vtmp).
  _packet_encode_t.
  Unfocused.

  Focus.
  instantiate (1 := Assign "arg" (Var "pid")); admit.
  keep_unmodified_packet.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment counter in cache") nil); admit.
  Unfocused.

  Focus.
  instantiate (1 := Assign "arg" (Var "mask")); admit.
  keep_unmodified_packet.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment counter in cache") nil); admit.
  Unfocused.

  Focus.
Ltac _compile_CallListLength ::=
  match_ProgOk
    ltac:(fun _ _ post _ _ =>
            match constr:post with
            | [[ _ <-- Word.natToWord 32 (Datatypes.length ?lst) as _]] :: _ =>
              (* FIXME this should be an equivalent of find_in_ext *)
              (* FIXME this shoud be more principled *)
              unfold PacketAsCollectionOfVariables; simpl;
              match_ProgOk
                ltac:(fun _ pre _ _ _ =>
                        match constr:pre with
                        | context[Cons (NTSome ?k) (ret lst) _] =>
                          (eapply (CompileCallListResourceLength k) ||
                           eapply (CompileCallListQuestionLength k));
                          [ unfold DnsCacheAsCollectionOfVariables; (* FIXME autounfold *)
                            decide_TelEq_instantiate ]
                        end)
            end).
  _packet_encode_t.
  keep_unmodified_packet.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment counter in cache") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  keep_unmodified_packet.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment cache counter") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  keep_unmodified_packet.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment cache counter") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  keep_unmodified_packet.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Increment cache counter") nil); admit.
  Unfocused.

  Lemma IList_post_transform_TelEq :
    forall {av} {A bin : Type}
      (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
      (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
      (xs : list A) (base : bin) (env : Cache.CacheEncode)
      k__stream (cacheF: Telescope av -> Cache.CacheEncode -> Telescope av) (tenv: Telescope av) ext,
      let fold_on b :=
          fold_left (IList.IList_encode'_body cache transformer A_encode) xs (b, env) in
      TelEq ext
        ([[ret (fold_on Transformer.transform_id) as folded]]
           ::[[ k__stream <-- Transformer.transform base (fst folded) as _]] :: cacheF tenv (snd folded))
        ([[ret (fold_on base) as folded]]
           ::[[ k__stream <-- fst folded as _]] :: cacheF tenv (snd folded)).
  Proof.
    cbv zeta; intros.
    setoid_rewrite Propagate_anonymous_ret.
    rewrite (IList.IList_encode'_body_characterization _ _ _ _ base).
    destruct (fold_left _ _ _); simpl; reflexivity.
  Qed.

  Inductive EvarTag {T A} (a: A) (t: T) := __EvarTag.

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
      rewrite (IList_post_transform_TelEq cache)
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

  Lemma CompileLoop2_destructed'' :
    forall {A1 A2 C}
      `{FacadeWrapper (Value QsADTs.ADTValue) A1}
      `{FacadeWrapper (Value QsADTs.ADTValue) C}
      `{FacadeWrapper (Value QsADTs.ADTValue) (list C)}
      vhead vtest vlst vret1
      (lst: list C) init1 init2 (init := (init1, init2))
      tenvF (f: A1 * A2 -> C -> A1 * A2) tenv0 tenv tenv'
      env (ext: StringMap.t (Value QsADTs.ADTValue))
      fpop fempty fdealloc facadeBody facadeConclude,
      (* GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env -> *)
      (* GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env -> *)
      (* GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env -> *)
      PreconditionSet tenv ext [[[vhead; vtest; vlst; vret1]]] ->
      TelEq ext tenv0 ([[`vlst <-- lst as _]] :: [[`vret1 <-- init1 as _]] :: tenvF tenv init2) ->
      (forall v, NotInTelescope vtest (tenvF tenv v)) ->
      {{ [[`vret1 <-- fst (fold_left f lst init) as _]] :: tenvF tenv (snd (fold_left f lst init)) }}
        facadeConclude
        {{ [[`vret1 <-- fst (fold_left f lst init) as v1]] :: tenvF tenv' (snd (fold_left f lst init)) }}
        ∪ {{ ext }} // env ->
      (forall head (acc1: A1) (acc2: A2) (s: list C),
          {{ [[`vhead <-- head as _]] :: [[`vret1 <-- acc1 as _]] :: tenvF tenv acc2 }}
            facadeBody
            {{ [[`vret1 <-- fst (f (acc1, acc2) head) as _]] :: tenvF tenv (snd (f (acc1, acc2) head)) }} ∪
            {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
      {{ tenv0 }}
        (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
        {{ [[ ret (fold_left f lst init) as folded ]]
             :: [[`vret1 <-- fst folded as v1]]
             :: tenvF tenv' (snd folded) }} ∪ {{ ext }} // env.
  Proof.
    intros.
    rewrite H3.
    setoid_rewrite Propagate_anonymous_ret.
    hoare.
    change init1 with (fst init).
    change init2 with (snd init).
    eapply @CompileLoopBase2'; eassumption.
  Qed.

  Ltac _packet_encode_IList__compile_loop :=
    unfold PacketAsCollectionOfVariables; simpl;
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:post with
              | appcontext[fold_left (IList.IList_encode'_body _ _ _) ?lst] =>
                match constr:pre with
                | context[Cons (NTSome ?vlst) (ret lst) _] =>
                  delete_tagged_var_from_post vlst;
                  let vhead := gensym "head" in
                  let vtest := gensym "test" in
                  eapply (CompileLoop2_destructed'' vhead vtest vlst);
                  [ | unfold DnsCacheAsCollectionOfVariables; simpl; decide_TelEq_instantiate | idtac.. ]
                end
              end).

  Ltac _packet_encode_IList_compile :=
    _packet_encode_IList__rewrite_as_fold;
    _packet__havoc_packet_in_postcondition;
    _packet_encode_IList__compile_loop.

  Add Parametric Morphism {av} ext : (@DnsCacheAsCollectionOfVariables av)
    with signature (eq ==> eq ==> eq ==> (TelEq ext) ==> eq ==> (TelEq ext))
      as DnsCacheAsCollectionOfVariables_TelEq_morphism.
  Proof.
    unfold DnsCacheAsCollectionOfVariables; intros * teq **.
    repeat (apply TelEq_chomp_head; red; intros).
    assumption.
  Qed.

  Focus.
  _packet_encode_t.
  _packet_encode_IList_compile.
  compile_do_side_conditions.
  _packet_encode_t.
  unfold DnsCacheAsCollectionOfVariables; decide_NotInTelescope.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode question") nil); admit.
  Unfocused.

  (* Lemma antiChomp: *)
  (*   forall (av A : Type) (H : FacadeWrapper (Value av) A) *)
  (*     (env : Env av) (key : StringMap.key) (v : A) *)
  (*     (prog : Stmt) (tail1 tail2 : Telescope av) *)
  (*     (ext : StringMap.t (Value av)), *)
  (*     key ∉ ext -> *)
  (*     {{ [[ `key  <--  v as kk]]::tail1 }} *)
  (*       prog *)
  (*     {{ [[ `key  <--  v as kk]]::tail2 }} ∪ {{ ext }} // env -> *)
  (*     {{ tail1 }} *)
  (*       prog *)
  (*     {{ tail2 }} ∪ {{ [key <-- wrap v]::ext }} // env. *)
  (* Proof. *)
  (*   SameValues_Facade_t; *)
  (*   change tail1 with ((fun v => tail1) v) in H2; *)
  (*   apply Cons_PopExt in H2; *)
  (*   SameValues_Facade_t. *)
  (* Qed. *)

  Focus.
  _packet_encode_t.
  _packet_encode_IList__rewrite_as_fold.
  _packet__havoc_packet_in_postcondition.

  Ltac _packet_encode__clear_EvarTags :=
    repeat match goal with
           | [ H: EvarTag ?v ?tag |- _ ] => try unify v tag; clear H
           end.

  Ltac _compile_Loop2 vlst :=
    let vhead := gensym "head" in
    let vtest := gensym "test" in
    eapply (CompileLoop2_destructed'' vhead vtest vlst);
    [ | unfold DnsCacheAsCollectionOfVariables; simpl; decide_TelEq_instantiate | idtac.. ].

  Ltac _packet_encode_IList__compile_loop ::=
    unfold PacketAsCollectionOfVariables; simpl;
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:post with
              | appcontext[fold_left (IList.IList_encode'_body _ _ _) ?lst] =>
                match constr:pre with
                | context[Cons (NTSome ?vlst) (ret lst) _] =>
                  delete_tagged_var_from_post vlst;
                  _packet_encode__clear_EvarTags;
                  _compile_Loop2 vlst
                end
              end).

  Ltac decide_TelEq_instantiate_step ::=
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

  _packet_encode_IList__compile_loop.
  (* Note: One could also never unfold PacketAsCollectionOfVariables and DnsCacheAsCollectionOfVariables (and instead find the variable to loop on by copying the precondition into the context and unfolding locally. *)
  compile_do_side_conditions.
  _packet_encode_t; unfold DnsCacheAsCollectionOfVariables; decide_NotInTelescope.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode answer") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  _packet_encode_IList_compile.
  compile_do_side_conditions.
  _packet_encode_t; unfold DnsCacheAsCollectionOfVariables; decide_NotInTelescope.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority") nil); admit.
  Unfocused.

  Focus.
  _packet_encode_t.
  _packet_encode_IList_compile.
  compile_do_side_conditions.
  _packet_encode_t; unfold DnsCacheAsCollectionOfVariables; decide_NotInTelescope.
  _packet_encode_t.
  instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional") nil); admit.
  Unfocused.

  repeat lazymatch goal with
         | [  |- context[fst (?a, ?b)] ] => change (fst (a, b)) with a
         | [  |- context[snd (?a, ?b)] ] => change (snd (a, b)) with b
         | [  |- context[Transformer.transform nil _] ] => setoid_rewrite @Transformer.transform_id_left
         | [  |- context[Transformer.transform _ nil] ] => setoid_rewrite @Transformer.transform_id_right
         end.

  _packet_encode_t.
  unfold DnsCacheAsCollectionOfVariables, PacketAsCollectionOfVariables; simpl.
  _packet_encode_t.
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
