Require Import
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.TelAppend.

Lemma CompileConstant:
  forall {av} name env w ext (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    {{ tenv }}
      (Assign name (Const w))
    {{ [[`name ->> w as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileConstantBool:
  forall {av} name env (b: bool) ext (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    {{ tenv }}
      (Assign name (Const (bool2w b)))
    {{ [[`name ->> b as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  change (wrap (bool2w b)) with (wrap (FacadeWrapper := (@FacadeWrapper_bool av)) b).
  SameValues_Facade_t.
Qed.

Lemma CompileRead:
  forall {av} name var (val: W) ext (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var (wrap val) ext ->
    forall env,
    {{ tenv }}
      (Assign name (Var var))
    {{ [[`name ->> val as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileSkip:
  forall {av} (ext : StringMap.t (Value av)) env tenv,
    {{ tenv }}
      Skip
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_First :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v1 v2: Comp A),
    {{ [[k ~~> v1 as _]]::t1 }}       prog1      {{ [[k ~~> v2 as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k ~~> v2 as _]]::t1 }}       prog2      {{ [[k ~~> v2 as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[k ~~> v1 as _]]::t1 }}  Seq prog1 prog2 {{ [[k ~~> v2 as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_First_defunc :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v1 v2: Comp A),
    {{ [[k ~~> v1 as _]]::t1 }}       prog1      {{ [[k ~~> v2 as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k ~~> v2 as _]]::t1 }}       prog2      {{ [[k ~~> v2 as kk]]::t2 }} ∪ {{ ext }} // env ->
    {{ [[k ~~> v1 as _]]::t1 }}  Seq prog1 prog2 {{ [[k ~~> v2 as kk]]::t2 }} ∪ {{ ext }} // env.
Proof.
  intros; apply ProgOk_Transitivity_First; assumption.
Qed.

Lemma ProgOk_Transitivity_Cons :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v: Comp A),
    {{ t1 }}                     prog1      {{ [[k ~~> v as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k ~~> v as _]]::t1 }}      prog2      {{ [[k ~~> v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                Seq prog1 prog2 {{ [[k ~~> v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_Cons_defunc :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v: Comp A),
    {{ t1 }}                     prog1      {{ [[k ~~> v as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k ~~> v as _]]::t1 }}      prog2      {{ [[k ~~> v as kk]]::t2 }} ∪ {{ ext }} // env ->
    {{ t1 }}                Seq prog1 prog2 {{ [[k ~~> v as kk]]::t2 }} ∪ {{ ext }} // env.
Proof.
  intros; apply ProgOk_Transitivity_Cons; assumption.
Qed.

Lemma ProgOk_Transitivity_Name :
  forall `{FacadeWrapper (Value av) A} k env ext t1 t2 prog1 prog2 (v: Comp A),
    {{ t1 }}                          prog1        {{ [[`k ~~> v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> v as kk]]::t2 kk }}      prog2        {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                      Seq prog1 prog2  {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_Name' :
  forall `{FacadeWrapper (Value av) A} k env ext t1 t2 prog1 prog2 (v: Comp A),
    {{ t1 }}                     prog1        {{ [[`k ~~> v as _]]::t1 }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> v as _]]::t1 }}     prog2        {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                 Seq prog1 prog2  {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Remove_Skip_L :
  forall {av} ext (t1 t2: Telescope av) env prog,
    {{ t1 }} (Seq Skip prog) {{ t2 }} ∪ {{ ext }} // env ->
    {{ t1 }} prog {{ t2 }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  learn (RunsToSkip env (Equal_refl initial_state)); eauto.
  learn (RunsToSeq (RunsToSkip _ (Equal_refl _)) H1); eauto.
Qed.

Lemma ProgOk_Remove_Skip_R :
  forall {av} ext (t1 t2: Telescope av) env prog,
    {{ t1 }} (Seq prog Skip) {{ t2 }} ∪ {{ ext }} // env ->
    {{ t1 }} prog {{ t2 }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  learn (RunsToSeq H1 (RunsToSkip _ (Equal_refl _))); eauto.
Qed.

Lemma ProgOk_Transitivity_Name_SCA :
  forall {av} k env ext t1 (t2: W -> Telescope av) prog1 (v: Comp W),
    {{ t1 }} prog1 {{ [[`k ~~> v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }} prog1 {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  eauto using SameValues_Dealloc_W.
Qed.

Lemma CompileSeq :
  forall {av} (tenv1 tenv1' tenv2: Telescope av) ext env p1 p2,
    {{ tenv1 }}
      p1
    {{ tenv1' }} ∪ {{ ext }} // env ->
    {{ tenv1' }}
      p2
    {{ tenv2 }} ∪ {{ ext }} // env ->
    {{ tenv1 }}
      (Seq p1 p2)
    {{ tenv2 }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Add_snd_under_fn_ret :
  forall {A A' B av} (f: B -> Telescope av) (g: A -> A') (kfst: NameTag av _) (cpair: A * B) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
      {{ [[ NTNone  ->>  cpair as pair ]]
          :: [[ kfst  ->> g (fst pair) as p1 ]]
          :: TelAppend (f (snd pair)) tenv' }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  ->>  cpair as pair ]]
        :: [[ kfst  ->> g (fst pair) as p1 ]]
        :: TelAppend (f (snd pair)) tenv' }}
      p2
      {{ [[ NTNone  ->>  cpair as pair ]]
          :: [[ kfst  ->> g (fst pair) as p1 ]]
          :: TelAppend (Nil) tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
      {{ [[ kfst  ->> g (fst cpair) as p1 ]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; eapply CompileSeq; try eassumption.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
Qed.

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
  intros; eapply CompileSeq; try eassumption.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
Qed.

Ltac hoare :=
  match goal with
  | _ => progress intros
  | [  |- {{ _ }} (Seq _ _) {{ _ }} ∪ {{ _ }} // _ ] => eapply CompileSeq; try eassumption
  end.
