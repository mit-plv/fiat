Require Import
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.ExtendedLemmas.

Lemma CompileConstant:
  forall {av} name env w ext (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    {{ tenv }}
      (Assign name (Const w))
    {{ [[`name <-- w as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
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
    {{ [[`name <-- val as _]]::tenv }} ∪ {{ ext }} // env.
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

Lemma ProgOk_Transitivity_Cons :
  forall {av A} env ext t1 t2 prog1 prog2 (k: NameTag av A) (v: Comp A),
    {{ t1 }}                     prog1      {{ [[k <~~ v as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k <~~ v as _]]::t1 }}      prog2      {{ [[k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                Seq prog1 prog2 {{ [[k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_Name :
  forall `{FacadeWrapper (Value av) A} k env ext t1 t2 prog1 prog2 (v: Comp A),
    {{ t1 }}                          prog1        {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as kk]]::t2 kk }}      prog2        {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                      Seq prog1 prog2  {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_Name' :
  forall `{FacadeWrapper (Value av) A} k env ext t1 t2 prog1 prog2 (v: Comp A),
    {{ t1 }}                     prog1        {{ [[`k <~~ v as _]]::t1 }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as _]]::t1 }}     prog2        {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
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
    {{ t1 }} prog1 {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }} prog1 {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  eauto using SameValues_Dealloc_SCA.
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

Ltac hoare :=
  match goal with
  | _ => progress intros
  | [  |- {{ _ }} (Seq _ _) {{ _ }} ∪ {{ _ }} // _ ] => eapply CompileSeq; try eassumption
  end.
