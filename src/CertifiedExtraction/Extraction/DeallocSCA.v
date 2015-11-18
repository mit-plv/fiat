Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Basics.

Lemma CompileDeallocSCA:
  forall {av} (env : Env av) k (compSCA: Comp W) tail tail' ext prog,
    {{ [[compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  learn (SameValues_Dealloc_SCA _ _ _ _ _ H0);
  SameValues_Facade_t.
Qed.

Lemma CompileExtendLifetime:
  forall {av A} {env ext} (k: NameTag av A) comp tenv tenv' prog dealloc,
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      prog
    {{ [[k <~~ comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv' kk }}
      dealloc
    {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      (Seq prog dealloc)
    {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.
