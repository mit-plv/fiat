Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Basics.

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

Lemma CompileDeallocW:
  forall {av} (env : Env av) k (compSCA: Comp W) tail tail' ext prog,
    {{ [[compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  eauto using CompileDeallocSCA.
Qed.

Lemma CompileExtendLifetime:
  forall {av A} {env ext} (k: NameTag av A) comp tenv tenv' prog dealloc,
    {{ [[k ~~> comp as kk]] :: tenv kk }}
      prog
    {{ [[k ~~> comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k ~~> comp as kk]] :: tenv' kk }}
      dealloc
    {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k ~~> comp as kk]] :: tenv kk }}
      (Seq prog dealloc)
    {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.
