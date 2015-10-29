Require Import
        CertifiedExtraction.Extraction.Core.

Lemma CompileDeallocSCA:
  forall {av} (env : Env av) k compSCA tail tail' ext prog,
    AlwaysComputesToSCA compSCA ->
    {{ [[compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[k <~~ compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  apply SameValues_Dealloc_SCA in H1;
  SameValues_Facade_t.
Qed.

Lemma CompileDeallocSCA_ret:
  forall {av} (env : Env av) k v tail tail' ext
    prog,
    {{ [[(ret (SCA _ v)) as kk]]::(tail kk)}}
      prog
    {{ [[(ret (SCA _ v)) as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[k <~~ ret (SCA _ v) as kk]]::(tail kk)}}
      prog
    {{ [[ret (SCA _ v) as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  intros; apply CompileDeallocSCA;
  SameValues_Facade_t.
Qed.

Lemma CompileDeallocSCA_discretely :
  forall {av} tenv tenv' ext env k v prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[k <-- SCA av v as _]] :: tenv }} prog {{ [[k <-- SCA av v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[k <-- SCA av v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.
