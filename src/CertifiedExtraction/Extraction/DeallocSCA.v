Require Import
        CertifiedExtraction.Extraction.Core.

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

(* Lemma CompileDeallocSCA_ret: *)
(*   forall {av} (env : Env av) k (v: W) tail tail' ext *)
(*     prog, *)
(*     {{ [[(ret v) as kk]]::(tail kk)}} *)
(*       prog *)
(*     {{ [[(ret v) as kk]]::(tail' kk) }} ∪ {{ ext }} // env -> *)
(*     {{ [[k <~~ ret v as kk]]::(tail kk)}} *)
(*       prog *)
(*     {{ [[ret v as kk]]::(tail' kk) }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   intros; apply CompileDeallocSCA; *)
(*   SameValues_Facade_t. *)
(* Qed. *)

Lemma CompileDeallocSCA_discretely :
  forall {av} (tenv tenv': Telescope av) ext env k (v: W) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[`k <-- v as _]] :: tenv }} prog {{ [[`k <-- v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k <-- v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.
