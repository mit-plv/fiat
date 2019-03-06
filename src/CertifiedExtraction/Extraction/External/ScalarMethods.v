Require Import
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.GenericMethods.

Require Import Coq.Lists.List.

Lemma CompileCallFacadeImplementationWW:
  forall {av} {env} fWW,
  forall fpointer varg (arg: W) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationWW av fWW)) env ->
    forall vret ext,
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      StringMap.MapsTo varg (wrap arg) ext ->
      {{ tenv }}
        Call vret fpointer (varg :: nil)
      {{ [[ `vret ->> (fWW arg) as _]]:: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationWW_full:
  forall {av} {env} fWW,
  forall fpointer varg (arg: W) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationWW av fWW)) env ->
    forall vret ext p,
      vret ∉ ext ->
      varg ∉ ext ->
      NotInTelescope vret tenv ->
      NotInTelescope varg tenv ->
      vret <> varg ->
      {{ tenv }}
        p
      {{ [[ `varg ->> arg as _]]:: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq p (Call vret fpointer (varg :: nil))
      {{ [[ `vret ->> (fWW arg) as _]]:: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.
