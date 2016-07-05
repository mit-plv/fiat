Require Import
        CertifiedExtraction.Extraction.Extraction.

Definition Any := { x: W | True }%comp.

Definition FAny {av} : AxiomaticSpec av.
Proof. refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ exists w, ret = SCA av w
    |}; spec_t. Defined.

Lemma Any_characterization:
  forall x : W, Any ↝ x.
Proof. constructor. Qed.

Hint Immediate Any_characterization : call_helpers_db.

Lemma CompileCallAny:
  forall {av} (env : GLabelMap.t (FuncSpec av)),
  forall fpointer tenv,
    GLabelMap.MapsTo fpointer (Axiomatic FAny) env ->
    forall var ext,
      var ∉ ext ->
      NotInTelescope var tenv ->
      {{ tenv }}
        (DFacade.Call var fpointer nil)
      {{ [[ ` var ~~> Any as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call); facade_eauto.
Qed.
