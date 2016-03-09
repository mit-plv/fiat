Require Import
        CertifiedExtraction.Extraction.Extraction.

Definition Random := { x: W | True }%comp.

Definition FRandom {av} : AxiomaticSpec av.
Proof. refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ exists w, ret = SCA av w
    |}; spec_t. Defined.

Lemma Random_characterization:
  forall x : W, Random ↝ x.
Proof. constructor. Qed.

Hint Immediate Random_characterization : call_helpers_db.

Lemma CompileCallRandom:
  forall {av} (env : GLabelMap.t (FuncSpec av)),
  forall fpointer tenv,
    GLabelMap.MapsTo fpointer (Axiomatic FRandom) env ->
    forall var ext,
      var ∉ ext ->
      NotInTelescope var tenv ->
      {{ tenv }}
        (DFacade.Call var fpointer nil)
      {{ [[ ` var <~~ Random as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Ltac compile_random :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?tenv, Cons (av := ?av) ?s Random ?tenv') =>
               call_tactic_after_moving_head_binding_to_separate_goal
                 ltac:(apply CompileCallRandom);
                ensure_all_pointers_found
            end).
