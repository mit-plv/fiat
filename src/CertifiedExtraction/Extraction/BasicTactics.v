Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Basics.

Ltac compile_constant value :=
  debug "-> constant value";
  apply CompileConstant.

Ltac compile_read value ext :=
  debug "-> read from the environment";
  let location := find_fast value ext in
  match location with
  | Some ?k => apply (CompileRead (var := k))
  end.

Ltac assoc_telescope tel needle :=
  match tel with (* Note that this may return None when a binding in fact exists *)
  | Cons (NTSome ?k) ?v _ => let eq := constr:(eq_refl k : k = needle) in constr:(Some v)
  | Cons _ _ (fun _ => ?t) => let ret := assoc_telescope t needle in constr:(ret)
  | _ => None
  end.

Ltac clean_DropName_in_ProgOk :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       try (is_dirty_telescope pre; PreconditionSet_t; clean_telescope pre ext);
                       try (is_dirty_telescope post; PreconditionSet_t; clean_telescope post ext)).

Ltac hoare :=
  match goal with
  | _ => progress intros
  | [  |- {{ _ }} (Seq _ _) {{ _ }} ∪ {{ _ }} // _ ] => eapply CompileSeq; try eassumption
  end.
