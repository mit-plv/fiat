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

Ltac compile_do_cons :=
  debug "Moving head of Cons to separate goal";
  apply ProgOk_Transitivity_Cons.

Ltac compile_do_chomp key :=
  debug "Applying chomp rule";
  match key with
  | @Some _ _ => apply ProgOk_Chomp_Some
  | @None _   => apply ProgOk_Chomp_None
  end; intros; computes_to_inv.

Ltac compile_do_bind k compA compB tl :=
  debug "Transforming Fiat-level bind into telescope-level Cons";
  first [rewrite (SameValues_Fiat_Bind_TelEq k compA compB tl) | (* FIXME use a smarter procedure for rewriting here *)
         rewrite (SameValues_Fiat_Bind_TelEq_W k compA compB tl)].

Ltac compile_do_alloc cmp tail :=
  let name := gensym "v" in
  debug "Naming nameless head variable";
  apply (ProgOk_Transitivity_Name (k := name)).

Ltac compile_skip :=
  debug "Compiling empty program";
  apply CompileSkip.

Ltac clean_DropName_in_ProgOk :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       try (is_dirty_telescope pre; clean_telescope pre ext);
                       try (is_dirty_telescope post; clean_telescope post ext)).
