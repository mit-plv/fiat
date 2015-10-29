Require Export
        Coq.Strings.String
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.Extraction.External.External.
Require Import
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.AllExternal.

Global Open Scope string_scope.

Ltac compile_simple_internal env cmp ext :=
  match cmp with
  | ret (SCA ?av (?op ?lhs ?rhs)) => let facade_op := translate_op op in compile_binop av facade_op lhs rhs ext
  | ret (@bool2val ?av (?op ?lhs ?rhs)) => let facade_op := translate_op op in compile_binop av facade_op lhs rhs ext
  | ret (@bool2val ?av (@dec2bool _ _ (?op ?lhs ?rhs))) => let facade_op := translate_op op in compile_binop av facade_op lhs rhs ext
  | ret (SCA _ ?w) => compile_constant w; compile_do_side_conditions
  | ret (SCA ?av ?w) => compile_read (SCA av w) ext; compile_do_side_conditions
  | ret (SCA ?av (?f ?w)) => compile_external_call_SCA av env f w ext
  | (if ?t then ?tp else ?fp) => compile_if t tp fp
  end.

Hint Rewrite WrapComp_W_rewrite : compile_simple_db.

Ltac compile_simple name cmp :=
  debug "Compiling simple pattern";
  autorewrite with compile_simple_db;  (* Rewrite using user-provided lemmas *)
  match_ProgOk ltac:(fun prog pre post ext env => (* Recapture cmp after rewriting *)
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s ?cmp (fun _ => ?tenv)) => compile_simple_internal env cmp ext
                       end).

Ltac compile_simple_in_place_internal env cmp cmp' tenv ext :=
  match cmp' with
  | (if ?t then ?tp else ?fp) => compile_if_in_place t tp fp
  | _ => fail "compile_simple_internal can't compile this:" cmp cmp' tenv ext
  end.

Ltac compile_simple_in_place name cmp cmp' :=
  debug "Compiling simple pattern";
  autorewrite with compile_simple_db;  (* Rewrite using user-provided lemmas *)
  match_ProgOk ltac:(fun prog pre post ext env => (* Recapture cmp after rewriting *)
                       match constr:(pre, post) with
                       | ([[`?k <~~ ?cmp as _]] :: ?tenv, [[`?k <~~ ?cmp' as _]] :: ?tenv) => compile_simple_in_place_internal env cmp cmp' tenv ext
                       end).

Ltac compile_do_unwrap_W val :=
  progress repeat match goal with
  | [ H: WrapComp_W _ ↝ val |- _ ] =>
    let eqn := fresh in
    destruct (WrapComp_W_computes_to H) as [? (? & eqn)];
      rewrite eqn in *; clear eqn H
  end.

Ltac compile_do_unwrap type wrapper key cmp tail val :=
  lazymatch type with
  | W => compile_do_unwrap_W val
  | _ => fail 1 "Don't know how to unwrap" type
  end;
  let wrapper_head := head_constant wrapper in
  cbv beta iota delta [WrappedCons wrapper_head].

(*! FIXME: Why is this first [ ... | fail] thing needed? If it's removed then the lazy match falls through *)
Ltac compile_ProgOk p pre post ext env :=
  is_evar p;
  lazymatch constr:(pre, post, ext) with
  | (_,                           (@WrappedCons _ ?T ?wrapper ?k ?cmp ?tl) ?v, _) => first [compile_do_unwrap T wrapper k cmp tl v | fail ]
  | (Cons ?k ?cmp _,              Cons ?k ?cmp _,                              _) => first [compile_do_chomp k | fail ]
  | (Cons (Some ?k) ?cmp _,       Cons None ?cmp _,                            _) => first [compile_dealloc k cmp | fail ]
  | (_,                           Cons None ?cmp ?tl,                          _) => first [compile_do_alloc cmp tl | fail ]
  | (_,                           Cons ?k (Bind ?compA ?compB) ?tl,            _) => first [compile_do_bind k compA compB tl | fail ]
  | (?tenv,                       Cons (Some ?k) ?cmp (fun _ => ?tenv),           _) => first [compile_simple k cmp | fail ]
  | ([[`?k <~~ ?cmp as _]] :: ?tenv, [[`?k <~~ ?cmp' as _]] :: ?tenv,                _) => first [compile_simple_in_place k cmp cmp' | fail ]
  | (?tenv,                       Cons ?k ?cmp ?tl,                            _) => first [compile_do_cons | fail ] (* FIXME *)
  | (?tenv,                       ?tenv,                                       _) => first [compile_skip | fail ]
  end.

Ltac is_pushable_head_constant f :=
  let hd := head_constant f in
  match hd with
  | Cons => fail 1
  | _ => idtac
  end.

Ltac compile_rewrite :=
  match goal with
  (*! FIXME Why is setoid needed here? !*)
  | [  |- appcontext[if ?b then ?x else ?y] ] => is_dec b; setoid_rewrite (dec2bool_correct b x y)
  | [  |- appcontext[?f (if ?b then ?x else ?y)] ] => is_pushable_head_constant f; setoid_rewrite (push_if f x y b)
  end.

Definition IsFacadeProgramImplementing {av} cmp env prog :=
  {{ @Nil av }}
    prog
  {{ [[`"ret" <~~ cmp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env.

Definition FacadeProgramImplementing {av} cmp env :=
  sigT (@IsFacadeProgramImplementing av cmp env).

Notation "'Facade' 'program' 'implementing' cmp 'with' env" :=
  (FacadeProgramImplementing cmp env) (at level 0).

Ltac start_compiling :=
  match goal with
  | [  |- FacadeProgramImplementing _ ?env ] =>
    unfold FacadeProgramImplementing, IsFacadeProgramImplementing; econstructor
  end.

Ltac compile_step :=
  idtac;
  match goal with
  | _ => start_compiling
  | _ => compile_rewrite
  | _ => compile_do_side_conditions
  | _ => match_ProgOk compile_ProgOk
  end.

