Require Export
        Coq.Strings.String
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.Extraction.External.External.
Require Import
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.AllExternal.

Global Open Scope string_scope.

Ltac compile_do_use_transitivity_to_handle_head_separately :=
  (* NOTE: this is a very risky rule; it doesn't make much sense to apply it
     unless one has a good way to handle the first goal that it produces. *)
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(post) with
                       | Cons ?k _ _ =>
                         match constr:(pre) with
                         | context[k] => fail 1 "Head variable appears in pre-condition"
                         | _ => apply ProgOk_Transitivity_Cons
                         end
                       end).

Ltac compile_do_extend_scalar_lifetime :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre) with
                       | @Cons _ W ?k _ _ =>
                         match constr:(post, ext) with
                         | context[k] => fail 1 "Head variable appears in post-condition"
                         | _ => apply CompileDeallocSCA_discretely; [ compile_do_side_conditions.. | ]
                         end
                       end).

(* Ltac case_unifiable x y when_unifiable unless_unifiable := *)
(*   match goal with *)
(*   | _ => let pr := constr:(eq_refl x : x = y) in first [ when_unifiable | fail 1 ] *)
(*   | _ => unless_unifiable *)
(*   end. *)

Ltac strip_useless_binder tenv :=
  match constr:(tenv) with
  | (fun _ => ?tenv) => let tenv := strip_useless_binder tenv in constr:(tenv)
  | _ => constr:(tenv)
  end.

Ltac call_tactic_after_moving_head_binding_to_separate_goal continuation :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, Cons _ _ ?tenv') =>
              let tenv' := strip_useless_binder tenv' in
              let pr := constr:(eq_refl tenv : tenv = tenv') in
              first [ continuation | fail 1 ]
            | _ => compile_do_use_transitivity_to_handle_head_separately; [ continuation | ]
            end).

(** The compile_simple* tactics handle simple gallina forms *)

Ltac check_type expr type :=
  match type of expr with
  | ?t => let pr := constr:(eq_refl t: t = type) in idtac
  end.

Ltac is_word w :=
  check_type w W.

Ltac compile_simple_internal av env cmp ext :=
  match cmp with
  | ret (?op ?lhs ?rhs) => is_word (op lhs rhs); let facade_op := translate_op op in compile_binop facade_op lhs rhs ext
  | ret (bool2w (?op ?lhs ?rhs)) => let facade_op := translate_op op in compile_binop facade_op lhs rhs ext
  | ret (bool2w (@dec2bool _ _ (?op ?lhs ?rhs))) => let facade_op := translate_op op in compile_binop facade_op lhs rhs ext
  | ret ?w => is_word w; compile_constant w; compile_do_side_conditions
  | ret ?w => is_word w; compile_read (SCA av w) ext; compile_do_side_conditions
  | ret (?f ?w) => is_word w; compile_external_call_SCA av env f w ext
  | (if ?t then ?tp else ?fp) => compile_if t tp fp
  end.

Ltac compile_simple_ProgOk prog pre post ext env :=
  match constr:(pre, post) with
  | (?tenv, Cons (av := ?av) ?s ?cmp (fun _ => ?tenv)) => compile_simple_internal av env cmp ext
  end.

Ltac compile_simple_same_tenv :=
  (* FIXME remove autorewrite with compile_simple_db; (* Rewrite using user-provided lemmas *) *)
  idtac; match_ProgOk compile_simple_ProgOk. (* Recapture cmp after rewriting *)

Ltac compile_simple :=
  debug "Compiling simple pattern";
  call_tactic_after_moving_head_binding_to_separate_goal compile_simple_same_tenv.

(** The compile_simple_inplace* tactic do roughly the same, but modifying an
    existing binding: *)

Ltac compile_simple_inplace_internal av env cmp cmp' ext :=
  match cmp' with
  | (if ?t then ?tp else ?fp) => compile_if_in_place t tp fp
  end.

Ltac compile_simple_inplace_ProgOk prog pre post ext env :=
  match constr:(pre, post) with
  | (Cons ?s ?cmp ?tenv, Cons (av := ?av) ?s ?cmp' ?tenv') => compile_simple_inplace_internal av env cmp cmp' ext
  end.

Ltac compile_simple_inplace :=
  debug "Compiling simple pattern in place";
  (* FIXME remove autorewrite with compile_simple_db; (* Rewrite using user-provided lemmas *) *)
  match_ProgOk compile_simple_inplace_ProgOk. (* Recapture cmp after rewriting *)

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
  rewrite (SameValues_Fiat_Bind_TelEq k compA compB tl).

Ltac compile_do_alloc cmp tail :=
  let name := gensym "v" in
  debug "Naming nameless head variable";
  apply (ProgOk_Transitivity_Name (k := name)).

Ltac compile_skip :=
  debug "Compiling empty program";
  apply CompileSkip.

(*! FIXME: The [ ... | fail] thing is needed: when removed the lazy match sometimes falls through *)
Ltac compile_ProgOk p pre post ext env :=
  is_evar p;
  lazymatch constr:(pre, post) with
  (** Abstract manipulations **)
  | (?tenv, ?tenv) => (* Empty program (side condition of a general lemma) *)
    first [compile_skip | fail ]
  | (Cons ?k ?cmp _, Cons ?k ?cmp _) => (* Chomp rule *)
    first [compile_do_chomp k | fail ]
  | (Cons (Some ?k) ?cmp _, Cons None ?cmp _) => (* Deallocation of head variable *)
    first [compile_dealloc k cmp | fail ]
  | (_, Cons None ?cmp ?tl) => (* Program does deallocation + something else; split *)
    first [compile_do_alloc cmp tl | fail ]

  (** Fiat manipulations **)
  | (_, Cons ?k (Bind ?compA ?compB) ?tl) => (* Bindings *)
    first [compile_do_bind k compA compB tl | fail ]

  (** Concrete compilation **)
  | _ => match goal with
        | _ => (* Direct assignment *)
          (lazymatch constr:(pre, post) with
            | ([[`?k <~~ ?cmp as _]] :: ?tenv, [[`?k <~~ ?cmp' as _]] :: ?tenv') => (* In place modifications *)
              first [ compile_simple_inplace | fail ]
            | (?tenv, Cons (Some ?k) ?cmp ?tenv') => (* Assignments to new variables *)
              first [ compile_simple | fail ]
            end)
        | _ => (* Fallback abstract manipulation *)
          (match goal with
           | _ => compile_do_extend_scalar_lifetime
           end)
        end
  end.

Ltac is_pushable_head_constant f :=
  let hd := head_constant f in
  match hd with
  | Cons => fail 1
  | _ => idtac
  end.

Ltac compile_rewrite p pre post ext env :=
  match post with
  (*! FIXME Why is setoid needed here? !*)
  | appcontext[if ?b then ?x else ?y] => is_dec b; setoid_rewrite (dec2bool_correct b x y)
  | appcontext[?f (if ?b then ?x else ?y)] => is_pushable_head_constant f; setoid_rewrite (push_if f x y b)
  end.

Definition IsFacadeProgramImplementing `{FacadeWrapper (Value av) A} (cmp: Comp A) env prog :=
  {{ @Nil av }}
    prog
  {{ [[`"ret" <~~ cmp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env.

Definition FacadeProgramImplementing `{FacadeWrapper (Value av) A} cmp env :=
  sigT (IsFacadeProgramImplementing cmp env).

Notation "'Facade' 'program' 'implementing' cmp 'with' env" :=
  (FacadeProgramImplementing cmp env) (at level 0).

Ltac start_compiling :=
  match goal with
  | [  |- FacadeProgramImplementing _ ?env ] =>
    unfold FacadeProgramImplementing, IsFacadeProgramImplementing; econstructor
  end.

Ltac compile_step_with worker :=
  idtac;
  match goal with
  | _ => start_compiling
  | _ => compile_do_side_conditions
  | _ => match_ProgOk compile_rewrite
  | _ => match_ProgOk worker
  | _ => progress (subst || intros)
  end.

Ltac compile_step :=
  compile_step_with compile_ProgOk.
