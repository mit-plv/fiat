Require Export
        Coq.Strings.String
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.Extraction.External.External.
Require Import
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.Extraction.Internal.

Global Open Scope string_scope.

Ltac compile_do_use_transitivity_to_handle_head_separately :=
  (* NOTE: this is a very risky rule; it doesn't make much sense to apply it
     unless one has a good way to handle the first goal that it produces. *)
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(post) with
                       | Cons ?k _ _ =>
                         match constr:(pre) with
                         | Cons k _ _ => (apply ProgOk_Transitivity_First || apply ProgOk_Transitivity_First_defunc)
                         | context[k] => fail 1 "Head variable appears in pre-condition"
                         | _ => (apply ProgOk_Transitivity_Cons || apply ProgOk_Transitivity_Cons_defunc)
                         end
                       end).

Ltac strip_useless_binder tenv :=
  match constr:(tenv) with
  | (fun _ => ?tenv) => let tenv := strip_useless_binder tenv in constr:(tenv)
  | _ => constr:(tenv)
  end.

Ltac call_tactic_after_moving_head_binding_to_separate_goal continuation :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
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

Ltac translate_op gallina_op :=
  let hd := head_constant gallina_op in
  match hd with
  | @Word.wplus => constr:(@inl IL.binop IL.test IL.Plus)
  | @Word.wminus => constr:(@inl IL.binop IL.test IL.Minus)
  | @Word.wmult => constr:(@inl IL.binop IL.test IL.Times)
  | @Word.weqb => constr:(@inr IL.binop IL.test IL.Eq)
  | @IL.weqb => constr:(@inr IL.binop IL.test IL.Eq)
  | @IL.wneb => constr:(@inr IL.binop IL.test IL.Ne)
  | @IL.wltb => constr:(@inr IL.binop IL.test IL.Lt)
  | @IL.wleb => constr:(@inr IL.binop IL.test IL.Le)
  | @Word.wlt_dec => constr:(@inr IL.binop IL.test IL.Lt)
  | _ => fail 1 "Unknown operator" gallina_op
  end.

Ltac compile_binop facade_op lhs rhs ext :=
  let av := av_from_ext ext in
  let vlhs := find_fast (wrap (FacadeWrapper := FacadeWrapper_SCA (av := av)) lhs) ext in
  let vrhs := find_fast (wrap (FacadeWrapper := FacadeWrapper_SCA (av := av)) rhs) ext in
  lazymatch constr:((vlhs, vrhs)) with
  | (Some ?vlhs, Some ?vrhs) =>
    apply (BinExpr.CompileBinopOrTest (var1 := vlhs) (var2 := vrhs) facade_op)
  | (Some ?vlhs, None) =>
    let vrhs := gensym "r" in
    apply (BinExpr.CompileBinopOrTest_left (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, Some ?vrhs) =>
    let vlhs := gensym "l" in
    apply (BinExpr.CompileBinopOrTest_right (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, None) =>
    let vlhs := gensym "l" in
    let vrhs := gensym "r" in
    apply (BinExpr.CompileBinopOrTest_full (var1 := vlhs) (var2 := vrhs) facade_op)
  end.

Ltac compile_external_call_SCA av env fWW arg ext :=
  let varg := find_fast arg ext in
  match varg with
  | Some ?varg =>
    apply (CompileCallFacadeImplementationWW (varg := varg))
  | None =>
    let varg := gensym "arg" in
    apply (CompileCallFacadeImplementationWW_full (varg := varg))
  end; ensure_all_pointers_found.

Ltac is_pushable_head_constant f :=
  let hd := head_constant f in
  match hd with
  | @Cons => fail 1
  | _ => idtac
  end.

(* Ltac compile_chomp := *)
(*   match_ProgOk *)
(*     ltac:(fun prog pre post ext env => *)
(*             match pre with    (* NOTE could be generalized beyond the first binding *) *)
(*             | Cons ?k ?v ?tenv => *)
(*               match post with *)
(*               | Cons k v _ => fail 1 *)
(*               | context[Cons k v _] => move_to_front k *)
(*               end *)
(*             end). *)

Ltac _compile_chomp :=         (* This is a weak version of the real compile_chomp, which is too slow *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (Cons (NTSome ?k) ?v ?tenv, Cons NTNone ?v' ?tenv') =>
              unify v v'; apply miniChomp'
            | (Cons ?k ?v ?tenv, Cons ?k' ?v' ?tenv') =>
              unify k k'; unify v v';
              match k with
              | NTNone => apply ProgOk_Chomp_None
              | _ => apply ProgOk_Chomp_Some
              end
            | (Cons ?k ?v ?tenv, Cons _ _ (fun _ => Cons ?k' ?v' ?tenv')) =>
              unify k k'; unify v v';
              match k with
              | NTNone => apply ProgOk_Chomp_None_snd
              | _ => apply ProgOk_Chomp_Some_snd
              end
            end).


Ltac __compile_prepare_chomp tenv tenv' :=
  match tenv with
  | Cons ?k ?v _ =>
    match tenv' with
    | Cons ?k' ?v' _ =>
      unify k k'; unify v v';
      fail 1 (* Nothing to do: can already chomp *)
    | Cons _ _ (fun _ => ?tail) =>
      unify tenv tail; idtac;
      fail 1 (* This is a job for deallocation, not chomping *)
    | context[Cons k v _] =>
      move_to_front k
    end
  end.

Ltac _compile_prepare_chomp :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            is_evar prog;
            first [ __compile_prepare_chomp pre post
                  | __compile_prepare_chomp post pre ]).

Ltac _compile_rewrite_bind :=
  (* setoid_rewrite at the speed of light *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | context[Cons ?k (ret _) ?tail] =>
              first [ useless_binder tail; fail 1 |
                      match k with
                      | NTSome _ => setoid_rewrite Propagate_ret
                      | NTNone => setoid_rewrite Propagate_anonymous_ret
                      end ]
            | context[Cons _ (Bind _ _) _] => setoid_rewrite SameValues_Fiat_Bind_TelEq
            end).

Ltac _compile_rewrite_if :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             match post with
             | appcontext [if ?b then ?x else ?y] =>
               is_dec b; first [ rewrite (dec2bool_correct b x y)
                               | setoid_rewrite (dec2bool_correct b x y) ]
             | appcontext [?f (if ?b then ?x else ?y)] =>
               is_pushable_head_constant f; first [ rewrite (push_if f x y b)
                                                  | setoid_rewrite (push_if f x y b) ]
             end).

Ltac compile_constant value :=
  debug "-> constant value";
  apply CompileConstant.

Ltac compile_read value ext :=
  debug "-> read from the environment";
  let location := find_fast value ext in
  match location with
  | Some ?k => apply (CompileRead (var := k))
  end.

Ltac _compile_skip :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?tenv, ?tenv') => not_evar tenv; not_evar tenv'; unify tenv tenv'; apply CompileSkip
            end).

Ltac _compile_if :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (_, Cons _ (if _ then _ else _) _) =>
              let vtest := gensym "test" in
              apply (CompileIf (tmp := vtest))
            end).

Ltac compile_simple_internal av env cmp ext :=
  match cmp with
  | ret (?op ?lhs ?rhs) => is_word (op lhs rhs); let facade_op := translate_op op in compile_binop facade_op lhs rhs ext
  | ret (bool2w (?op ?lhs ?rhs)) => let facade_op := translate_op op in compile_binop facade_op lhs rhs ext
  | ret (bool2w (@dec2bool _ _ (?op ?lhs ?rhs))) => let facade_op := translate_op op in compile_binop facade_op lhs rhs ext
  | ret ?w => is_word w; compile_constant w; compile_do_side_conditions (* FIMXE Check these uses of do_side_conditions *)
  | ret ?w => is_word w; compile_read (SCA av w) ext; compile_do_side_conditions
  | ret (?f ?w) => is_word w; compile_external_call_SCA av env f w ext
  end.

Ltac compile_simple_same_tenv :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?tenv, Cons (av := ?av) ?s ?cmp (fun _ => ?tenv)) => compile_simple_internal av env cmp ext
            end).

Ltac compile_simple :=
  debug "Compiling simple pattern";
  call_tactic_after_moving_head_binding_to_separate_goal compile_simple_same_tenv.

(** The compile_simple_inplace tactic does roughly the same, but modifying an
    existing binding: *)

Ltac compile_simple_inplace :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons (NTSome ?s) (ret (?op ?a' ?b)) ?tenv' =>
              match pre with
              | context[Cons (NTSome ?s) (ret ?a) _] =>
                unify a a';
                is_word (op a b);
                let facade_op := translate_op op in
                move_to_front s;
                first [ apply (CompileBinopOrTest_right_inPlace_tel facade_op)
                      | apply (CompileBinopOrTest_right_inPlace_tel_generalized facade_op) ]
              end
            end).

Ltac _compile_map :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vhead := gensym "head" in
            let vhead' := gensym "head'" in
            let vtest := gensym "test" in
            let vtmp := gensym "tmp" in
            match constr:((pre, post)) with
            | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (revmap _ ?seq')) ?tenv') =>
              unify seq seq';
                first [
                    apply (CompileMap_SCA seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)) |
                    apply (CompileMap_ADT seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)) ]
            end).

Ltac _compile_fold :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtest := gensym "test" in
            let vhead := gensym "head" in
            match constr:((pre, post)) with
            | ([[`?vinit ~~> ?init as _]] :: [[`?vseq ->> ?seq as _]] :: ?tenv, [[`?vret ~~> fold_left _ ?seq ?init as _]] :: ?tenv') =>
              apply (CompileLoop seq init (vtest := vtest) (vhead := vhead))
            | ([[`?vinit ->> ?init as _]] :: [[`?vseq ->> ?seq as _]] :: ?tenv, [[`?vret ->> fold_left _ ?seq ?init as _]] :: ?tenv') =>
              apply (CompileLoop_ret seq init (vtest := vtest) (vhead := vhead))
            | ([[`?vseq ->> ?seq as _]] :: ?tenv, [[`?vret ~~> fold_left _ ?seq _ as _]] :: ?tenv') =>
              apply (CompileLoopAlloc (vtest := vtest) (vhead := vhead))
            | ([[`?vseq ->> ?seq as _]] :: ?tenv, [[`?vret ->> fold_left _ ?seq _ as _]] :: ?tenv') =>
              apply (CompileLoopAlloc_ret (vtest := vtest) (vhead := vhead))
            end).

Ltac _compile_destructor_unsafe vtmp tenv tenv' :=
  (apply CompileDeallocW_discretely ||
   first [ unify tenv tenv';
           apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp))
         | eapply CompileSeq;
           [ apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) | ] ]);
  try compile_do_side_conditions.

Ltac _compile_destructor :=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              let vtmp := gensym "tmp" in
              match pre with
              | Cons (NTSome ?k) ?v (fun _ => ?tenv) =>
                match tenv with
                | context[post] => (* post is a suffix of pre *)
                  _compile_destructor_unsafe vtmp tenv post
                | _ => (* post is pre *)
                  unify tenv post; _compile_destructor_unsafe vtmp tenv post
                | _ => let is_sca := is_sca_comp v in
                      lazymatch is_sca with
                      | true => (match post with
                                | context[k] => fail 1
                                | _ => apply CompileDeallocW_discretely
                                end)
                      | false => (lazymatch v with
                                  | ret ?vv => first [ tenv_mentions_fast post vv; fail 1
                                                    | _compile_destructor_unsafe vtmp tenv post ]
                                  | ?vv => first [ tenv_mentions_fast post vv; fail 1
                                                | _compile_destructor_unsafe vtmp tenv post ]
                                  end)
                      end
                end
              end).

Ltac _compile_mutation :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | [[`?s ->> ?f _ _ as _]]::?tenv =>
              let arg := gensym "arg" in
              let tmp := gensym "tmp" in
              let arg_type := first_arg f in
              let uses_sca := unifiable arg_type W in
              lazymatch uses_sca with
              | true => match pre with
                       | context[Cons (NTSome s) _ _] =>
                         move_to_front s;
                           first [ eapply (CompileCallFacadeImplementationOfMutation_SCA (vtmp:=DummyArgument tmp))
                                 | eapply (CompileCallFacadeImplementationOfMutation_SCA_Replace (varg:=arg) (vtmp:=DummyArgument tmp))
                                 | eapply (CompileCallFacadeImplementationOfMutation_SCA_Replace_strong (varg:=arg) (vtmp:=DummyArgument tmp))
                                 | eapply (CompileCallFacadeImplementationOfMutation_SCA_Replace_strong' (varg:=arg) (vtmp:=DummyArgument tmp))
                                 | fail 1 ]
                       | tenv => eapply (CompileCallFacadeImplementationOfMutation_SCA_Alloc (varg:=arg) (vtmp:=DummyArgument tmp))
                       end
              | false => match pre with
                        | context[Cons (NTSome s) _ _] =>
                          move_to_front s;
                            first [ eapply (CompileCallFacadeImplementationOfMutation_ADT (vtmp:=DummyArgument tmp))
                                  | eapply (CompileCallFacadeImplementationOfMutation_ADT_Replace (varg:=arg) (vtmp:=DummyArgument tmp))
                                  | eapply (CompileCallFacadeImplementationOfMutation_ADT_Replace_strong (varg:=arg) (vtmp:=DummyArgument tmp))
                                  | eapply (CompileCallFacadeImplementationOfMutation_ADT_Replace_strong' (varg:=arg) (vtmp:=DummyArgument tmp))
                                  | fail 1 ]
                        | tenv => eapply (CompileCallFacadeImplementationOfMutation_ADT_Alloc (varg:=arg) (vtmp:=DummyArgument tmp))
                        end
              end; ensure_all_pointers_found
            end).

Ltac _compile_constructor :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?tenv, [[?s ->> ?adt as _]]::?tenv') =>
              match type of adt with
              | W => fail 1
              | _ => call_tactic_after_moving_head_binding_to_separate_goal
                      ltac:(apply CompileCallFacadeImplementationOfConstructor);
                  ensure_all_pointers_found
              end
            end).

Ltac start_compiling :=
  match goal with
  | |- sigT _ => eexists; intros
  end.

Ltac _compile_early_hook := fail.
Ltac _compile_late_hook := fail.

Ltac _compile_step :=
  match goal with
  | _ => start_compiling
  | _ => progress subst
  | _ => progress intros
  | _ => progress computes_to_inv
  | _ => compile_do_side_conditions
  | _ => _compile_early_hook
  | _ => _compile_rewrite_bind
  | _ => _compile_skip
  | _ => _compile_map
  | _ => _compile_fold
  (* | _ => _compile_CallBagFind *)
  (* | _ => _compile_CallBagInsert *)
  (* | _ => _compile_CallGetAttribute *)
  | _ => _compile_chomp
  | _ => _compile_prepare_chomp
  | _ => _compile_if
  | _ => _compile_mutation
  | _ => _compile_constructor
  | _ => compile_simple
  | _ => compile_simple_inplace
  | _ => _compile_destructor
  | _ => _compile_rewrite_if
  | _ => _compile_late_hook
  (* | _ => progress simpl *)
  end.

Ltac _compile :=
  repeat _compile_step.
