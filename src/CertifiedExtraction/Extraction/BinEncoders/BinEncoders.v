Require Export
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties
        Fiat.CertifiedExtraction.Extraction.BinEncoders.CallRules.CallRules
        Fiat.CertifiedExtraction.Extraction.BinEncoders.RewriteRules.
Unset Implicit Arguments.

Require Import Coq.Lists.List.

Ltac _compile_decide_padding_0 :=
  repeat first [ reflexivity |
                 apply ByteString_transform_padding_0 |
                 eapply encode_word8_Impl_padding_0 |
                 eapply EncodeBoundedNat8_padding_0 |
                 apply fold_encode_list_body_padding_0 |
                 apply encode_list_Impl_EncodeBoundedNat_padding_0 ].

(* FIXME remove coercions? *)
Global Transparent nat_as_word.

Ltac _compile_decide_AllocString_size :=
  unfold nat_as_word;
  match goal with
  | [  |- natToWord ?sz ?z = ?x ^* natToWord ?sz ?y ] =>
    let zz := (eval compute in (NPeano.div z y)) in
    unify x (natToWord sz zz); reflexivity
  end.

Ltac _compile_decide_write8_side_condition_step_omega :=
  repeat match goal with
         | [ n: { _ | _ < _ }%type |- _ ] =>
           let neq := fresh in
           destruct n; simpl in *
         end;
  change (pow2 8) with 256 in *;
  omega.

Create HintDb _compile_decide_write8_side_condition_db.
Hint Rewrite @length_firstn : _compile_decide_write8_side_condition_db.

Ltac _compile_decide_write8_side_condition_step :=
  idtac;
  match goal with
  | [ H := _ |- _ ] => unfold H in *; clear H
  | [  |- context[List.length (Core.byteString (?x))] ] =>
    match x with
    | transform_id => change (length (Core.byteString transform_id)) with 0
    | fst (EncodeBoundedNat _ _) => rewrite EncodeBoundedNat8_length
    | fst (encode_word_Impl _ _) => rewrite encode_word8_Impl_length
    | fst (encode_list_Impl _ _ _) => rewrite encode_list_Impl_EncodeBoundedNat_length
    | fst (fold_left (encode_list_body EncodeBoundedNat) _ _) => rewrite fold_encode_list_body_length
    | transform _ _ => rewrite ByteString_transform_length by _compile_decide_padding_0
    | _ => fail 3 "Unrecognized form" x
    end
  | _ => progress autorewrite with _compile_decide_write8_side_condition_db
  | _ => _compile_decide_write8_side_condition_step_omega
  end.

Ltac _compile_decide_write8_side_condition :=
  progress repeat _compile_decide_write8_side_condition_step.

Ltac _compile_encode_do_side_conditions :=
  match goal with
  | [  |- _ = _ ^* _ ] => _compile_decide_AllocString_size
  | [  |- padding _ = 0 ] => _compile_decide_padding_0
  | [  |- (_ <= _)%nat ] => _compile_decide_write8_side_condition
  end.

Ltac _compile_encode_list :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | appcontext[fold_left (encode_list_body _) (`?lst)] =>
              lazymatch pre with
              | context[Cons (NTSome ?vlst) (ret lst) _] =>
                _compile_LoopMany vlst;
                try rewrite (TelEq_same_wrap (`lst) (lst)) by reflexivity
              end
            end).

Ltac mod_first :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match pre with
            | (Cons _ _ (fun _ => ?tail)) =>
              match post with
              | context[?e] => is_evar e; (unify e tail)
              end
            end).

Ltac keep_first :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | context[?e] => is_evar e; (unify e pre)
            end).

Create HintDb f2f_binencoders_autorewrite_db.
Hint Rewrite @NToWord_of_nat : f2f_binencoders_autorewrite_db.
Hint Rewrite @NToWord_WordToN : f2f_binencoders_autorewrite_db.
Hint Rewrite encode_byte_simplify :  f2f_binencoders_autorewrite_db.
Hint Rewrite EncodeBoundedNat8_simplify :  f2f_binencoders_autorewrite_db.
Hint Rewrite ByteString_transformer_eq_app : f2f_binencoders_autorewrite_db.
Hint Resolve WrapByte_BoundedNat8ToByte_WrapNat8_compat : compile_do_side_conditions_db.
Hint Rewrite @encode_list_as_foldl : f2f_binencoders_autorewrite_db.
Hint Rewrite app_nil_r : f2f_binencoders_autorewrite_db.
Hint Unfold TelAppend : f2f_binencoders_autorewrite_db.
Hint Unfold Enum.Enum_encode : f2f_binencoders_autorewrite_db.

(* Ltac simpl_without_uncaught_exception := *)
(*   (* Avoids an “Uncaught exception: not found” *) *)
(*   set_evars; simpl; subst_evars. *)

Ltac encode_list_body_simpl :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | Cons NTNone (ret (@encode_list_body _ _ ?cache ?transformer _ _ _)) _ =>
              rewrite (encode_list_body_simpl cache transformer)
            end).

Ltac encode_list__cleanup_post_encode_list_as_fold :=
  lazymatch goal with
  | [  |- appcontext[fold_left (@encode_list_body _ _ ?cache ?transformer _)] ] =>
    change_post_into_TelAppend; (* FIXME: Need either this, or a set_evars call; why? *)
    setoid_rewrite (encode_list_post_transform_TelEq_TelAppend cache transformer)
  end.

Ltac _encode_cleanup :=
  match goal with
  | _ => match_ProgOk
          ltac:(fun prog pre post ext env =>
                  match post with
                  | [[ ret (_, _) as _]] :: _ =>
                    apply Propagate_anonymous_ret__fast
                  end)
  | _ => progress simpl
  | _ => encode_list_body_simpl  (* Doesn't work as a rewrite hint *)
  | _ => encode_list__cleanup_post_encode_list_as_fold
  | _ => progress autounfold with f2f_binencoders_autorewrite_db
  | _ => progress autorewrite with f2f_binencoders_autorewrite_db
  | [  |- context[wordToNat (natToWord _ (S ?x))] ] => change (wordToNat (natToWord _ (S x))) with (S x)
  end.

(*  Disable the propagation of rets for this file, since we use them for structure *)
Ltac _compile_rewrite_bind ::= fail.
(*  Disable automatic decompilation for this file (it only works for simple examples with no evars in the post) *)
Ltac _compile_destructor ::= fail.

Arguments NotInTelescope: simpl never.

Tactic Notation "apply_in_body" hyp(H) constr(f) :=
  let H' := fresh in
  pose (f H) as H';
  unfold H in *; clear H;
  rename H' into H.

Definition CompositionDepth (n: nat) := S n.

Ltac _compile_compose :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | [[ ret _ as _ ]] :: [[ ?k ->> _ as _ ]] :: _ =>
              change_post_into_TelAppend;
              first [ eapply CompileCompose |
                      may_alloc k; eapply CompileCompose_init ];
              [ try match goal with
                    | [ H := CompositionDepth _ |- _ ] => apply_in_body H CompositionDepth
                    end.. | ];
              intros
            end).

Ltac _compile_SameWrap :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | [[ ?k ->> BoundedNat8ToByte ?w as _ ]] :: ?tail =>
              rewrite (TelEq_same_wrap (BoundedNat8ToByte w) w)
            end).

Ltac _compile_constant_SCA :=
  may_alloc_head;
  apply CompileConstant_SCA.

Ltac _compile_dealloc_SCA :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtmp := gensym "tmp" in
            lazymatch pre with
            | Cons (NTSome ?k) ?v (fun _ => ?tenv) =>
              lazymatch tenv with
              | context[post] => (* post is a suffix of pre *)
                match type of v with
                | Comp ?t =>
                  let is_sca := constr:(_ : FacadeWrapper W t) in
                  apply CompileDeallocSCA_discretely
                end
              end
            end).

Definition Counted {A} (x: A) := x.

Ltac count_instances head_symbol counter_var :=
  pose 0 as counter_var;
  repeat match goal with
         | [  |- appcontext C [head_symbol ?x] ] =>
           apply_in_body counter_var S;
           let C' := context C[(Counted head_symbol) x] in change C'
         end;
  change (Counted head_symbol) with (head_symbol).

Ltac last_argument fun_appl :=
  lazymatch fun_appl with
  | _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ _ ?x => x
  | _ _ _ _ _ ?x => x
  | _ _ _ _ ?x => x
  | _ _ _ ?x => x
  | _ _ ?x => x
  | _ ?x => x
  | ?x => x
  end.

Fixpoint MakeString base ncopies :=
  match ncopies with
  | O => ""%string
  | S n => String.append base (MakeString base n)
  end.

Ltac _encode_show_progress :=
  try match_ProgOk
      ltac:(fun prog pre post ext env =>
              lazymatch pre with
              | context[@Compose.compose] => fail "In final (deallocation) goals"
              | _ => lazymatch post with
                    | Cons NTNone (ret (Compose.compose _ ?action _ _)) _ =>
                      lazymatch goal with
                      | H := Counted action |- _ => fail "Already counted"
                      | _ => pose (Counted action);
                            let counter := fresh in
                            count_instances @Compose.compose counter;
                            let arg := last_argument action in
                            let steps_left := (eval unfold counter in counter) in
                            (try pose (CompositionDepth 0) as CompositionDepth);
                            lazymatch goal with
                            | H := CompositionDepth _ |- _ =>
                              let indent := (eval compute in (MakeString """" (pred H))) in
                              match steps_left with
                              | 1 => idtac "<infomsg>" indent "-" steps_left "step left:"
                                          "compiling encoder for" arg "...</infomsg>"
                              | _ => idtac "<infomsg>" indent "-" steps_left "steps left:"
                                          "compiling encoder for" arg "...</infomsg>"
                              end
                            end;
                            clear counter
                      end
                    end
              end).

Ltac _encode_trace_progress :=
  debug "--------------------------------------------------------------------------------";
  match goal with
  | |- ?g => debug g
  end.
