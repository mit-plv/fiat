Require Export
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties
        Fiat.CertifiedExtraction.Extraction.BinEncoders.CallRules
        Fiat.CertifiedExtraction.Extraction.BinEncoders.RewriteRules.
Unset Implicit Arguments.

Require Import Coq.Lists.List.

Ltac _encode_IList__rewrite_as_fold :=
  lazymatch goal with (* FIXME make this an autorewrite? *)
  | [  |- appcontext[fold_left (IList.IList_encode'_body ?cache ?transformer _)] ] =>
    change_post_into_TelAppend; (* FIXME: Need either this, or a set_evars call; why? *)
    setoid_rewrite (IList_post_transform_TelEq_TelAppend cache transformer)
  end.

Ltac _encode_IList__compile_loop :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | appcontext[fold_left (IList.IList_encode'_body _ _ _) ?lst] =>
              match pre with
              | context[Cons (NTSome ?vlst) (ret lst) _] =>
                _compile_LoopMany vlst
              end
            end).

Ltac _encode_IList_compile :=
  _encode_IList__rewrite_as_fold;
  [ _encode_IList__compile_loop | idtac.. ].

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
Hint Rewrite @length_of_fixed_length_list : f2f_binencoders_autorewrite_db.
Hint Rewrite @IList.IList_encode'_as_foldl : f2f_binencoders_autorewrite_db.
Hint Rewrite @FixInt_encode_is_copy : f2f_binencoders_autorewrite_db.
Hint Rewrite @IList_encode_bools_is_copy : f2f_binencoders_autorewrite_db.
Hint Rewrite @FixList_is_IList : f2f_binencoders_autorewrite_db.
Hint Rewrite app_nil_r : f2f_binencoders_autorewrite_db.
(* FXIME Hint Rewrite (@IList_encode'_body_simpl DnsMap.cache) : f2f_binencoders_autorewrite_db. *)
Hint Unfold IList.IList_encode : f2f_binencoders_autorewrite_db.
Hint Unfold FixList.FixList_encode : f2f_binencoders_autorewrite_db.
Hint Unfold TelAppend : f2f_binencoders_autorewrite_db.
Hint Unfold Enum.Enum_encode : f2f_binencoders_autorewrite_db.
(* FIXME Hint Unfold encode_question : f2f_binencoders_autorewrite_db. *)
(* FIXME Hint Unfold encode_resource : f2f_binencoders_autorewrite_db. *)

(* Ltac simpl_without_uncaught_exception := *)
(*   (* Avoids an “Uncaught exception: not found” *) *)
(*   set_evars; simpl; subst_evars. *)

Ltac _encode_cleanup :=
  match goal with
  | _ => match_ProgOk
          ltac:(fun prog pre post ext env =>
                  match post with
                  | [[ ret (_, _) as _]] :: _ =>
                    apply Propagate_anonymous_ret__fast
                  end)
  | _ => progress simpl
  | _ => progress autounfold with f2f_binencoders_autorewrite_db
  | _ => progress autorewrite with f2f_binencoders_autorewrite_db
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

(* Hint Resolve WrapN16_WrapListBool16 : compile_do_side_conditions_db. *)

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
