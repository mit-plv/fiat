Require Export
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.TelAppend
        CertifiedExtraction.PropertiesOfTelescopes
        CertifiedExtraction.ExtendedPropertiesOfTelescopes
        CertifiedExtraction.Extraction.Gensym
        CertifiedExtraction.Extraction.PreconditionSets.

Require Import Coq.Strings.String.
Global Open Scope string_scope.

Ltac av_from_ext ext :=
  match type of ext with
  | StringMap.t (Value ?av) => constr:(av)
  end.

Ltac find_in_tenv tenv v :=
  lazymatch tenv with
  | context[Cons ?k (ret v) _] => constr:k
  end.

Ltac NameTag_name v :=
  match v with
  | NTSome ?name => constr:name
  end.

Ltac ensure_all_pointers_found :=
  match goal with
  | |- GLabelMap.MapsTo ?ptr _ _ => is_evar ptr; first [solve [GLabelMapUtils.decide_mapsto_maybe_instantiate] | fail 2]
  | _ => idtac
  end.

Ltac tenv_mentions env v :=
  first [ match env with
          | context[?vv] => first [ is_evar vv; fail 1
                                 | unify v vv; fail 2 ]
          | _ => idtac
          end; fail 1 | idtac ].

Ltac tenv_mentions_fast env v :=
  lazymatch v with
  | ?f => match env with context[f] => idtac end
  | ?f ?a => match env with context[f ?a'] => unify a a' end
  | ?f ?a ?b => match env with context[f ?a' ?b'] => unify a a'; unify b b' end
  | ?f ?a ?b ?c => match env with context[f ?a' ?b' ?c'] => unify a a'; unify b b'; unify c c' end
  | ?f ?a ?b ?c ?d => match env with context[f ?a' ?b' ?c' ?d'] => unify a a'; unify b b'; unify c c'; unify d d' end
  end.

Ltac unifiable t1 t2 :=
  match constr:(true) with
  | _ => let pr := constr:(eq_refl t1 : t1 = t2) in
        constr:(true)
  | _ => constr:(false)
  end.

Ltac is_sca_comp v :=
  match type of v with
  | Comp ?w => let r := unifiable w W in constr:(r)
  end.

Ltac useless_binder term :=
  lazymatch term with
  | (fun _ => ?body) => let capture := body in idtac
  end.

Ltac first_arg f :=
  match type of f with
  | ?a -> _ => a
  end.

Ltac move_to_front var :=
  repeat
    lazymatch goal with         (* `at 1' prevents setoid_rewrite from modifying evars *)
    | [  |- context[Cons ?k _ (fun _ => Cons var _ _)] ] => setoid_rewrite (TelEq_swap k var) at 1
    | [  |- context[Cons ?k _ (fun _ => Cons (@NTSome _ _ var _) _ _)] ] => setoid_rewrite (TelEq_swap k (@NTSome _ _ var _)) at 1
    end.

Tactic Notation "debug" constr(msg) :=
  idtac msg.

Tactic Notation "debug" constr(m1) constr(m2) :=
  idtac m1 m2.

Hint Extern 1 (NotInTelescope _ _) => decide_NotInTelescope : SameValues_db.
Hint Extern 1 (_ ∉ _) => decide_not_in : SameValues_db.

Create HintDb compile_do_side_conditions_db discriminated.

Ltac compile_do_side_conditions_internal :=
  repeat cleanup; PreconditionSet_t;
   match goal with
   | _ => exact I (* NOTE This is much faster than adding a match for True; why? *)
   | |- _ <> _ => discriminate 1
   | |- _ <> _ => congruence
   | |- _ ∉ _ => decide_not_in
   | |- TelEq _ _ _ => decide_TelEq_instantiate
   | |- NotInTelescope _ _ => decide_NotInTelescope
   | |- StringMap.find _ _ = Some _ => decide_mapsto_maybe_instantiate
   | |- StringMap.MapsTo _ _ _ => decide_mapsto_maybe_instantiate
   | |- GLabelMap.MapsTo _ _ _ => GLabelMapUtils.decide_mapsto_maybe_instantiate
   | _ => idtac
   end; auto with compile_do_side_conditions_db.

Ltac compile_do_side_conditions :=
  solve [compile_do_side_conditions_internal].

Ltac match_ProgOk continuation :=
  lazymatch goal with (* Removing the [idtac] causes failures in [continuation] to cause backtracking *)
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => idtac; continuation prog pre post ext env
  | _ => fail "Goal does not look like a ProgOk statement"
  end.

Ltac match_ProgOk_constr continuation :=
  lazymatch goal with
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] =>
    let ret := continuation prog pre post ext env in
    constr:ret
  end.

Ltac may_alloc k :=
  (* Fail if ‘k’ is bound in precondition. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match pre with
            | context[Cons k _ _] => fail 1 "Precondition contains" k
            | context[Cons (NTSome k) _ _] => fail 1 "Precondition contains" k
            | _ => idtac
            end).

Ltac may_alloc_head :=
  (* Fail if pre-condition contains key of head of post-condition. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons ?k _ _ => may_alloc k
            end).

Ltac find_in_precondition v :=
  match_ProgOk_constr
    ltac:(fun prog pre post ext env => find_in_tenv pre v).

Ltac find_name_in_precondition v :=
  let nt := find_in_precondition v in
  let v := NameTag_name nt in
  constr:v.

Ltac clean_DropName_in_ProgOk :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       try (is_dirty_telescope pre; PreconditionSet_t; clean_telescope pre ext);
                       try (is_dirty_telescope post; PreconditionSet_t; clean_telescope post ext)).

Ltac change_post_into_TelAppend :=
  simpl (TelAppend _ _); (* Make sure that there are no leftover [TelAppend]s *)
  match_ProgOk ltac:(fun prog pre post ext env =>
                       let pp := fresh in
                       set post as pp; (* Otherwise change sometimes fails *)
                       let post' := make_TelAppend post in
                       change pp with post'; clear pp).
