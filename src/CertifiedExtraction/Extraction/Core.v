Require Export
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.ComputesToLemmas
        CertifiedExtraction.PropertiesOfTelescopes
        CertifiedExtraction.ExtendedPropertiesOfTelescopes
        CertifiedExtraction.Extraction.Gensym
        CertifiedExtraction.Extraction.PreconditionSets.

Require Import Coq.Strings.String.
Global Open Scope string_scope.

Ltac av_from_ext ext :=
  match type of ext with
  | StringMap.t (Value ?av) => constr:av
  end.

(* Ltac find_function_in_env function env := *)
(*   match goal with *)
(*   | [ H: GLabelMap.MapsTo ?k function env |- _ ] => constr:(k) *)
(*   | _ => let key := GLabelMapUtils.find_fast function env in *)
(*         match key with *)
(*         | Some ?k => k *)
(*         end *)
(*   end. *)

(* Ltac find_function_pattern_in_env pattern env := *)
(*   match goal with *)
(*   | [ H: GLabelMap.MapsTo ?k ?function env |- _ ] => let pr := GLabelMapUtils.matches_pattern function pattern in constr:(k) *)
(*   | _ => let key := GLabelMapUtils.find_pattern pattern env in *)
(*         match key with *)
(*         | Some ?k => k *)
(*         end *)
(*   end. *)

(* Ltac assoc_telescope tel needle := *)
(*   match tel with (* Note that this may return None when a binding in fact exists *) *)
(*   | Cons (NTSome ?k) ?v _ => let eq := constr:(eq_refl k : k = needle) in constr:(Some v) *)
(*   | Cons _ _ (fun _ => ?t) => let ret := assoc_telescope t needle in constr:(ret) *)
(*   | _ => None *)
(*   end. *)

Ltac ensure_all_pointers_found :=
  (* FIXME use instead of explicitly finding pointers *)
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
        constr:true
  | _ => constr:false
  end.

Ltac is_sca_comp v :=
  match type of v with
  | Comp ?w => let r := unifiable w W in constr:r
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

Ltac compile_do_side_conditions_internal :=
  repeat cleanup; PreconditionSet_t;
   match goal with
   | _ => exact I (* FIXME This is much faster than adding a match for True; why? *)
   | |- _ <> _ => discriminate 1
   | |- _ <> _ => congruence
   | |- _ ∉ _ => decide_not_in
   | |- NotInTelescope _ _ => decide_NotInTelescope
   | |- StringMap.find _ _ = Some _ => decide_mapsto_maybe_instantiate
   | |- StringMap.MapsTo _ _ _ => decide_mapsto_maybe_instantiate
   | |- GLabelMap.MapsTo _ _ _ => GLabelMapUtils.decide_mapsto_maybe_instantiate
   end.

Ltac compile_do_side_conditions :=
  solve [compile_do_side_conditions_internal].

Ltac match_ProgOk continuation :=
  lazymatch goal with
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => first [continuation prog pre post ext env | fail]
  | _ => fail "Goal does not look like a ProgOk statement"
  end.

Ltac clean_DropName_in_ProgOk :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       try (is_dirty_telescope pre; PreconditionSet_t; clean_telescope pre ext);
                       try (is_dirty_telescope post; PreconditionSet_t; clean_telescope post ext)).
