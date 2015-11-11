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

Ltac find_function_in_env function env :=
  match goal with
  | [ H: GLabelMap.MapsTo ?k function env |- _ ] => constr:(k)
  | _ => let key := GLabelMapUtils.find_fast function env in
        match key with
        | Some ?k => k
        end
  end.

Ltac find_function_pattern_in_env pattern env :=
  match goal with
  | [ H: GLabelMap.MapsTo ?k ?function env |- _ ] => let pr := GLabelMapUtils.matches_pattern function pattern in constr:(k)
  | _ => let key := GLabelMapUtils.find_pattern pattern env in
        match key with
        | Some ?k => k
        end
  end.

Tactic Notation "debug" constr(msg) :=
  idtac msg.

Tactic Notation "debug" constr(m1) constr(m2) :=
  idtac m1 m2.

Hint Extern 1 (NotInTelescope _ _) => decide_NotInTelescope : SameValues_db.
Hint Extern 1 (_ ∉ _) => decide_not_in : SameValues_db.

Ltac compile_do_side_conditions :=
  solve [ PreconditionSet_t;
          match goal with
          | _ => abstract decide_not_in
          | _ => abstract decide_NotInTelescope
          | [  |- StringMap.find _ _ = Some _ ] => solve [decide_mapsto_maybe_instantiate]
          | [  |- StringMap.MapsTo _ _ _ ] => solve [decide_mapsto_maybe_instantiate]
          | [  |- GLabelMap.MapsTo _ _ _ ] => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
          end].

Ltac match_ProgOk continuation :=
  lazymatch goal with
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => first [continuation prog pre post ext env | fail]
  | _ => fail "Goal does not look like a ProgOk statement"
  end.
