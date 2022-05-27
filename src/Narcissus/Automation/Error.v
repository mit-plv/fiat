Require Import
        Coq.Strings.String
        Fiat.Narcissus.Automation.Common.

Inductive Maybe (A : Type) :=
| Failure (s : string)
| Success (p : Type).

Arguments Failure {A} _.
Arguments Success {A} _.

Inductive ErrorReport :=
  ErrorMessage (s : string).

Ltac no_error :=
  match goal with
    H := ErrorMessage ?s |- _ => is_evar s; unify s ""%string; clear H
  end.

Ltac throw s :=
  match goal with
    H := ErrorMessage ?s' |- _ => first [ is_evar s'; unify s s'
                                      | idtac ] (* TODO: Something better when there is already an error? *)
  end.

Axiom failing_case : forall (A: Type), A.

Ltac maybe tac errorMsg :=
  match goal with
  | M := ErrorMessage ?s |- _ => is_evar s
  | _ => makeEvar string ltac:(fun x => pose (ErrorMessage x))
  end ;
  lazymatch goal with
  | |- Maybe ?A =>
      let H := fresh in
      assert A as H by (ltac:(tac ());
                       (* If we make it here, the tactic failed to discharge all goals. *)
                       throw errorMsg; apply failing_case) ;
      first [ no_error; exact (Success H)
            | match goal with
                M := ErrorMessage ?s' |- _ => exact (Failure s')
              end ]
  | _ => fail "Expected a goal with type Maybe."
  end.
