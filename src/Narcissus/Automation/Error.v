Require Import
        Coq.Strings.String
        Fiat.Narcissus.Automation.Common.

Inductive Maybe (A : Type) :=
| Failure (s : string)
| Success (a : Type).

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
                                      (* TODO: Something better when there is already an error? *)
                                      | idtac ]
  end.

Axiom failing_case : forall (e: ErrorReport) (A: Type), A.

Ltac maybe tac errorMsg :=
  match goal with
  | M := ErrorMessage ?s |- _ => is_evar s
  | _ => makeEvar string ltac:(fun x => pose (ErrorMessage x))
  end ;
  lazymatch goal with
  | |- Maybe ?A =>
      let H := fresh in
      assert A as H by (unshelve ltac:(tac ());
                       (* If we make it here, the tactic failed to discharge all goals. *)
                       throw errorMsg; apply failing_case; exact (ErrorMessage errorMsg)) ;
      first [ no_error; exact (Success H)
            | match goal with
                M := ErrorMessage ?s' |- _ => exact (Failure s')
              end ]
  | _ => fail "Expected a goal with type Maybe."
  end.


(* Example *)

(* Ltac foo := intros; auto. *)
(* Ltac bar := ltac:(foo). *)

(* Lemma baz : Maybe (forall n : nat, n = n). *)
(*   maybe ltac:(fun _ => bar) "error in baz"%string. *)
(*   Show Proof. *)
(* Defined. *)
