Require Import
        Coq.Strings.String
        Fiat.Narcissus.Automation.Common.

(** * Error Reporting in Narcissus Automation

    We report errors in Narcissus automation using the <<Maybe>> type
    defined below. When we know automation (e.g., decoder synthesis)
    might fail, we wrap the top-level type in a <<Maybe>>. For example,
    synthesizing a <<CorrectAlignedDecoderFor ?invariant ?format>> might
    fail if the <<format>> is improperly specified, and so we may wish
    to synthesize the type <<Maybe (CorrectAlignedDecoderFor ...)>>.

    Rather than require every proof term in the synthesis pipeline to
    be aware of <<Maybe>> and define their types accordingly, we
    instead take the following approach:

    1. When we prove a <<Maybe>> type (using the <<maybe>> tactic
       defined below), we first introduce an <<ErrorReport ?message>>,
       into the proof context, where <<message>> is an un-unified
       evar.
    2. At any point in the automation, any tactic may call the
       <<throw>> tactic defined below to report a failure. This tactic
       unifies the <<message>> evar with a concrete error message.
    3. At the end of the <<maybe>> tactic, we check to see that
       a) <<message>> is still un-unified, and
       b) all proof obligations have been discharged.
       If both of these conditions are met, we yield a <<Success>>.
       Otherwise, we yield a <<Failure>> with the appropriate error
       message.

    When a failure is detected, we use the <<failing_case>> axiom
    defined below to provide a proof object of the appropriate type.
    In this way, the proof automation successfully completes, but with
    a <<Failure>> instance. (The intuition here is that a <<Failure>>
    "inhabits" all types.)

    Tracking error messages in the proof context this way might seem
    like (and arguably is) a bit of a hack, but the approach has the
    following advantages:

    - Most of the automation code does not need to worry about
      <<Maybe>>; the <<Maybe>> type does not proliferate across the
      entire codebase, but rather is confined to the places that care
      about errors.

    - When a failure occurs, the proof search stops and a complete
      proof object is still assembled. Instead of, e.g., monitoring
      the response buffer to determine synthesis status, external
      processes using Narcissus can pattern match against <<Maybe>>
      success or failure on the complete proof object during
      extraction.
 *)

Inductive Maybe (A : Type) :=
| Failure (s : string)
| Success (a : A).

Arguments Failure {A} _.
Arguments Success {A} _.

(**
    The error object type. Currently we just have an error message string,
    but we could add other error information or types if needed.
 *)
Inductive ErrorReport :=
  ErrorMessage (s : string).

(**
   The axiom we will use to provide "dummy" proof terms in failure cases.
   Indexed on <<ErrorReport>>s to formalize the intuition that errors "inhabit"
   arbitrary types.
 *)
Axiom failing_case : forall (e: ErrorReport) (A: Type), A.

(**
    If there is an un-unified error in the proof context, unifies it with a
    dummy string and clears it. Fails otherwise. This tactic is used to check the
    error state at the end of a <<maybe>> tactic application.
 *)
Ltac no_error :=
  match goal with
    H := ErrorMessage ?s |- _ => is_evar s; unify s ""%string; clear H
  end.

(**
   If there is an error object in the context with an un-unified error message,
   unifies with the given message string. Otherwise, does nothing.
   This is the tactic most code should use to report a failure.
 *)
Ltac throw s :=
  match goal with
    H := ErrorMessage ?s' |- _ => first [ is_evar s'; unify s s'
                                      (* TODO: Something better when there is already an error? *)
                                      | idtac ] ;
                                apply failing_case; exact (ErrorMessage s)
  end.

(**
   The core tactic for proving a goal of type <<Maybe>>. Callers should provide
   <<tac>>, a tactic (wrapped in a dummy function) which attempts to solve the
   Maybe's contained type, as well as <<errorMsg>>, the error string to report
   if <<tac>> fails to discharge all proof obligations.

   Note that <<tac>> must be wrapped in a dummy function from (), i.e.,
   <<fun _ => tactic here>>, because ltac is call-by-value and we want to,
   for example, delay any pattern matching on the goal.
 *)
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

(** A large elimination from <<Maybe A>> to either some type <<B>> in case of
    success or <<string>> in case of failure. *)
Definition MaybeT {A : Type} (B : Type) (m : Maybe A) : Type :=
  match m with
  | Failure _ => string
  | Success _ => B
  end.


Ltac foo := throw "foo"%string.
Ltac bar := foo.
Lemma baz : Maybe (forall n : nat, n = n).
Proof.
  maybe ltac:(fun _ => bar) "baz"%string.
Defined.

Print baz.
