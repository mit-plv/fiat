Set Implicit Arguments.

(* Specification of mutator method. *)
Definition mutatorMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final Model *)
  -> Prop.

(* Specification of an observer method *)
Definition observerMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> nat (* Return value *)
  -> Prop.
