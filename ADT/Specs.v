Set Implicit Arguments.

Section ADTSpecs.

  (* Specification of mutator method. *)

  Definition mutatorMethodSpec (Ty Dom : Type) :=
    Ty    (* Initial model *)
    -> Dom (* Actual argument*)
    -> Ty (* Final Model *)
    -> Prop.

  (* Specification of an observer method *)
  Definition observerMethodSpec (Ty Dom Cod : Type) :=
    Ty    (* Initial model *)
    -> Dom (* Actual argument*)
    -> Cod (* Return value *)
    -> Prop.

End ADTSpecs.
