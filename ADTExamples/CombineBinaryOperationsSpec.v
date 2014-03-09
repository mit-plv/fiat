Require Import Common ADT ADTRefinement.Pick ADTRefinement.Specs.
Require Import ADTExamples.BinaryOperationSpec.

Section two_op_spec.
  Variable op1_spec : relation nat.
  Variable op1_default_spec : nat -> Prop.
  Variable op2_spec : relation nat.
  Variable op2_default_spec : nat -> Prop.

  Variable comb : nat -> nat -> nat -> Prop.

  (** The specification of combining the two binary operations via [comb]. *)
  Definition two_op_spec
  : observerMethodSpec multiset
    := fun m x n => exists o1,
                      bin_op_spec op1_spec op1_default_spec m x o1
                      /\ exists o2,
                           bin_op_spec op2_spec op2_default_spec m x o2
                           /\ comb o1 o2 n.

  Arguments two_op_spec / .

  Definition NatTwoBinOpSpec
  : ADT
    := pickImpl (fun _ : unit => add_spec)
                (fun _ : unit => two_op_spec).
End two_op_spec.
