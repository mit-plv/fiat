Require Import Common String ADT ADTRefinement.Pick ADTRefinement.Specs.
Require Import ADTExamples.BinaryOperationSpec.

Section two_op_spec.
  Variable op1_spec : relation nat.
  Variable op1_default_spec : nat -> Prop.
  Variable op2_spec : relation nat.
  Variable op2_default_spec : nat -> Prop.

  Variable comb : nat -> nat -> nat -> Prop.

  (** The specification of combining the two binary operations via [comb]. *)

  Definition two_op_spec
  : observerMethodSpec multiset nat nat
    := fun m x n => exists o1,
                      bin_op_spec op1_spec op1_default_spec m x o1
                      /\ exists o2,
                           bin_op_spec op2_spec op2_default_spec m x o2
                           /\ comb o1 o2 n.

  Arguments two_op_spec / .

  Definition CombTwoOpCollectionSig comName : ADTSig :=
    ADTsignature {
        "Insert" : rep × nat → rep ;
        comName : rep × nat → nat
      }%ADTSig.

  Definition NatTwoBinOpSpec comName
  : ADT (CombTwoOpCollectionSig comName) :=
    ADTRep multiset `[
             def "Insert" `[ m `: rep , n `: nat ]` : rep :=
               {m' | add_spec m n m'}%comp ;
             def comName `[m `: rep , n `: nat ]` : nat :=
                 {n' | two_op_spec m n n'}%comp
           ]`%ADT .

End two_op_spec.

Definition MinPlusMaxSpec : ADT (CombTwoOpCollectionSig "MinPlusMax"%string)
  := NatTwoBinOpSpec le (fun _ => True) ge (fun _ => True) (fun x y sum => x + y = sum) _.
