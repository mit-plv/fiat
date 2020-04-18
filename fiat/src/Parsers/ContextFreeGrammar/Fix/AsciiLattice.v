Require Import Coq.Strings.Ascii.
Require Import Coq.MSets.MSetPositive.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Common.MSetBoundedLattice.
Require Import Fiat.Common.MSetExtensions.
Require Import Fiat.Common.BoolFacts.

Module PositiveSetBoundedLattice := MSetBoundedLattice PositiveSet.
Module Import PositiveSetExtensions := MSetExtensions PositiveSet.

Section gen.
  Global Instance positive_set_fpdata
    : grammar_fixedpoint_lattice_data PositiveSet.t.
  Proof.
    refine {| prestate_lt := Basics.flip PositiveSetBoundedLattice.lift_ltb;
              prestate_beq := PositiveSet.equal;
              preleast_upper_bound x y
              := constant (PositiveSet.inter x y) |};
      try abstract (
            repeat match goal with
                   | [ |- is_true true ] => reflexivity
                   | [ |- ?R ?x ?x ] => reflexivity
                   | _ => assumption
                   | [ |- well_founded _ ] => fail 1
                   | [ |- Proper _ _ ] => unfold Proper, respectful
                   | [ |- Transitive _ ] => repeat intro; etransitivity; eassumption
                   | _ => progress unfold flip in *
                   | _ => progress unfold lattice_for_beq, lattice_for_lt, PositiveSetBoundedLattice.lift_ltb in *
                   | _ => progress intros
                   | _ => progress PositiveSetExtensions.handle_known_comparisons
                   | _ => progress bool_congr
                   | _ => progress PositiveSetExtensions.to_caps
                   | _ => progress PositiveSetExtensions.simplify_sets
                   end
          ).
    { unfold flip; apply PositiveSetBoundedLattice.well_founded_lift_ltb. }
  Defined.
End gen.

Definition max_ascii := Eval compute in BinPos.Pos.of_nat (S (nat_of_ascii (Ascii true true true true true true true true))).
