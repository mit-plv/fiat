Require Import Coq.Strings.Ascii.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.MSets.MSetFacts.
Require Import Coq.MSets.MSetProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Common.MSetBoundedLattice.
Require Import Fiat.Common.MSetExtensions.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.

Module PositiveSetBoundedLattice := MSetBoundedLattice PositiveSet.
Module Import PositiveSetExtensions := MSetExtensions PositiveSet.

Section gen.
  Context (max : PositiveSet.t).

  Definition transparent_is_true {P} : is_true P -> is_true P
    := match P return is_true P -> is_true P with
       | true => fun _ => eq_refl
       | false => fun x => x
       end.

  Notation small_PositiveSet := { v : PositiveSet.t | is_true (PositiveSet.subset v max) } (only parsing).

  Lemma union_subset_max {x y : small_PositiveSet}
    : is_true (PositiveSet.subset (PositiveSet.union (proj1_sig x) (proj1_sig y)) max).
  Proof.
    destruct x as [x Hx], y as [y Hy].
    apply PositiveSet.subset_spec; simpl.
    setoid_rewrite PositiveSet.subset_spec in Hx.
    setoid_rewrite PositiveSet.subset_spec in Hy.
    rewrite Hx, Hy.
    rewrite PositiveSetExtensions.union_idempotent; reflexivity.
  Qed.

  Global Instance positive_set_fpdata
    : grammar_fixedpoint_lattice_data small_PositiveSet.
  Proof.
    refine {| prestate_lt x y
              := PositiveSetBoundedLattice.lift_ltb (proj1_sig x) (proj1_sig y);
              prestate_beq x y
              := PositiveSet.equal (proj1_sig x) (proj1_sig y);
              preleast_upper_bound x y
              := constant
                   (let v := PositiveSet.union (proj1_sig x) (proj1_sig y) in
                    exist
                      _ v
                      (transparent_is_true union_subset_max)) |};
      try abstract (
            repeat match goal with
                   | [ |- Equivalence _ ]
                     => split; repeat intro;
                        [ reflexivity
                        | symmetry; assumption
                        | etransitivity; eassumption ]
                   | [ |- Transitive _ ] => hnf
                   | [ |- is_true true ] => reflexivity
                   | [ |- well_founded _ ] => fail 1
                   | [ |- Proper _ _ ] => unfold Proper, respectful
                   | [ |- Transitive _ ] => repeat intro; etransitivity; eassumption
                   | [ |- ?R ?x ?x ] => reflexivity
                   | _ => progress intros
                   | _ => progress simpl in *
                   | _ => progress rewrite ?orb_negb_r
                   | [ H : _ |- _ ] => setoid_rewrite <- BasicFacts.equal_iff in H
                   | _ => setoid_rewrite <- BasicFacts.equal_iff
                   | _ => progress unfold PositiveSetBoundedLattice.lift_ltb, PositiveSetBoundedLattice.lift_ltb_with_max, proj1_sig in *
                   | [ H : sig _ |- PositiveSet.Equal _ _ ] => destruct H as [? _]
                   | _ => progress setoid_subst_rel PositiveSet.Equal
                   | [ H : sig _ |- _ ] => destruct H as [? _]
                   | [ |- context[PositiveSet.subset ?x (PositiveSet.union ?x ?y)] ]
                     => replace (PositiveSet.subset x (PositiveSet.union x y))
                        with true
                       by (rewrite union_subset_1b; reflexivity)
                   | [ |- context[PositiveSet.subset ?y (PositiveSet.union ?x ?y)] ]
                     => replace (PositiveSet.subset y (PositiveSet.union x y))
                        with true
                       by (rewrite union_subset_2b; reflexivity)
                   end
          );
      repeat match goal with
             | [ |- Transitive _ ] => abstract (repeat intro; etransitivity; eassumption)
             end.
    { eapply well_founded_subrelation.
      2:eapply well_founded_RA_of with (f := @proj1_sig _ _), PositiveSetBoundedLattice.well_founded_lift_gtb_with_max with (max := max).
      unfold flip; intros [x Hx] [y Hy] H; simpl in *.
      unfold PositiveSetBoundedLattice.lift_ltb_with_max, PositiveSetBoundedLattice.lift_ltb in *.
      rewrite Hx.
      rewrite andb_true_r.
      assumption. }
  Defined.
End gen.
