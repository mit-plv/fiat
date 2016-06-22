
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Properties.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.
Require Import Fiat.Common.Wf.

Set Implicit Arguments.

Local Open Scope bool_scope.

Global Instance prod_fixedpoint_lattice {prestate0 prestate1}
       {fpldata0 : grammar_fixedpoint_lattice_data prestate0}
       {fpldata1 : grammar_fixedpoint_lattice_data prestate1}
  : grammar_fixedpoint_lattice_data (@state _ fpldata0 * @state _ fpldata1).
Proof.
  refine {| prestate_lt x y := ((state_le (fst x) (fst y) && state_le (snd x) (snd y))
                                  && negb (state_beq (fst x) (fst y) && state_beq (snd x) (snd y)));
            prestate_beq := Equality.prod_beq state_beq state_beq;
            preleast_upper_bound x y
            := constant (least_upper_bound (fst x) (fst y), least_upper_bound (snd x) (snd y)) |};
  try abstract (
        repeat match goal with
               | _ => progress unfold Equality.prod_beq
               | [ |- RelationClasses.Equivalence _ ]
                 => split; repeat intro
               | [ |- well_founded _ ] => fail 1
               | [ |- is_true (?R ?x ?x) ] => reflexivity
               | [ |- is_true true ] => reflexivity
               | [ |- ?R ?x ?x ] => reflexivity
               | _ => congruence
               | [ |- Proper _ _ ] => unfold Proper, respectful
               | [ |- Transitive _ ] => intros ???; cbv beta
               | _ => progress intros
               | [ H : and _ _ |- _ ] => destruct H
               | [ H : prod _ _ |- _ ] => destruct H
               | _ => progress simpl in *
               | [ H : is_true (state_beq ?x ?y) |- _ ]
                 => rewrite H in *; clear x H
               | [ H : is_true (state_beq ?x ?y) |- _ ]
                 => clear x H
               | [ |- context[(?x <= least_upper_bound ?x ?y)%fixedpoint] ]
                 => replace (x <= least_upper_bound x y)%fixedpoint
                    with true by (symmetry; apply least_upper_bound_correct_l)
               | [ |- context[(?y <= least_upper_bound ?x ?y)%fixedpoint] ]
                 => replace (y <= least_upper_bound x y)%fixedpoint
                    with true by (symmetry; apply least_upper_bound_correct_r)
               | [ H : is_true true |- _ ] => clear H
               | [ H : is_true ?x |- context[?x] ]
                 => progress replace x with true by (symmetry; exact H)
               | [ H : is_true ?x, H' : context[?x] |- _ ]
                 => progress replace x with true in H' by (symmetry; exact H)
               | [ H : context[@state_beq ?A ?B ?x ?x] |- _ ]
                 => replace (@state_beq A B x x) with true in H by (symmetry; change (is_true (@state_beq A B x x)); reflexivity)
               | [ H : is_true (?R ?x ?y), H' : is_true (?R ?y ?z) |- _ ]
                 => unique pose proof (transitivity (R := R) H H' : is_true (R x z))
               | [ H : is_true (@state_le ?A ?B ?x ?y), H' : is_true (state_le ?y ?x) |- _ ]
                 => unique pose proof (@antisymmetry _ (@state_beq A B) _ (@state_le A B) _ x y H H' : is_true (state_beq x y))
               | [ |- context[is_true (negb ?x)] ]
                 => destruct x eqn:?; simpl; fold_is_true
               | _ => progress bool_congr_setoid
               | [ |- and _ _ ] => split
               end
      ).
  { unfold flip.
    eapply well_founded_subrelation; [ | eapply well_founded_prod_relationA with (eqA := state_beq) ];
      [ .. | eapply state_gt_wf | eapply state_gt_wf ].
    { intros x y H.
      unfold prod_relationA, flip, state_le, state in *.
      revert H.
      generalize (@state_lt _ fpldata0).
      generalize (@state_lt _ fpldata1).
      generalize (@state_beq _ fpldata0).
      generalize (@state_beq _ fpldata1).
      unfold state.
      clear.
      abstract (
          repeat match goal with
                 | _ => setoid_rewrite Bool.negb_andb
                 | _ => tauto
                 | _ => congruence
                 | _ => progress destruct_head and
                 | [ H : is_true ?x, H' : context[?x] |- _ ]
                   => progress replace x with true in H' by (symmetry; exact H)
                 | _ => progress simpl in *
                 | _ => progress bool_congr_setoid
                 | _ => progress intros
                 | _ => progress destruct_head or
                 end
        ). }
    { apply prod_relationA_Proper_from_Equivalence; try exact _; [].
      unfold flip; intros ??? x y H H'; subst.
      rewrite H; assumption. } }
Defined.

Global Instance prod_fixedpoint_lattice' {prestate0 prestate1}
       {fpldata0 : grammar_fixedpoint_lattice_data prestate0}
       {fpldata1 : grammar_fixedpoint_lattice_data prestate1}
  : grammar_fixedpoint_lattice_data (lattice_for prestate0 * lattice_for prestate1)
  := prod_fixedpoint_lattice.
