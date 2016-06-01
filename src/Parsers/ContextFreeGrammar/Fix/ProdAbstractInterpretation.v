Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Prod.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Common.

Set Implicit Arguments.

Section aidata.
  Context {Char : Type} {T0 T1}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}.

  Definition prod_on_terminal
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
    : (Char -> bool) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun P => constant (on_terminal0 P, on_terminal1 P).

  Definition prod_on_nil_production
             (on_nil_production0 : lattice_for T0)
             (on_nil_production1 : lattice_for T1)
    : lattice_for (lattice_for T0 * lattice_for T1)
    := constant (on_nil_production0, on_nil_production1).

  Definition prod_precombine_production_dep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production (precombine_production1 (fst x) (fst y)) (snd x) (snd y)).

  Definition prod_precombine_production_nondep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production precombine_production1 (snd x) (snd y)).

  Global Instance prod_precombine_production_dep_Proper
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0}
         {HP1 : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1}
    : Proper (prestate_beq ==> prestate_beq ==> state_beq) (prod_precombine_production_dep precombine_production0 precombine_production1).
  Proof.
    unfold state_beq, prestate_beq, prod_fixedpoint_lattice', prod_fixedpoint_lattice, Equality.prod_beq, state_beq.
    intros x y H x' y' H'; simpl.
    apply Bool.andb_true_iff in H; apply Bool.andb_true_iff in H'; apply Bool.andb_true_iff;
      fold_is_true.
    destruct H as [H0 H1], H' as [H0' H1'].
    split.
    { eapply lattice_for_combine_production_Proper; assumption. }
    { specialize (HP1 _ _ H0 _ _ H0').
      destruct x as [x0 [|x1|]], y as [y0 [|y1|]]; simpl in *; try congruence;
        destruct x' as [x0' [|x1'|]], y' as [y0' [|y1'|]]; simpl in *; try congruence.
      apply HP1; assumption. }
  Qed.

  Global Instance prod_precombine_production_nondep_Proper
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0}
         {HP1 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production1}
    : Proper (prestate_beq ==> prestate_beq ==> state_beq) (prod_precombine_production_nondep precombine_production0 precombine_production1).
  Proof.
    intros x y H x' y' H'.
    change (prod_precombine_production_nondep precombine_production0 precombine_production1) with
    (prod_precombine_production_dep precombine_production0 (fun _ _ => precombine_production1)).
    eapply prod_precombine_production_dep_Proper; assumption.
    Grab Existential Variables.
    intros ??????; exact HP1.
  Qed.

  Definition prod_aidata_dep
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_nil_production0 : lattice_for T0)
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
             (on_nil_production1 : lattice_for T1)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
             (precombine_production0_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0)
             (precombine_production1_Proper
              : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1)
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'.
  Proof.
    refine {| on_terminal := prod_on_terminal on_terminal0 on_terminal1;
              on_nil_production := prod_on_nil_production on_nil_production0 on_nil_production1;
              precombine_production := prod_precombine_production_dep precombine_production0 precombine_production1 |}.
  Defined.

  Definition prod_aidata_nondep
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_nil_production0 : lattice_for T0)
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
             (on_nil_production1 : lattice_for T1)
             (precombine_production1 : T1 -> T1 -> lattice_for T1)
             (precombine_production0_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0)
             (precombine_production1_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production1)
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'.
  Proof.
    refine {| on_terminal := prod_on_terminal on_terminal0 on_terminal1;
              on_nil_production := prod_on_nil_production on_nil_production0 on_nil_production1;
              precombine_production := prod_precombine_production_nondep precombine_production0 precombine_production1 |}.
  Defined.
End aidata.
