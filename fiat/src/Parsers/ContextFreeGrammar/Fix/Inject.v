Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.

Set Implicit Arguments.

Global Instance inject_fixedpoint_lattice {prestate} {fpldata : grammar_fixedpoint_lattice_data prestate}
  : grammar_fixedpoint_lattice_data state
  := { prestate_lt := state_lt;
       prestate_beq := state_beq;
       prestate_beq_Equivalence := state_beq_Equivalence;
       preleast_upper_bound x y := constant (least_upper_bound x y);
       preleast_upper_bound_correct_l := least_upper_bound_correct_l;
       preleast_upper_bound_correct_r := least_upper_bound_correct_r;
       prestate_gt_wf := state_gt_wf;
       preleast_upper_bound_Proper := least_upper_bound_Proper;
       prestate_lt_Proper := state_lt_Proper;
       prestate_lt_Transitive := state_lt_Transitive }.
