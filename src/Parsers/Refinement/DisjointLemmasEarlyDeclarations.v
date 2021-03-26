Require Export Fiat.Common.Coq__8_4__8_5__Compat.
(** We declare this tactic here so we can overwrite it in
    DisjointLemmas, but also run it in Refinement/Tactics.v without
    importing DisjointLemmas. *)
Ltac do_disjoint_precomputations _ := idtac.
