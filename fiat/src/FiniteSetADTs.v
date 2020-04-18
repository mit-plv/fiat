Require Export Fiat.FiniteSetADTs.FiniteSetADT Fiat.FiniteSetADTs.FiniteSetRefinement.
(** Files to make examples more plesant *)
Require Export Fiat.Computation.Core Fiat.Computation.Notations Fiat.ADTRefinement.GeneralRefinements Fiat.ADTNotation Fiat.ComputationalEnsembles.
(** Re-export this one last, so we get the right [cardinal]. *)
Require Export Fiat.FiniteSetADTs.FiniteSetADT.

(** We don't care about displaying the implementation argument *)
Arguments FiniteSetOfList {_} _.

Global Open Scope comp_scope.
