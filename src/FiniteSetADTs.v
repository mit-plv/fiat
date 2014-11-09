Require Export ADTSynthesis.FiniteSetADTs.FiniteSetADT ADTSynthesis.FiniteSetADTs.FiniteSetRefinement.
(** Files to make examples more plesant *)
Require Export ADTSynthesis.Computation.Core ADTSynthesis.Computation.Notations ADTSynthesis.ADTRefinement.GeneralRefinements ADTSynthesis.ADTNotation ADTSynthesis.ComputationalEnsembles.
(** Re-export this one last, so we get the right [cardinal]. *)
Require Export ADTSynthesis.FiniteSetADTs.FiniteSetADT.

(** We don't care about displaying the implementation argument *)
Arguments FiniteSetOfList {_} _.

Global Open Scope comp_scope.
