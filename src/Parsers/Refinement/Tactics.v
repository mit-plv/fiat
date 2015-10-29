Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.
Require Export Fiat.Parsers.ParserADTSpecification.
Require Export Fiat.Parsers.Refinement.ReductionTactics.
Require Export Fiat.Parsers.Refinement.PreTactics.

Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Common.Equality.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.Refinement.FinishingLemma.

(** TODO: move this elsewhere, e.g., IndexedAndAtMostOneNonTerminal.v *)
Ltac start_honing_ri repInv :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  hone representation using repInv;
  parser_hone_cleanup.

Ltac start_honing :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  unfold rindexed_spec, rindexed_spec'; simpl;
  unfold forall_reachable_productions; simpl.

Tactic Notation "start" "honing" "parser" "representation" "using" open_constr(repInv)
  := (lazymatch goal with
     | [ |- FullySharpened _ ]
       => (eapply FullySharpened_Start; [ start_honing_ri repInv | | ])
     | _ => start_honing_ri repInv
      end).

Tactic Notation "start" "honing" "parser" "using" "indexed" "representation"
  := (lazymatch goal with
     | [ |- FullySharpened _ ]
       => (eapply FullySharpened_Start; [ start_honing | | ])
     | _ => start_honing
      end).

Ltac finish_Sharpening_SplitterADT
  := solve [ refine finish_Sharpening_SplitterADT ].
