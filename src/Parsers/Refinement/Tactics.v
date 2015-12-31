Require Export Fiat.ADTRefinement.
Require Export Fiat.ADTNotation.BuildADT.
Require Export Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Export Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Export Fiat.ADTNotation.BuildADTSig.
Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.
Require Export Fiat.Parsers.ParserADTSpecification.
Require Export Fiat.Parsers.Refinement.ReductionTactics.
Require Export Fiat.Parsers.Refinement.PreTactics.
Require Export Fiat.Parsers.StringLike.String.

Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.PrettyNotations.

Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Common.Equality.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.Refinement.FinishingLemma.

Notation hiddenT := (ADTSig.methodType _ _ _).

Ltac finish_honing_by_eq tac
  := solve [ repeat (subst
                       || rewrite refineEquiv_pick_eq'
                       || (simplify with monad laws)
                       || (simpl @fst; simpl @snd)
                       || tac);
             match goal with
               | [ |- refine (ret _) _ ] => finish honing
             end  ].

Ltac parser_hone_cleanup :=
  try (hone constructor "new"; [ finish_honing_by_eq idtac | ]);
  try (hone method "to_string"; [ finish_honing_by_eq idtac | ]);
  try (hone method "is_char"; [ finish_honing_by_eq idtac | ]);
  try (hone method "length"; [ finish_honing_by_eq idtac | ]);
  try (hone method "take"; [ finish_honing_by_eq idtac | ]);
  try (hone method "drop"; [ finish_honing_by_eq idtac | ]).

Ltac start_honing_ri repInv :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  hone representation using repInv;
  parser_hone_cleanup.

Ltac start_honing :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  unfold rindexed_spec, rindexed_spec'; simpl;
  unfold forall_reachable_productions_if_eq; simpl.

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

Tactic Notation "finish" "honing" "parser" "method"
  := finish_honing_by_eq parser_pull_tac.

Ltac finish_Sharpening_SplitterADT
  := solve [ refine finish_Sharpening_SplitterADT ].
