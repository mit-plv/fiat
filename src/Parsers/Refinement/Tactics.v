Require Export Fiat.ADTRefinement.
Require Export Fiat.ADTNotation.BuildADT.
Require Export Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Export Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Export Fiat.ADTNotation.BuildADTSig.
Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.
Require Export Fiat.Parsers.ParserADTSpecification.
Require Export Fiat.Parsers.Refinement.ReductionTactics.
Require Export Fiat.Parsers.Refinement.PreTactics.
Require Export Fiat.Parsers.ContextFreeGrammar.Notations.
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
  unfold rindexed_spec, rindexed_spec';
  cbv beta iota zeta delta [expanded_fallback_list' BaseTypes.production_carrierT BaseTypes.nonterminals_listT BaseTypes.nonterminal_carrierT RDPList.rdp_list_predata Carriers.default_production_carrierT Carriers.default_nonterminal_carrierT BaseTypes.to_production RDPList.rdp_list_to_production expanded_fallback_list'_body forall_reachable_productions_if_eq];
  lazymatch goal with
  | [ |- context[List.fold_right _ _ (Operations.List.uniquize _ (List.map _ ?ls))] ]
    => let ls' := (eval lazy in ls) in
       change ls with ls'
  end;
  lazymatch goal with
  | [ |- context[List.fold_right _ _ (Operations.List.uniquize _ ?ls)] ]
    => let ls' := (eval lazy in ls) in
       change ls with ls'
  end;
  lazymatch goal with
  | [ |- context[List.fold_right _ _ (Operations.List.uniquize ?beq ?ls)] ]
    => let x := constr:(Operations.List.uniquize beq ls) in
       let x' := (eval lazy in x) in
       change x with x'
  end;
  change @List.length with @BooleanRecognizerOptimized.opt2.opt2.length;
  change @fst with @BooleanRecognizerOptimized.opt2.opt2.fst at 2 4;
  change @snd with @BooleanRecognizerOptimized.opt2.opt2.snd at 2 5 6;
  cbv beta iota zeta delta [to_production_opt Lookup_idx List.combine ret_cases_to_comp fst snd List.map];
  change @BooleanRecognizerOptimized.opt2.opt2.length with @List.length;
  change @BooleanRecognizerOptimized.opt2.opt2.fst with @fst;
  change @BooleanRecognizerOptimized.opt2.opt2.snd with @snd;
  cbv beta iota zeta delta [List.fold_right ret_cases_BoolDecR beq_nat_opt andb_opt];
  simpl orb; simpl andb;
  simpl.

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

Ltac splitter_start :=
  start sharpening ADT;
  start honing parser using indexed representation;
  hone method "splits";
  [ simplify parser splitter
  | ].

Ltac splitter_finish :=
  idtac;
  lazymatch goal with
  | [ |- refine _ _ ] => finish honing parser method
  | [ |- Sharpened _ ] => finish_Sharpening_SplitterADT
  end.
