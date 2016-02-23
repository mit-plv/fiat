Require Export Fiat.ADTRefinement.
Require Export Fiat.ADTNotation.BuildADT.
Require Export Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Export Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Export Fiat.ADTNotation.BuildADTSig.
Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.
Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflectiveOpt.
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

Ltac change_with_cbv c :=
    let c' := (eval cbv in c) in
    change c with c'.

Ltac replace_with_vm_compute c :=
  let c' := (eval vm_compute in c) in
  (* we'd like to just do: *)
  (* replace c with c' by (clear; abstract (vm_compute; reflexivity)) *)
  (* but [set] is too slow in 8.4, so we write our own version (see https://coq.inria.fr/bugs/show_bug.cgi?id=3280#c13 *)
  let set_tac := (fun x' x
                  => pose x as x';
                     change x with x') in
  replace_with_at_by c c' set_tac ltac:(clear; abstract (vm_compute; reflexivity)).

Ltac start_honing :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  unfold opt_rindexed_spec;
  (*
  let p' := fresh "p'" in
  match goal with
  | [ |- appcontext[pregrammar_productions ?G] ]
    => let p := constr:(pregrammar_productions G) in
       set (p' := p);
       hnf in p'
  end; *)
  do 2 match goal with
       | [ |- context[opt.combine ?ls ?ls'] ]
         => replace_with_vm_compute (opt.combine ls ls')
       | [ |- context[opt2.uniquize ?beq ?ls] ]
         => replace_with_vm_compute (opt2.uniquize beq ls)
       end;
  cbv [opt2.fold_right opt.map opt2.ret_cases_BoolDecR opt.fst opt.snd];
  change (orb false) with (fun x : bool => x); cbv beta.

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
