(** Sharpened ADT for grammars with at most one nonterminal *)
Require Import Coq.Strings.String Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Equality.
Require Import ADTSynthesis.ADTRefinement.
Require Import ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist.
Require Import ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import ADTSynthesis.Common.IterateBoundedIndex.
Require Import ADTSynthesis.Parsers.Refinement.IndexedAndAtMostOneNonTerminal.
Require Import ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section helpers.
  Lemma pull_match_list {A R R' rn rc} {ls : list A} (f : R -> R')
  : match ls with
      | nil => f rn
      | cons x xs => f (rc x xs)
    end = f (match ls with
               | nil => rn
               | cons x xs => rc x xs
             end).
  Proof.
    destruct ls; reflexivity.
  Qed.

  Lemma pull_match_item {A R R' rn rc} {ls : item A} (f : R -> R')
  : match ls with
      | NonTerminal x => f (rn x)
      | Terminal x => f (rc x)
    end = f (match ls with
               | NonTerminal x => rn x
               | Terminal x => rc x
             end).
  Proof.
    destruct ls; reflexivity.
  Qed.

  Lemma pull_match_bool {R R' rn rc} {b : bool} (f : R -> R')
  : (if b then f rn else f rc)
    = f (if b then rn else rc).
  Proof.
    destruct b; reflexivity.
  Qed.
End helpers.

Section IndexedImpl.
  Context (G : grammar Ascii.ascii).

  Section reachable.
    Context (ls' : list nat)
            (H_at_most_one_non_terminal
             : forall nt its,
                 production_is_reachable G ((NonTerminal nt)::its) -> has_only_terminals its).

    Lemma any_list_complete {it its str}
    : refine
        {ls : list nat
        | match it with
            | Terminal _ => True
            | NonTerminal _ =>
              if has_only_terminals its
              then True
              else
                split_list_is_complete G str it its ls
          end }
        (ret ls').
    Proof.
      apply refine_pick_val.
      destruct it; trivial.
      case_eq (has_only_terminals its); trivial.
      intro H'.
      repeat intro.
      exfalso.
      rewrite H_at_most_one_non_terminal in H'; [ congruence | ].
      eassumption.
    Qed.
  End reachable.

  (** TODO: reflective version *)
  (*Section reachable_reflective.
    Fixpoint only_one_nt_valid_prod
             (only_one_nt_valid : String.string -> bool)
             (p : production Ascii.ascii)
    : bool
      := match p with
           | nil => true
           | (Terminal _)::p' => only_one_nt_valid_prod only_one_nt_valid p'
           | (NonTerminal nt)::p' => ((only_one_nt_valid_prod only_one_nt_valid p')
                                        && only_one_nt_valid nt
                                        && (has_only_terminals p'))%bool
         end.

    Definition only_one_nt_valid : bool
      := split_valid (G := G) only_one_nt_valid_prod.

    Lemma only_one_nt_valid_prod_cons {fcv x xs}
    : only_one_nt_valid_prod fcv (x::xs)
      = match x with
          | Terminal _ => only_one_nt_valid_prod fcv xs
          | NonTerminal nt => ((only_one_nt_valid_prod fcv xs)
                                 && fcv nt
                                 && (has_only_terminals xs || fallback_valid_prod (x::xs)))%bool
        end.
    Proof.
      reflexivity.
    Qed.




production_is_reachable G (fst n :: snd n)*)
  Context (H_at_most_one_non_terminal
           : forall nt its,
               production_is_reachable G ((NonTerminal nt)::its) -> has_only_terminals its).

  Ltac finish_honing_by_eq tac
    := solve [ repeat (subst || rewrite refineEquiv_pick_eq' || simplify with monad laws);
               simpl @fst; simpl @snd;
               tac;
               match goal with
                 | [ |- refine (ret _) _ ] => finish honing
               end  ].

  Ltac parser_pull_tac :=
    repeat match goal with
             | [ |- context G[match ?ls with
                                | nil => [?x]
                                | (_::_) => [?y]
                              end] ]
               => rewrite (@pull_match_list _ _ _ x (fun _ _ => y) ls (fun k => [k]))
             | [ |- context G[match ?it with
                                | NonTerminal _ => [?x]
                                | Terminal _ => [?y]
                              end] ]
               => rewrite (@pull_match_item _ _ _ (fun _ => x) (fun _ => y) it (fun k => [k]))
             | [ |- context G[match ?b with
                                | true => [?x]
                                | false => [?y]
                              end] ]
               => rewrite (@pull_match_bool _ _ x y b (fun k => [k]))
           end.

  Ltac parser_hone_cleanup :=
    try (hone constructor "new"; [ finish_honing_by_eq idtac | ]);
    try (hone method "to_string"; [ finish_honing_by_eq idtac | ]);
    try (hone method "is_char"; [ finish_honing_by_eq idtac | ]);
    try (hone method "length"; [ finish_honing_by_eq idtac | ]);
    try (hone method "take"; [ finish_honing_by_eq idtac | ]);
    try (hone method "drop"; [ finish_honing_by_eq idtac | ]).

  (** TODO: move this elsewhere, e.g., IndexedAndAtMostOneNonTerminal.v *)
  Tactic Notation "start" "honing" "parser" "representation" "using" open_constr(repInv)
    := eapply SharpenStep;
      [ solve [ apply FirstStep ] | ];
      hone representation using repInv;
      parser_hone_cleanup.

  Lemma FullySharpenedSplitter
  : Sharpened (string_spec G).
  Proof.
    start honing parser representation using (fun r_o r_n => r_o = r_n).

    hone method "splits".
    {
      rewrite (@any_list_complete [1]); [ | assumption ].
      finish_honing_by_eq parser_pull_tac.
    }

    (* what to do here? *)
    admit.
  Defined.

  Definition ComputationalSplitter : { impl : cADT (string_rep Ascii.ascii) & refineADT (string_spec G) (LiftcADT impl) }.
  Proof.
    eexists (Sharpened_Implementation (projT1 FullySharpenedSplitter)
                                     (fun _ => unit)
                                     (fun idx => _)).
    apply (projT2 FullySharpenedSplitter).
    (* how does this goal get solved? *)
    (* also, is it better to do it seprately each time, where we can run [simpl], or better to do it once and for all, in ParserFromParserADT.v? *)
  Admitted.
End IndexedImpl.
