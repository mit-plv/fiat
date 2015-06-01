(** Refinement rules for binary operations *)
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.MakeBinOpTable.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpLemmas.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammarValidReflective.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Export Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Refinement.Tactics.

Local Open Scope string_like_scope.

(*Require Import Coq.Lists.List.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Common.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.StringLike.Core. *)

Set Implicit Arguments.

Lemma refine_binop_table {G : grammar Ascii.ascii}
      {pdata : paren_balanced_hiding_dataT Ascii.ascii}
      (table : list (option nat))
      (Hvalid : grammar_rvalid G)
      {str n m nt ch its}
      (** this is a placeholder *)
      (H_nt_hiding
       : forall str', parse_of_item G str' (NonTerminal nt)
                      -> paren_balanced_hiding is_bin_op is_open is_close str')
      (Htable : list_of_next_bin_ops_spec is_bin_op is_open is_close table str)
      (Hch : is_bin_op ch)
: refine {splits : list nat
         | split_list_is_complete
             G (substring n m str)
             (NonTerminal nt)
             (Terminal ch :: its) splits}
         (ret match List.nth n table None with
                | Some idx => [idx]
                | None => nil
              end).
Proof.
  intros ls H.
  computes_to_inv; subst.
  apply PickComputes.
  specialize (Htable n).
  intros idx' Hsmall Hreachable pit pits Hpit Hpits; simpl.
  specialize (H_nt_hiding _ pit).
  rewrite substring_take_drop in H_nt_hiding.
  unfold paren_balanced_hiding in *.
  rewrite take_take in H_nt_hiding.
  inversion pits.
  repeat match goal with
           | [ H : context[substring _ _ _] |- _ ] => rewrite substring_take_drop in H
           | [ H : is_true (take ?n ?str ~= [ ?ch ]) |- _ ]
             => progress apply take_n_1_singleton in H

           | [ H : context[take _ (drop _ (take _ _))] |- _ ] => rewrite drop_take in H
           | [ H : is_true (take _ (take _ _) ~= [ _ ]) |- _ ] => rewrite take_take in H
           | [ H : _ <= StringLike.length _ |- _ ] => rewrite take_length in H
           | [ H : context[min ?x ?y], H' : ?x <= min ?y _ |- _ ]
             => replace (min x y) with x in H
                                         by (revert H'; repeat apply Min.min_case_strong; intros; omega)
           | [ H : parse_of_item _ _ (Terminal _) |- _ ] => inversion H; clear H
           | _ => progress subst
         end.

  destruct (List.nth n table None) as [idx|].
  { specialize (Htable _ eq_refl).
    destruct Htable as [Htable0 Htable1].
    left.
    destruct (Compare_dec.lt_eq_lt_dec idx idx') as [[?|?]|?]; [ | assumption | ];
    exfalso.
    { (** idx < idx'; this contradicts the paren-balanced-hiding
          assumption about [nt], because we have a character in the
          middle of the string of length idx', where the prefix is
          paren-balanced-hiding at level 0, and the character is a
          bin-op. *)
      (** cleanup and reorganization *)
      unfold index_points_to_binop in *.
      apply paren_balanced_hiding_impl_paren_balanced' in Htable1; [ | exact _ .. ].
      repeat match goal with
               | [ H : context[StringLike.get ?n ?str] |- _ ]
                 => not constr_eq n 0;
                   let H' := fresh in
                   revert H;
                     case_eq (StringLike.get n str);
                     rewrite get_drop; intros
               | [ H : StringLike.get 0 _ = Some _ |- _ ] => apply get_0 in H
               | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
               | [ H : ?idx < _, H' : context[drop (?n + ?idx) _] |- _ ]
                 => replace (n + idx) with (idx + n) in H' by omega
               | [ H : ?idx < _, H' : context[drop (?idx + _) _] |- _ ]
                 => rewrite <- drop_drop in H'
               | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length in H
               | [ H : context[take _ (drop _ (take _ _))] |- _ ] => rewrite drop_take in H
               | [ H : is_true (take _ (take _ _) ~= [ _ ]) |- _ ] => rewrite take_take in H
               | [ H : is_true (_ ~= [ _ ]) |- _ ] => progress apply take_n_1_singleton in H
             end.
      { eapply (paren_balanced_hiding'_prefix is_bin_op is_open is_close);
        [ exact H_nt_hiding
        | exact Htable1
        | eassumption
        | try eassumption
        | eassumption ]. }
      { repeat match goal with
                 | [ H : StringLike.get 0 _ = None |- _ ] => apply no_first_char_empty in H; revert H
                 | [ H : is_true (_ ~= [ _ ]) |- _ ] => apply length_singleton in H; revert H
                 | [ H : _ < _ |- _ ] => revert H
               end.
        clear.
        rewrite !take_length, !(drop_length _ idx), !(drop_length _ idx').
        repeat apply Min.min_case_strong; intros; omega. } }
    { (** idx' < idx; this contradicts the paren-balanced-hiding
          assumption about the string of length idx, because we have a
          string parsing as a valid nt, with an unhidden bin-op right
          after it. *)
      apply paren_balanced_hiding_impl_paren_balanced' in H_nt_hiding; [ | exact _ .. ].

      eapply (paren_balanced_hiding'_prefix is_bin_op is_open is_close);
        [ exact Htable1
        | exact H_nt_hiding
        | eassumption
        | eassumption
        | assumption ]. } }
  { simpl.
