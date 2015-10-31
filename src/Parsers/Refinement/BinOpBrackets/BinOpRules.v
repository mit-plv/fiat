(** Refinement rules for binary operations *)
Require Import Coq.Lists.List.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.OfParse.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.MakeBinOpTable.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalancedLemmas.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalancedGrammar.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Export Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.

Local Open Scope string_like_scope.

Set Implicit Arguments.

Local Opaque string_stringlike.

Section helper_lemmas.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  Lemma paren_balanced_hiding'_prefix__index_points_to_binop
        (str : StringLike.String)
        (n idx len : nat)
        (H_hiding : paren_balanced_hiding' (take len (drop n str)) 0)
        (H_points_to : index_points_to_binop n idx str)
        (H_pre_hiding : paren_balanced' (take idx (drop n str)) 0)
        (H_small : idx < min len (StringLike.length (drop n str)))
  : False.
  Proof.
    unfold index_points_to_binop in *.
    repeat match goal with
             | [ H : context[StringLike.get ?n ?str] |- _ ]
               => not constr_eq n 0;
                 let H' := fresh in
                 revert H;
                   case_eq (StringLike.get n str);
                   rewrite get_drop; intros
             | _ => progress destruct_head ex
             | _ => progress split_and
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
             | [ H : FirstChar.for_first_char _ _, H' : _ < _, H'' : _ < _ |- _ ]
               => apply FirstChar.for_first_char_exists in H;
                 [
                     | rewrite !drop_length; clear -H' H''; omega ]
             | [ H : _ < min _ _ |- _ ] => apply NPeano.Nat.min_glb_lt_iff in H
           end.
    eapply (paren_balanced_hiding'_prefix);
      [ exact H_hiding
      | exact H_pre_hiding
      | eassumption
      | eassumption
      | assumption ].
  Qed.
End helper_lemmas.

Section refine_rules.
  Context {G : grammar Ascii.ascii}
          (Hvalid : grammar_rvalid G)
          {str : StringLike.String} {n m : nat} {nt : string} {ch : Ascii.ascii} {its : production Ascii.ascii}
          (Hnt_valid : let predata := rdp_list_predata (G := G) in is_valid_nonterminal initial_nonterminals_data nt).

  Definition dummy_value := 0.

  Local Opaque rdp_list_predata.

  Local Notation retT table
    := (refine {splits : list nat
               | split_list_is_complete
                   G (substring n m str)
                   (NonTerminal nt)
                   (Terminal ch :: its) splits}
               (ret [match List.nth n table None with
                       | Some idx => idx
                       | None => dummy_value
                     end])).

  Section general_table.
    Context {pdata : paren_balanced_hiding_dataT Ascii.ascii}
            (Hch : is_bin_op ch).
    Context (table : list (option nat)).
    Context (Htable : list_of_next_bin_ops_spec table str).

    Lemma refine_binop_table'
          (H_nt_hiding
           : forall str', parse_of_item G str' (NonTerminal nt)
                          -> paren_balanced_hiding str')
    : retT table.
    Proof.
      intros ls H.
      computes_to_inv; subst.
      apply PickComputes.
      specialize (Htable n).
      intros idx' Hsmall Hreachable pit pits; simpl.
      specialize (H_nt_hiding _ pit).
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
                                             by (revert H'; clear; abstract (repeat apply Min.min_case_strong; intros; omega))
               | [ H : parse_of_item _ _ (Terminal _) |- _ ] => inversion H; clear H
               | _ => progress subst
             end.
      unfold list_of_next_bin_ops_spec'' in *.

      destruct (List.nth n table None) as [idx|].
      { edestruct Htable as [[Htable0 Htable1] _]; clear Htable; [ reflexivity | ].
        left.
        destruct (Compare_dec.lt_eq_lt_dec idx idx') as [[?|?]|?];
          [
          | subst; apply Min.min_r; rewrite take_length; assumption
          | ];
          exfalso.
        { (** idx < idx'; this contradicts the paren-balanced-hiding
          assumption about [nt], because we have a character in the
          middle of the string of length idx', where the prefix is
          paren-balanced-hiding at level 0, and the character is a
          bin-op. *)
          apply paren_balanced_hiding_impl_paren_balanced' in Htable1; [ | exact _ .. ].
          eapply paren_balanced_hiding'_prefix__index_points_to_binop; try eassumption.
          revert Hsmall.
          repeat apply Min.min_case_strong; intros; try assumption; omega. }
        { (** idx' < idx; this contradicts the paren-balanced-hiding
          assumption about the string of length idx, because we have a
          string parsing as a valid nt, with an unhidden bin-op right
          after it. *)
          apply paren_balanced_hiding_impl_paren_balanced' in H_nt_hiding; [ | exact _ .. ].

          eapply (paren_balanced_hiding'_prefix);
            [ exact Htable1
            | exact H_nt_hiding
            | eassumption
            | eassumption
            | assumption ]. } }
      { simpl.
        pose proof (fun idx => proj2 (Htable idx) eq_refl) as Htable'.
        clear Htable.
        apply paren_balanced_hiding_impl_paren_balanced' in H_nt_hiding.
        specialize (Htable' _ H_nt_hiding).
        unfold index_not_points_to_binop in *.
        apply FirstChar.for_first_char_exists in Htable';
          [
          | solve [ repeat
                      match goal with
                        | [ H : is_true (_ ~= [ _ ]) |- _ ] => apply length_singleton in H
                        | [ H : _ |- _ ] => progress rewrite ?drop_length, ?take_length in H
                        | _ => progress rewrite ?drop_length, ?take_length
                        | [ H : min _ _ = _ |- _ ] => revert H; apply Min.min_case_strong; clear; intros; omega
                      end ] ].
        destruct Htable' as [ch' [Ht0 Ht1]].
        repeat match goal with
                 | [ H : _ |- _ ] => progress rewrite ?drop_drop in H
                 | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
                   => assert (ch = ch') by (eapply singleton_unique; eassumption);
                     clear H'
                 | [ H : context[drop (?a + ?b) _], H' : context[drop (?b + ?a) _] |- _ ]
                   => replace (b + a) with (a + b) in H' by omega
                 | _ => progress subst
                 | _ => congruence
               end. }
    Qed.

    Lemma refine_binop_table''
          (predata := rdp_list_predata (G := G))
          (H_nt_hiding : paren_balanced_hiding_correctness_type G nt)
    : retT table.
    Proof.
      apply refine_binop_table'.
      apply paren_balanced_hiding_nt_correct.
      assumption.
    Qed.
  End general_table.

  Section derive_table.
    Context {pdata : paren_balanced_hiding_dataT Ascii.ascii}
            (Hch : is_bin_op ch).

    Lemma refine_binop_table'''
          (predata := rdp_list_predata (G := G))
          (H_nt_hiding : paren_balanced_hiding_correctness_type G nt)
    : retT (list_of_next_bin_ops_opt_nor str).
    Proof.
      apply refine_binop_table''; try assumption.
      apply list_of_next_bin_ops_opt_nor_satisfies_spec.
    Qed.
  End derive_table.

  Section derive_pbhd.
    Definition bin_op_data_of (open close : Ascii.ascii)
    : paren_balanced_hiding_dataT Ascii.ascii
      := {| is_bin_op := ascii_beq ch;
            is_open := ascii_beq open;
            is_close := ascii_beq close |}.

    Definition maybe_open_closes {Char} (p : production Char)
    : list (Char * Char)
      := match hd None (map Some p), hd None (map Some (rev p)) with
           | Some (Terminal open), Some (Terminal close)
             => [(open, close)]
           | _, _ => nil
         end.

    Definition possible_open_closes
    : list (Ascii.ascii * Ascii.ascii)
      := fold_right
           (@app _)
           nil
           (map maybe_open_closes (Lookup G nt)).

    Definition possible_valid_open_closes
    : list (Ascii.ascii * Ascii.ascii)
      := fold_right
           (@app _)
           nil
           (map
              (fun oc
               => if paren_balanced_hiding_correctness_type (pdata := bin_op_data_of (fst oc) (snd oc)) G nt
                  then [oc]
                  else nil)
              possible_open_closes).

    Definition bin_op_data_of_maybe (oc : option (Ascii.ascii * Ascii.ascii))
    : paren_balanced_hiding_dataT Ascii.ascii
      := {| is_bin_op := ascii_beq ch;
            is_open ch' := match oc with
                             | Some oc' => ascii_beq (fst oc') ch'
                             | None => false
                           end;
            is_close ch' := match oc with
                              | Some oc' => ascii_beq (snd oc') ch'
                              | None => false
                            end |}.

    Definition correct_open_close
    : paren_balanced_hiding_dataT Ascii.ascii
      := bin_op_data_of_maybe
           (hd None (map Some possible_valid_open_closes)).

    Lemma refine_binop_table
          (predata := rdp_list_predata (G := G))
          (pdata := correct_open_close)
          (H_nt_hiding
           : match possible_valid_open_closes with
               | nil => false
               | _ => true
             end)
    : retT (list_of_next_bin_ops_opt_nor str).
    Proof.
      unfold correct_open_close, possible_valid_open_closes in *.
      subst pdata.
      revert H_nt_hiding.
      generalize possible_open_closes.
      intro ls.
      induction ls; simpl.
      { intro; congruence. }
      { match goal with
          | [ |- context[if ?e then _ else nil] ] => destruct e eqn:?
        end.
        { simpl; intro.
          apply refine_binop_table'''; try assumption.
          apply ascii_lb; reflexivity. }
        { simpl; assumption. } }
    Qed.
  End derive_pbhd.
End refine_rules.

Global Arguments bin_op_data_of / .
Global Arguments possible_open_closes / .
Global Arguments maybe_open_closes / .
Global Arguments correct_open_close / .
Global Arguments possible_open_closes / .
Global Arguments possible_valid_open_closes / .
Global Arguments bin_op_data_of_maybe / .
Global Arguments default_list_of_next_bin_ops_opt_data / .
Global Arguments take : simpl never.
Global Arguments drop : simpl never.

(** [simpl] is very slow at simplifying [correct_open_close], so we
    help it along.  If the machinery of [Defined] changes, we may have
    to use [replace] rather than [change], and [vm_compute], or
    something. *)

Ltac presimpl_after_refine_binop_table :=
  unfold correct_open_close;
  match goal with
    | [ |- appcontext[@possible_valid_open_closes ?G ?nt ?ch] ]
      => let c := constr:(@possible_valid_open_closes G nt ch) in
         let c' := (eval lazy in c) in
         change c with c'
  end;
  match goal with
    | [ |- context[@default_list_of_next_bin_ops_opt_data ?HSL ?data] ]
      => let c := constr:(@default_list_of_next_bin_ops_opt_data HSL data) in
         let c' := (eval cbv beta iota zeta delta [default_list_of_next_bin_ops_opt_data ParenBalanced.Core.is_open ParenBalanced.Core.is_close ParenBalanced.Core.is_bin_op bin_op_data_of_maybe List.hd List.map fst snd] in c) in
         change c with c'
  end.
