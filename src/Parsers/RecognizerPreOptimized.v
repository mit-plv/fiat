Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Common.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.StringLike.Properties.
Require Fiat.Parsers.MinimalParseOfParse.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {G : pregrammar' Char}.

  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Let rdata' : @parser_removal_dataT' _ G predata := rdp_list_rdata'.
  Local Existing Instance rdata'.

  Context {splitdata : @split_dataT Char _ _}.
  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.
  Context {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}.

  Local Instance optsplitdata : @split_dataT Char _ _
    := { split_string_for_production p_idx str offset len
         := match to_production p_idx with
              | nil => 0::nil
              | _::nil => len::nil
              | it::_
                => match it with
                     | Terminal _ => 1::nil
                     | _ => @split_string_for_production _ _ _ splitdata p_idx str offset len
                   end
            end }.
  Let optdata : boolean_parser_dataT :=
    {| split_data := optsplitdata |}.

  Local Arguments minus !_ !_.
  Local Arguments min !_ !_.

  Local Instance optsplitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G optdata
    := { split_string_for_production_complete := _ }.
  Proof.
    pose proof (@split_string_for_production_complete _ _ _ _ _ splitdata_correct) as H.
    repeat (let x := fresh in intro x; specialize (H x)).
    revert H.
    apply ForallT_impl, ForallT_all; intro.
    apply Forall_tails_impl, Forall_tails_all; intros [|??];
    [ exact (fun x => x) | ].
    intro H;
      repeat (let x := fresh in intro x; specialize (H x));
      revert H.
    simpl in *.
    repeat match goal with
           | _ => assumption
           | [ |- ?R ?x ?x ] => reflexivity
           | [ H : S _ = 0 |- _ ] => clear -H; congruence
           | [ H : 0 = S _ |- _ ] => clear -H; congruence
           | [ H : nil = _::_ |- _ ] => clear -H; congruence
           | [ H : _::_ = nil |- _ ] => clear -H; congruence
           | [ H : _::_ = _::_ |- _ ] => inversion H; clear H
           | _ => progress subst
           | [ |- ?T -> ?T ] => exact (fun x => x)
           | [ |- context[match ?e with Terminal _ => _ | _ => _ end] ]
             => destruct e eqn:?
           | [ |- context[match ?e with nil => _ | _ => _ end] ]
             => destruct e eqn:?
           | _ => progress simpl
           | _ => rewrite Min.min_0_r
           | _ => intro
           | [ |- context[0 = min _ _] ] => exists 0
           | [ |- ?x = ?x ] => reflexivity
           | [ |- _ \/ False ] => left
           | _ => progress destruct_head @sigT
           | _ => progress destruct_head @prod
           | [ H : MinimalParse.minimal_parse_of_item _ _ (take _ (substring _ 0 _)) (Terminal _) |- _ ]
             => exfalso; inversion H; clear H
           | [ H : is_true (take _ (substring _ 0 _) ~= [_]) |- _ ]
             => apply length_singleton in H
           | [ H : length (take _ (substring _ 0 _)) = S _ |- _ ]
             => rewrite take_length, substring_length, <- Nat.sub_min_distr_r, Nat.add_sub, !Min.min_0_r in H
           | [ H : MinimalParse.minimal_parse_of_production _ _ _ nil |- _ ] => inversion H; clear H
           | [ |- MinimalParse.minimal_parse_of_production _ _ _ nil ] => constructor
           | [ H : MinimalParse.minimal_parse_of_item _ _ _ (Terminal _) |- _ ]
             => inversion H; clear H
           | [ |- MinimalParse.minimal_parse_of_item _ _ _ (Terminal _) ]
             => econstructor; [ eassumption | ]
           | [ H : length (drop _ (substring _ _ _)) = 0 |- _ ] => rewrite drop_length, substring_length in H
           | [ |- length (drop _ (substring _ _ _)) = 0 ] => rewrite drop_length, substring_length
           | [ H : ?x = 0 \/ ?T |- _ ]
             => let H' := fresh in
                destruct (Compare_dec.zerop x) as [H'|H'];
                  [ clear H
                  | assert T by (clear -H H'; destruct H; try assumption; try omega); clear H ]
           | [ |- (_ * _)%type ] => split
           | [ |- { _ : nat & _ } ] => eexists; repeat split; [ left; reflexivity | .. ]
           | [ H : ?x + ?y <= _ |- context[(?y + ?x)%nat] ]
             => not constr_eq x y; rewrite (Plus.plus_comm y x)
           | [ H : ?x + ?y <= _, H' : context[(?y + ?x)%nat] |- _ ]
             => not constr_eq x y; rewrite (Plus.plus_comm y x) in H'
           | [ H : context[(?x + 1)%nat] |- _ ] => rewrite (Plus.plus_comm x 1) in H; simpl plus in H
           | [ H : context[min ?x ?y], H' : ?y <= ?x |- _ ] => rewrite (Min.min_r x y) in H by assumption
           | [ H' : ?y <= ?x |- context[min ?x ?y] ] => rewrite (Min.min_r x y) by assumption
           | [ H : _ - _ = 0 |- _ ] => apply Nat.sub_0_le in H
           | [ |- _ - _ = 0 ] => apply Nat.sub_0_le
           | [ H : _ |- _ ] => progress rewrite ?Nat.add_sub, ?Minus.minus_plus in H
           | _ => progress rewrite ?Nat.add_sub, ?Minus.minus_plus, ?Minus.minus_diag, ?Min.min_idempotent
           | [ |- is_true (is_char (take ?x (take ?x _)) _) ]
             => rewrite take_take
           | [ H : is_true (is_char (take ?n ?str) ?ch) |- is_true (is_char ?str ?ch) ]
             => rewrite (take_long str)
               in H
               by (rewrite substring_length, Plus.plus_comm, Min.min_r by assumption; omega)
           | [ H : is_true (is_char (take ?n ?str) ?ch) |- is_true (is_char (take 1 ?str) ?ch) ]
             => apply take_n_1_singleton in H
           | [ |- MinimalParse.minimal_parse_of_production _ _ _ (_::_) ]
             => eapply @MinimalParseOfParse.expand_minimal_parse_of_production_beq;
               [ try assumption.. | eassumption ]
           | [ |- MinimalParse.minimal_parse_of_item _ _ (take 0 _) _ ]
             => eapply @MinimalParseOfParse.expand_minimal_parse_of_item_beq;
               [ try assumption.. | eassumption ]
           | [ |- MinimalParse.minimal_parse_of_item _ _ _ _ ]
             => eapply @MinimalParseOfParse.expand_minimal_parse_of_item_beq;
               [ try assumption.. | eassumption ]
           | [ H : is_true (is_char (take ?x _) _) |- ?R (drop ?x _) (drop 1 _) ]
             => apply length_singleton in H; rewrite take_length, substring_length in H
           | [ H : min ?x ?y = 1
               |- ?R (drop ?x (substring _ ?y _)) (drop 1 (substring _ ?y _)) ]
             => revert H; apply Min.min_case_strong; intros; subst;
                try reflexivity;
                apply bool_eq_empty
           | [ |- context[S ?x - ?x] ]
             => rewrite <- Nat.add_1_r, Minus.minus_plus
           | [ |- context[take ?x (take 0 _)] ]
             => rewrite take_take
           | [ |- context[min _ ?x - ?x] ]
             => rewrite <- Nat.sub_min_distr_r
           | [ H : ?y <= ?x |- context[take ?x (substring ?z ?y ?str)] ]
             => rewrite (take_long (substring z y str))
               by (rewrite substring_length, Plus.plus_comm, Min.min_r by assumption; omega)
           | [ |- context[take ?x (substring ?z ?x ?str)] ]
             => rewrite (take_long (substring z x str))
               by (rewrite substring_length, Plus.plus_comm, Min.min_r by assumption; omega)
           end.
  Qed.
End recursive_descent_parser.
