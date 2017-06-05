(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Common.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section brute_force_splitter.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition make_all_single_splits (str : String) (offset len : nat) : list nat
    := len::up_to len.

  Context (G : pregrammar' Char).


  Global Instance brute_force_split_data : @split_dataT Char _ (rdp_list_predata (G := G))
    := { split_string_for_production p := make_all_single_splits }.

  Global Instance brute_force_data : @boolean_parser_dataT Char _
    := { predata := @rdp_list_predata _ G;
         split_data := brute_force_split_data }.

  Global Instance brute_force_cdata : @boolean_parser_completeness_dataT' _ _ _ G brute_force_data
    := { split_string_for_production_complete str0 valid str offset len pf nt pf' pf''
         := ForallT_all (fun _ => Forall_tails_all (fun prod => _)) }.
  Proof.
    destruct prod; try solve [ constructor ].
    hnf.
    intros; intros [ n [ p0 p1 ] ].
    destruct (Compare_dec.le_lt_dec len n).
    { exists len; simpl; repeat split.
      { left; reflexivity. }
      { eapply expand_minimal_parse_of_item; [ .. | eassumption ];
        try solve [ reflexivity
                  | left; reflexivity
                  | rewrite !take_long; trivial; reflexivity
                  | rewrite take_long at 1 by (rewrite Properties.substring_length; apply Min.min_case_strong; omega);
                    symmetry;
                    rewrite take_long at 1 by (rewrite Properties.substring_length; apply Min.min_case_strong; omega);
                    reflexivity ]. }
      { eapply expand_minimal_parse_of_production; [ .. | eassumption ];
        try solve [ reflexivity
                  | left; reflexivity
                  | apply bool_eq_empty; rewrite drop_length; omega
                  | apply bool_eq_empty; rewrite drop_length, Properties.substring_length; apply Min.min_case_strong; omega ]. } }
    { exists n; simpl; repeat split; try assumption.
      right; apply List.in_map, in_up_to; assumption. }
  Qed.
End brute_force_splitter.
