(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Parsers.MinimalParseOfParse.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section brute_force_splitter.
  Context {string} {HSL : StringLike string} {HSLP : StringLikeProperties string}.

  Fixpoint up_to (n : nat) : list nat :=
    match n with
      | 0 => nil
      | S n' => n'::up_to n'
    end.

  Lemma in_up_to {n m} (H : n < m) : List.In n (up_to m).
  Proof.
    revert n H; induction m; intros n H.
    { exfalso; omega. }
    { simpl.
      hnf in H.
      apply le_S_n in H.
      apply Compare_dec.le_lt_eq_dec in H.
      destruct H; subst; [ right; eauto | left; reflexivity ]. }
  Qed.

  Definition make_all_single_splits (str : String) : list nat
    := (length str)::up_to (length str).

  Context (G : grammar string).

  Global Instance brute_force_data : @boolean_parser_dataT string _
    := { predata := @rdp_list_predata _ _ G;
         split_string_for_production it its := make_all_single_splits }.

  Global Instance brute_force_cdata : @boolean_parser_completeness_dataT' _ _ G brute_force_data
    := { split_string_for_production_complete str0 valid str pf it its
         := ForallT_all (fun _ => Forall_tails_all (fun prod => _)) }.
  Proof.
    destruct prod; try solve [ constructor ].
    hnf.
    intros [ n [ p0 p1 ] ].
    destruct (Compare_dec.le_lt_dec (length str) n).
    { exists (length str); simpl; repeat split.
      { left; reflexivity. }
      { eapply expand_minimal_parse_of_item; [ .. | eassumption ];
        try solve [ reflexivity
                  | left; reflexivity
                  | rewrite !take_long; trivial; reflexivity ]. }
      { eapply expand_minimal_parse_of_production; [ .. | eassumption ];
        try solve [ reflexivity
                  | left; reflexivity
                  | apply bool_eq_empty; rewrite drop_length; omega ]. } }
    { exists n; simpl; repeat split; try assumption.
      right; apply in_up_to; assumption. }
  Qed.
End brute_force_splitter.
