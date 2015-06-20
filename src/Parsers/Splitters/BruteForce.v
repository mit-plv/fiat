(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section brute_force_splitter.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

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

  Fixpoint up_to_rev (n : nat) : list nat :=
    match n with
      | 0 => nil
      | S n' => 0::map S (up_to_rev n')
    end.

  Lemma in_up_to_rev {n m} (H : n < m) : List.In n (up_to_rev m).
  Proof.
    revert n H; induction m; intros n H.
    { exfalso; omega. }
    { destruct n as [|n].
      { left; reflexivity. }
      { right; simpl in *.
        apply in_map, IHm.
        omega. } }
  Qed.

  Definition make_all_single_splits (str : String) : list nat
    := (length str)::up_to (length str).

  Definition make_all_production_rules (prods : productions Char) : list nat
    := up_to_rev (List.length prods).

  Context (G : grammar Char).

  Global Instance brute_force_data : @boolean_parser_dataT Char _
    := { predata := @rdp_list_predata _ G;
         split_string_for_production it its := make_all_single_splits;
         select_production_rules prods str := make_all_production_rules prods }.

  Global Instance brute_force_cdata : @boolean_parser_completeness_dataT' _ _ G brute_force_data
    := { split_string_for_production_complete len0 valid str pf it its
         := ForallT_all (fun _ => Forall_tails_all (fun prod => _));
         select_production_rules_complete len0 valid str pf nt Hvalid := _ }.
  Proof.
    { destruct prod; try solve [ constructor ].
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
        right; apply in_up_to; assumption. } }
    { hnf.
      generalize (Lookup G nt); clear.
      intros prods p.
      induction p as [ ??? pat pats p | ??? pat pats p [ n [ IHp0 [ pat' IHp1 ] ] ] ].
      { exists 0; split; [ | exists pat ].
        { apply in_up_to_rev; simpl; omega. }
        { split; [ reflexivity | assumption ]. } }
      { exists (S n); split; [ | exists pat' ].
        { right; apply in_map; assumption. }
        { simpl; assumption. } } }
  Qed.
End brute_force_splitter.
