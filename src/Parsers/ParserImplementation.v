(** * Implementation of simply-typed interface of the parser *)
Require Export Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.BooleanRecognizer Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Parsers.BooleanRecognizerPreOptimized.
Require Fiat.Parsers.SimpleRecognizer.
Require Fiat.Parsers.SimpleBooleanRecognizerEquality.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Local Open Scope list_scope.

Section implementation.
  Context {Char}
          {G : pregrammar Char}.

  Context (splitter : Splitter G).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Let parser_presplit_data : @split_dataT Char (string_type_min splitter) _.
  Proof.
    refine {| split_string_for_production idx str
              := splits_for splitter str idx |}.
  Defined.

  Local Instance parser_split_data : @split_dataT Char splitter predata
    := @optsplitdata _ _ _ parser_presplit_data.

  Local Instance preparser_data : @boolean_parser_dataT Char _ :=
    { predata := rdp_list_predata (G := G);
      split_data := parser_presplit_data }.

  Local Instance parser_data : @boolean_parser_dataT Char _ :=
    { predata := rdp_list_predata (G := G);
      split_data := parser_split_data }.

  Local Arguments split_string_for_production : simpl never.

  Local Instance parser_precompleteness_data : @boolean_parser_completeness_dataT' Char _ _ G preparser_data
    := { split_string_for_production_complete len0 valid str offset len pf nt Hvalid := _ }.
  Proof.
    apply initial_nonterminals_correct in Hvalid.
    generalize (fun it its idx offset len Hvalid' Heqb n pf pf' pit pits prefix H' => @splits_for_complete Char G splitter str idx offset len Hvalid' Heqb it its n pf pf' (ex_intro _ nt (ex_intro _ prefix (conj Hvalid H'))) pit pits).
    clear Hvalid.
    induction (G nt) as [ | x xs IHxs ].
    { intros; constructor. }
    { intros H'.
      simpl.
      split;
        [ clear IHxs
        | apply IHxs; trivial;
          intros; eapply H'; try eassumption; [ right; eassumption ] ].
      specialize (fun prefix idx it its H Hvalid' n offset len Heqb pf pf' pit pits => H' it its idx offset len Hvalid' Heqb n pf pf' pit pits prefix (or_introl H)).
      clear -H' H.
      induction x as [ | it its IHx ].
      { simpl; constructor. }
      { simpl.
        split;
          [ clear IHx
          | apply IHx;
            intros; subst; eapply (H' (_::_)); try eassumption; reflexivity ].
        intros idx Hvalid Heqb.
        specialize (H' nil idx _ _ eq_refl).
        specialize_by assumption.
        specialize (H' _ _ H).
        hnf.
        intros [ n [ pit pits ] ]; simpl in * |- .
        destruct (Compare_dec.le_ge_dec n (length (substring offset len str))).
        { exists n; repeat split; eauto.
          specialize (fun pf =>
                        H' _ pf
                           (parse_of_item__of__minimal_parse_of_item pit)
                           (parse_of_production__of__minimal_parse_of_production pits)).
          specialize_by assumption.
          rewrite Min.min_r by assumption.
          apply H'; eauto. }
        { exists (length (substring offset len str)).
          specialize (H' _ (reflexivity _)).
          rewrite Min.min_idempotent.
          rewrite !substring_length_no_min in * by assumption.
          repeat match goal with
                   | [ H : context[length (substring _ _ _)] |- _ ] => rewrite !substring_length_no_min in H by assumption
                 end.
          pose proof (fun H => expand_minimal_parse_of_item (str' := take len (substring offset len str)) (or_introl (reflexivity _)) (reflexivity _) (or_introl (reflexivity _)) H pit) as pit'; clear pit.
          pose proof (fun H => expand_minimal_parse_of_production (str' := drop len (substring offset len str)) (or_introl (reflexivity _)) (reflexivity _) (or_introl (reflexivity _)) H pits) as pits'; clear pits.
          set (s := substring offset len str) in *.
          specialize_by
            ltac:(first [ rewrite ?take_long, ?drop_long
                          by first [ subst s; reflexivity
                                   | subst s; rewrite substring_length_no_min by assumption; omega ];
                          reflexivity
                        | apply bool_eq_empty; rewrite ?drop_length; subst s;
                          rewrite substring_length_no_min by assumption;
                          omega ]).
          specialize_by assumption.
          repeat split; try assumption.
          apply H'.
          { eapply (@parse_of_item__of__minimal_parse_of_item Char splitter _ _ _ _); eassumption. }
          { eapply (@parse_of_production__of__minimal_parse_of_production Char splitter _ _ _ _ _); eassumption. } } } }
  Qed.

  Local Instance parser_completeness_data : @boolean_parser_completeness_dataT' Char _ _ G parser_data
    := optsplitdata_correct.

  Program Definition parser (Hvalid : grammar_valid G) : Parser G splitter
    := {| has_parse str := parse_nonterminal (data := parser_data) str (Start_symbol G);
          parse str := SimpleRecognizer.parse_nonterminal (data := parser_data) str (Start_symbol G);
          has_parse_sound str Hparse := parse_nonterminal_sound (data := parser_data) Hvalid _ _ Hparse;
          has_parse_complete str p := _ |}.
  Next Obligation.
  Proof.
    dependent destruction p.
    pose proof (fun pf => @parse_of_nonterminal_complete Char splitter _ _ G _ _ rdp_list_rdata' Hvalid str (Start_symbol G) pf p) as H'.
    apply H'; assumption.
  Qed.
  Next Obligation.
  Proof.
    erewrite SimpleBooleanRecognizerEquality.parse_nonterminal_eq; reflexivity.
  Qed.
End implementation.
