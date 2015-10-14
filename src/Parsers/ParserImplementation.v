(** * Implementation of simply-typed interface of the parser *)
Require Export Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.BooleanRecognizer Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Local Open Scope list_scope.

Section implementation.
  Context {Char} {G : grammar Char}.
  Context (splitter : Splitter G).

  Local Instance parser_data : @boolean_parser_dataT Char _ :=
    { predata := rdp_list_predata (G := G);
      split_string_for_production it its str
      := splits_for splitter str it its }.

  Local Instance parser_completeness_data : @boolean_parser_completeness_dataT' Char _ G parser_data
    := { split_string_for_production_complete str0 valid str pf nt Hvalid := _ }.
  Proof.
    unfold is_valid_nonterminal in Hvalid; simpl in Hvalid.
    unfold rdp_list_is_valid_nonterminal in Hvalid; simpl in Hvalid.
    hnf in Hvalid.
    apply Equality.list_in_bl in Hvalid; [ | apply @Equality.string_bl ].
    generalize (fun it its n pf pit pits prefix H' pitH pitsH => @splits_for_complete Char G splitter str it its n pf (ex_intro _ nt (ex_intro _ prefix (conj Hvalid H'))) pit pits pitH pitsH).
    clear Hvalid.
    induction (G nt) as [ | x xs IHxs ].
    { intros; constructor. }
    { intro H'.
      Opaque split_string_for_production.
      simpl.
      Transparent split_string_for_production.
      split;
        [ clear IHxs
        | apply IHxs;
          intros; eapply H'; try eassumption; [ right; eassumption ] ].
      specialize (fun prefix it its H n pf pit pits pitH pitsH => H' it its n pf pit pits prefix (or_introl H) pitH pitsH).
      clear -H'.
      induction x as [ | it its IHx ].
      { simpl; constructor. }
      { Opaque split_string_for_production.
        simpl.
        Transparent split_string_for_production.
        split;
          [ clear IHx
          | apply IHx;
            intros; subst; eapply (H' (_::_)); try eassumption; reflexivity ].
        specialize (H' nil it its eq_refl).
        hnf.
        intros [ n [ pit pits ] ]; simpl in * |- .
        destruct (Compare_dec.le_ge_dec n (length str)).
        { exists n; repeat split; eauto.
          specialize (fun pf =>
                        H' _ pf
                           (projT1 (parse_of_item__of__minimal_parse_of_item pit))
                           (projT1 (parse_of_production__of__minimal_parse_of_production pits))).
          rewrite Min.min_r by assumption.
          apply H'; eauto.
          { erewrite <- parse_of_item_respectful_refl.
            eapply expand_forall_parse_of_item;
              [ ..
              | rewrite parse_of_item_respectful_refl;
                exact (projT2 (parse_of_item__of__minimal_parse_of_item pit)) ];
              try reflexivity; simpl.
            simpl; intros ????? H0.
            unfold rdp_list_is_valid_nonterminal in *.
            apply list_in_bl in H0; [ | apply @string_bl ]; assumption. }
          { erewrite <- parse_of_production_respectful_refl.
            eapply expand_forall_parse_of_production;
              [ ..
              | rewrite parse_of_production_respectful_refl;
                exact (projT2 (parse_of_production__of__minimal_parse_of_production pits)) ];
              try reflexivity; simpl.
            simpl; intros ????? H0.
            unfold rdp_list_is_valid_nonterminal in *.
            apply list_in_bl in H0; [ | apply @string_bl ]; assumption. } }
        { exists (length str).
          specialize (H' (length str) (reflexivity _)).
          pose proof (fun H => expand_minimal_parse_of_item (str' := take (length str) str) (or_introl (reflexivity _)) (reflexivity _) (or_introl (reflexivity _)) H pit) as pit'; clear pit.
          pose proof (fun H => expand_minimal_parse_of_production (str' := drop (length str) str) (or_introl (reflexivity _)) (reflexivity _) (or_introl (reflexivity _)) H pits) as pits'; clear pits.
          rewrite Min.min_idempotent.
          refine ((fun ret => let pit'' := pit' (fst (snd ret)) in
                              let pits'' := pits' (snd (snd ret)) in
                              ((H' (projT1 (fst (fst ret) pit'')) (projT1 (snd (fst ret) pits'')) (projT2 (fst (fst ret) pit'')) (projT2 (snd (fst ret) pits'')), pit''), pits'')) _); repeat split.
          { intro p.
            exists (projT1 (@parse_of_item__of__minimal_parse_of_item Char splitter G _ _ _ _ _ p)).
            erewrite <- parse_of_item_respectful_refl.
            eapply expand_forall_parse_of_item;
              [ ..
              | rewrite parse_of_item_respectful_refl;
                exact (projT2 (parse_of_item__of__minimal_parse_of_item p)) ];
              try reflexivity; simpl.
            simpl; intros ????? H0.
            unfold rdp_list_is_valid_nonterminal in *.
            apply list_in_bl in H0; [ | apply @string_bl ]; assumption. }
          { intro p.
            exists (projT1 (@parse_of_production__of__minimal_parse_of_production Char splitter G _ _ _ _ _ p)).
            erewrite <- parse_of_production_respectful_refl.
            eapply expand_forall_parse_of_production;
              [ ..
              | rewrite parse_of_production_respectful_refl;
                exact (projT2 (parse_of_production__of__minimal_parse_of_production p)) ];
              try reflexivity; simpl.
            simpl; intros ????? H0.
            unfold rdp_list_is_valid_nonterminal in *.
            apply list_in_bl in H0; [ | apply @string_bl ]; assumption. }
          { rewrite !take_long; (assumption || reflexivity). }
          { apply bool_eq_empty; rewrite drop_length; omega. } } } }
    Grab Existential Variables.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.

  Program Definition parser : Parser G splitter
    := {| has_parse str := parse_nonterminal (G := G) (data := parser_data) str (Start_symbol G);
          has_parse_sound str Hparse := parse_nonterminal_sound G _ _ Hparse;
          has_parse_complete str p Hp := _ |}.
  Next Obligation.
  Proof.
    dependent destruction p.
    pose proof (@parse_nonterminal_complete Char splitter _ G _ _ rdp_list_rdata' str (Start_symbol G) p) as H'.
    apply H'.
    rewrite <- (parse_of_item_respectful_refl (pf := reflexivity _)).
    rewrite <- (parse_of_item_respectful_refl (pf := reflexivity _)) in Hp.
    eapply expand_forall_parse_of_item; [ | reflexivity.. | eassumption ].
    simpl.
    unfold rdp_list_is_valid_nonterminal; simpl.
    intros ? ? ? ? ? H0.
    apply Equality.list_in_lb; [ apply @Equality.string_lb | ]; assumption.
  Qed.
End implementation.
