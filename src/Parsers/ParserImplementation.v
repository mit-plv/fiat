(** * Implementation of simply-typed interface of the parser *)
Require Export Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.BooleanRecognizer Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListFacts.

Set Implicit Arguments.

Local Open Scope list_scope.

Section implementation.
  Context {Char} {G : grammar Char}.
  Context (splitter : Splitter G).

  Local Instance parser_data : @boolean_parser_dataT Char _ :=
    { predata := rdp_list_predata (G := G);
      split_string_for_production it its str
      := splits_for splitter str it its;
      select_production_rules prods str
      := rules_for splitter str prods }.

  Local Instance parser_completeness_data : @boolean_parser_completeness_dataT' Char _ G parser_data
    := { split_string_for_production_complete len0 valid str pf nt Hvalid := _;
         select_production_rules_complete len0 valid str pf nt Hvalid := _ }.
  Proof.
    { unfold is_valid_nonterminal in Hvalid; simpl in Hvalid.
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
            { apply bool_eq_empty; rewrite drop_length; omega. } } } } }
    { unfold is_valid_nonterminal in Hvalid; simpl in Hvalid.
      unfold rdp_list_is_valid_nonterminal in Hvalid; simpl in Hvalid.
      hnf in Hvalid.
      apply Equality.list_in_bl in Hvalid; [ | apply @Equality.string_bl ].
      generalize (@rules_for_complete Char G splitter str _ Hvalid).
      clear Hvalid.
      simpl.
      intros H p.
      set (prods := G nt) in p.
      assert (H' : { prefix : _ | prefix ++ prods = G nt }) by (eexists nil; reflexivity).
      clearbody prods.
      generalize dependent (G nt); intro Gnt; clear nt; intros.
      induction p; destruct H' as [prefix H']; subst.
      { exists (List.length prefix).
        specialize (H (List.length prefix)).
        let m := match goal with m : minimal_parse_of_production _ _ _ _ |- _ => constr:m end in
        pose proof m as m';
          apply (@parse_of_production__of__minimal_parse_of_production) in m'.
        destruct m' as [p Hp].
        specialize (fun H' => H _ H' p).
        rewrite !nth_error_length_app in H |- *; simpl in *.
        specialize (H eq_refl).
        split; [ | eexists; split; [ reflexivity | eassumption ] ].
        apply H.
        erewrite <- parse_of_production_respectful_refl.
        eapply expand_forall_parse_of_production;
          [ ..
          | rewrite parse_of_production_respectful_refl; eassumption ].
        simpl; intros ????? H0.
        unfold rdp_list_is_valid_nonterminal in *.
        apply list_in_bl in H0; [ | apply @string_bl ]; assumption. }
      { specialize_by assumption.
        apply IHp.
        eexists (prefix ++ [_]); simpl.
        rewrite <- List.app_assoc; simpl.
        reflexivity. } }
    Grab Existential Variables.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.

  Program Definition parser' : Parser G splitter
    := {| has_parse str := parse_nonterminal (G := G) (data := parser_data) str (Start_symbol G);
          has_parse_sound str Hparse := let p := parse_nonterminal_sound G _ _ Hparse in
                                        existT _ (projT1 p) ((fun H => _) (projT2 p));
          has_parse_complete str p Hp := _ |}.
  Next Obligation.
  Proof.
    erewrite <- parse_of_item_respectful_refl.
    eapply expand_forall_parse_of_item;
    [ ..
    | rewrite parse_of_item_respectful_refl; eassumption ].
    simpl; intros ????? H0.
    unfold rdp_list_is_valid_nonterminal in *.
    apply list_in_bl in H0; [ | apply @string_bl ]; assumption.
    Grab Existential Variables.
    reflexivity.
    reflexivity.
  Qed.
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
