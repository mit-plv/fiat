(** * Implementation of simply-typed interface of the parser *)
Require Export ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties.
Require Import ADTSynthesis.Parsers.BooleanRecognizer ADTSynthesis.Parsers.BooleanRecognizerCorrect.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.MinimalParseOfParse.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.

Local Open Scope list_scope.

Section implementation.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Context (splitter : Splitter String G).

  Local Notation split_stateT0
    := (fun str : String => { st : split_rep splitter | split_invariant splitter str st })
         (only parsing).

  Definition SplitAtT (n : nat) (str : StringWithSplitState String split_stateT0)
  : (StringWithSplitState String split_stateT0 * StringWithSplitState String split_stateT0).
  Proof.
    refine (let s1s2 := SplitAt n str in
            ({| string_val := fst s1s2;
                state_val := exist _ (split_take splitter n (proj1_sig (state_val str))) _ |},
             {| string_val := snd s1s2;
                state_val := exist _ (split_drop splitter n (proj1_sig (state_val str))) _ |})).
    { apply take_respectful, proj2_sig. }
    { apply drop_respectful, proj2_sig. }
  Defined.

  Local Instance parser_data : @boolean_parser_dataT _ String :=
    { predata := rdp_list_predata (G := G);
      split_stateT := split_stateT0;
      split_string_for_production it its str
      := List.map
           (fun n => SplitAtT n str)
           (splits_for splitter (proj1_sig (state_val str)) it its) }.
  Proof.
    simpl.
    intros.
    apply Forall_map; unfold compose; simpl.
    apply List.Forall_forall; intros;
    apply bool_eq_correct, SplitAt_correct.
  Defined.

  Local Instance parser_completeness_data : @boolean_parser_completeness_dataT' _ String G parser_data
    := { split_string_for_production_complete str0 valid str pf nt Hvalid := _ }.
  Proof.
    unfold is_valid_nonterminal in Hvalid; simpl in Hvalid.
    unfold rdp_list_is_valid_nonterminal in Hvalid; simpl in Hvalid.
    hnf in Hvalid.
    edestruct List.in_dec as [Hvalid' | ]; [ clear Hvalid | congruence ].
    generalize (fun it its n pf pit pits prefix H' => @splits_for_complete _ String G splitter str (proj1_sig (state_val str)) it its (proj2_sig (state_val str)) n pf pit pits (ex_intro _ nt (ex_intro _ prefix (conj Hvalid' H')))).
    clear Hvalid'.
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
      specialize (fun prefix it its H n pf pit pits => H' it its n pf pit pits prefix (or_introl H)).
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
        intros [ [ s1 s2 ] [ [ H0 pit ] pits ] ]; simpl in * |- .
        apply bool_eq_correct in H0.
        exists (SplitAtT (Length s1) str).
        destruct str as [str st]; simpl in * |- *.
        subst str.
        rewrite <- Length_correct in H'.
        specialize (H' (Length s1) (Plus.le_plus_l _ _)).
        rewrite SplitAt_concat_correct in H'; simpl in H'.
        specialize (H' (parse_of_item__of__minimal_parse_of_item pit) (parse_of_production__of__minimal_parse_of_production pits)).
        split; [ split | ];
        [
        | rewrite (SplitAt_concat_correct String s1 s2); assumption
        | rewrite (SplitAt_concat_correct String s1 s2); assumption ].
        let f := match goal with |- List.In _ (List.map ?f _) => constr:f end in
        apply (List.in_map f).
        assumption. } }
  Qed.

  Program Definition parser : Parser splitter
    := {| has_parse str st := parse_nonterminal (G := G) (data := parser_data) {| string_val := str ; state_val := exist _ st _ |} (Start_symbol G);
          has_parse_sound str st Hinv Hparse := parse_nonterminal_sound G _ _ Hparse;
          has_parse_complete str p Hp st Hinv := _ |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Proof.
    dependent destruction p.
    let st := match goal with |- parse_nonterminal {| state_val := ?st |} _ = _ => constr:st end in
    pose proof (@parse_nonterminal_complete _ String G _ _ rdp_list_rdata' {| string_val := str ; state_val := st |} (Start_symbol G) p) as H'.
    apply H'.
    eapply expand_forall_parse_of_item; [ | eassumption ]; simpl.
    unfold rdp_list_is_valid_nonterminal; simpl.
    intros ? ? ? H0.
    edestruct List.in_dec as [ | nH ]; trivial; [].
    destruct (nH H0).
  Qed.
End implementation.
