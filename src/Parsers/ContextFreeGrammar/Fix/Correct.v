Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Properties.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope grammar_fixedpoint_scope.

Section grammar_fixedpoint.
  Context {Char : Type}.

  Context (gdata : grammar_fixedpoint_data)
          (G : pregrammar' Char).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Lemma pre_Fix_grammar_fixedpoint_correct_valid
        (P : default_nonterminal_carrierT -> state gdata -> Type)
        (Pinit : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt)
                            -> P nt ⊥)
        (IH : forall nt st v,
            st nt = v
            -> is_true (is_valid_nonterminal initial_nonterminals_data nt)
            -> P nt v
            -> P nt (v ⊔ step_constraints gdata st nt v))
    : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt) -> P nt (lookup_state (pre_Fix_grammar gdata initial_nonterminals_data) nt).
  Proof.
    specialize (fun nt st => IH nt st _ eq_refl).
    assert (Hvalid' : forall nt,
               is_true (is_valid_nonterminal initial_nonterminals_data nt)
               -> match FMapPositive.PositiveMap.find
                          (nonterminal_to_positive nt)
                          (aggregate_state_max gdata initial_nonterminals_data)
                  with
                  | Some v => P nt v
                  | None => False
                  end).
    { intros nt Hvalid.
      pose proof (find_aggregate_state_max_spec gdata G (nonterminal_to_positive nt)) as Hvalid'.
      rewrite nonterminal_to_positive_to_nonterminal in Hvalid'.
      edestruct Hvalid' as [Hvalid'0 Hvalid'1].
      simpl in *.
      rewrite Hvalid'1 by (split; [ reflexivity | assumption ]).
      eauto. }
    pose proof (fun nt (pf : is_true (is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt))
                => match eq_sym pf in (_ = b)
                         return (if b then ⊥ else ⊤) =
                                lookup_state (aggregate_state_max gdata initial_nonterminals_data) nt
                                -> _
                   with
                   | eq_refl => eq_rect _ (P nt) (Pinit _ pf) _
                   end (eq_sym (lookup_state_aggregate_state_max gdata G nt))) as Pinit'.
    unfold pre_Fix_grammar, pre_Fix_grammar_helper.
    let Rwf := lazymatch goal with |- context[Fix ?Rwf _ _ ?v] => Rwf end in
    let v := lazymatch goal with |- context[Fix Rwf _ _ ?v] => v end in
    pose proof (fun nt => IH nt (lookup_state v)) as IHv;
      specialize (fun nt pf => IHv nt pf (Pinit' _ pf));
      induction (Rwf v) as [a Ha IHa].
    rewrite Init.Wf.Fix_eq by (intros; edestruct Sumbool.sumbool_of_bool; trivial).
    edestruct Sumbool.sumbool_of_bool; [ intros; apply Pinit'; assumption | ].
    fold (pre_Fix_grammar_helper (gdata := gdata) initial_nonterminals_data) in *.
    destruct (aggregate_state_eq a (aggregate_step a)) eqn:Heq.
    { intuition congruence. }
    { apply step_lt in Heq.
      intros nt.
      apply IHa; eauto; intros; try apply IH;
        repeat match goal with
               | _ => progress intros
               | _ => rewrite find_aggregate_step
               | _ => rewrite lookup_state_aggregate_step
               | _ => rewrite nonterminal_to_positive_to_nonterminal
               | _ => tauto
               | _ => assumption
               | _ => progress unfold lookup_state, PositiveMapExtensions.find_default, state, option_map, option_rect in *
               | [ H : forall nt, is_true (?P nt) -> _, H' : is_true (?P _) |- _ ]
                 => specialize (H _ H')
               | [ |- ?P ?nt (_ ⊔ _) ] => apply P_lub
               | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
               | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
               end. }
  Qed.

  Lemma pre_Fix_grammar_fixedpoint_correct
        (P : default_nonterminal_carrierT -> state gdata -> Type)
        (Pbot : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt)
                          -> P nt ⊥)
        (Ptop : forall nt, is_valid_nonterminal initial_nonterminals_data nt = false
                           -> P nt ⊤)
        (IH : forall nt st v,
            st nt = v
            -> is_true (is_valid_nonterminal initial_nonterminals_data nt)
            -> P nt v
            -> P nt (v ⊔ step_constraints gdata st nt v))
    : forall nt, P nt (lookup_state (pre_Fix_grammar gdata initial_nonterminals_data) nt).
  Proof.
    intro nt.
    destruct (is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt) eqn:Hvalid.
    { apply pre_Fix_grammar_fixedpoint_correct_valid; eauto with nocore. }
    { simpl rewrite lookup_state_invalid_pre_Fix_grammar; [ | assumption ]. eauto with nocore. }
  Qed.

  Lemma pre_Fix_grammar_fixedpoint_correct_stronger'
        (P : default_nonterminal_carrierT -> state gdata -> Type)
        (Pbot : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt)
                          -> P nt ⊥)
        (Ptop : forall nt, is_valid_nonterminal initial_nonterminals_data nt = false
                           -> P nt ⊤)
        (IH : forall nt st,
            (forall nt', is_valid_nonterminal initial_nonterminals_data nt' = false -> st nt' = ⊤)
            -> (forall nt', P nt' (st nt'))
            -> P nt (st nt ⊔ step_constraints gdata st nt (st nt)))
    : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt) -> P nt (lookup_state (pre_Fix_grammar gdata initial_nonterminals_data) nt).
  Proof.
    assert (Htop : forall nt', is_valid_nonterminal initial_nonterminals_data nt' = false -> lookup_state (aggregate_state_max gdata initial_nonterminals_data) nt' = ⊤).
    { intros nt' Hinvalid.
      simpl rewrite lookup_state_aggregate_state_max; simpl in *; rewrite Hinvalid.
      reflexivity. }
    assert (Hvalid' : forall nt,
               is_true (is_valid_nonterminal initial_nonterminals_data nt)
               -> match FMapPositive.PositiveMap.find
                          (nonterminal_to_positive nt)
                          (aggregate_state_max gdata initial_nonterminals_data)
                  with
                  | Some v => P nt v
                  | None => False
                  end).
    { intros nt Hvalid.
      pose proof (find_aggregate_state_max_spec gdata G (nonterminal_to_positive nt)) as Hvalid'.
      rewrite nonterminal_to_positive_to_nonterminal in Hvalid'.
      edestruct Hvalid' as [Hvalid'0 Hvalid'1].
      simpl rewrite Hvalid'1; [ | split; [ reflexivity | assumption ] ].
      eauto. }
    pose proof (fun nt
                => match is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt as b
                         return is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt = b
                                -> (if b then ⊥ else ⊤) =
                                   lookup_state (aggregate_state_max gdata initial_nonterminals_data) nt
                                -> _
                   with
                   | true => fun pf => eq_rect _ (P nt) (Pbot _ pf) _
                   | false => fun pf => eq_rect _ (P nt) (Ptop _ pf) _
                   end eq_refl (eq_sym (lookup_state_aggregate_state_max gdata G nt))) as Pinit'.
    unfold pre_Fix_grammar, pre_Fix_grammar_helper.
    let Rwf := lazymatch goal with |- context[Fix ?Rwf _ _ ?v] => Rwf end in
    let v := lazymatch goal with |- context[Fix Rwf _ _ ?v] => v end in
    pose proof (fun nt => IH nt (lookup_state v)) as IHv;
      specialize (fun nt => IHv nt Htop Pinit');
      induction (Rwf v) as [a Ha IHa].
    rewrite Init.Wf.Fix_eq by (intros; edestruct Sumbool.sumbool_of_bool; trivial).
    edestruct Sumbool.sumbool_of_bool; [ intros; apply Pinit'; assumption | ].
    fold (pre_Fix_grammar_helper (gdata := gdata) initial_nonterminals_data) in *.
    destruct (aggregate_state_eq a (aggregate_step a)) eqn:Heq.
    { intuition congruence. }
    { apply step_lt in Heq.
      intros nt.
      simpl @nonterminal_carrierT in *.
      apply IHa; eauto; intros; try apply IH;
        repeat match goal with
               | _ => progress intros
               | _ => rewrite find_aggregate_step
               | _ => rewrite lookup_state_aggregate_step
               | _ => rewrite nonterminal_to_positive_to_nonterminal
               | _ => tauto
               | _ => assumption
               | _ => progress subst
               | _ => progress unfold lookup_state, PositiveMapExtensions.find_default, state, option_map, option_rect in *
               | [ H : ?A -> ?B, H' : ?A |- _ ]
                 => specialize (H H')
               | [ H : is_true true -> _ |- _ ] => specialize (H eq_refl)
               | [ |- is_true true ] => reflexivity
               | [ |- is_true false ] => exfalso
               | [ |- ?P ?nt (_ ⊔ _) ] => apply P_lub
               | _ => rewrite top_lub_l
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
               | [ H : forall nt : default_nonterminal_carrierT, _ |- _ ]
                 => repeat match goal with
                           | [ nt' : default_nonterminal_carrierT |- _ ]
                             => unique pose proof (H nt')
                           | [ H' : context[is_valid_nonterminal _ ?nt'] |- _ ]
                             => unique pose proof (H nt')
                           | [ |- context[is_valid_nonterminal _ ?nt'] ]
                             => unique pose proof (H nt')
                           end;
                      clear H
               | [ H : forall a b, is_true (is_valid_nonterminal ?ls ?nt) -> _ |- _ ]
                 => destruct (is_valid_nonterminal ls nt) eqn:?
               | [ P_lub : forall a b, _ -> _ -> _ -> ?P ?nt (_ ⊔ _) |- ?P ?nt (_ ⊔ _) ] => apply P_lu
               | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
               | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
               end. }
  Qed.

  Lemma pre_Fix_grammar_fixedpoint_correct_stronger
        (P : default_nonterminal_carrierT -> state gdata -> Type)
        (Pbot : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt)
                            -> P nt ⊥)
        (Ptop : forall nt, is_valid_nonterminal initial_nonterminals_data nt = false
                           -> P nt ⊤)
        (IH : forall nt st,
            (forall nt', is_valid_nonterminal initial_nonterminals_data nt' = false -> st nt' = ⊤)
            -> (forall nt', P nt' (st nt'))
            -> is_true (is_valid_nonterminal initial_nonterminals_data nt)
            -> P nt (st nt ⊔ step_constraints gdata st nt (st nt)))
    : forall nt, P nt (lookup_state (pre_Fix_grammar gdata initial_nonterminals_data) nt).
  Proof.
    intro nt.
    destruct (is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt) eqn:Hvalid.
    { apply pre_Fix_grammar_fixedpoint_correct_stronger'; eauto with nocore.
      { intros nt'' st'' Hfalse H''.
        move IH at bottom.
        specialize (IH nt'').
        let v := match type of IH with context[is_true ?v] => v end in
        destruct v eqn:Hvalid'; eauto; [].
        { rewrite Hfalse by assumption.
          rewrite top_lub_l.
          eauto. } } }
    { simpl rewrite lookup_state_invalid_pre_Fix_grammar; [ | assumption ]. eauto with nocore. }
  Qed.
End grammar_fixedpoint.
