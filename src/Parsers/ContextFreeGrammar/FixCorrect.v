Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.

Set Implicit Arguments.
Local Open Scope grammar_fixedpoint_scope.

Section grammar_fixedpoint.
  Context {Char : Type}.

  Context (gdata : grammar_fixedpoint_data)
          (G : pregrammar' Char).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Lemma pre_Fix_grammar_fixedpoint_correct
        (P : default_nonterminal_carrierT -> state gdata -> Type)
        (Pinit : forall nt, is_true (is_valid_nonterminal initial_nonterminals_data nt)
                            -> P nt (initial_state nt))
        (Pbot : forall nt, is_valid_nonterminal initial_nonterminals_data nt = false
                           -> P nt ⊥)
        (P_glb : forall nt a b, P nt a -> P nt b -> P nt (a ⊓ b))
        (IH : forall nt st v,
            st nt = v
            -> P nt v
            -> P nt (step_constraints gdata st nt v))
    : forall nt, P nt (lookup_state (pre_Fix_grammar gdata G) nt).
  Proof.
    specialize (fun nt st => IH nt st _ eq_refl).
    assert (Hvalid' : forall nt,
               is_true (is_valid_nonterminal initial_nonterminals_data nt)
               -> match FMapPositive.PositiveMap.find
                          (nonterminal_to_positive nt)
                          (aggregate_state_max gdata G)
                  with
                  | Some v => P nt v
                  | None => False
                  end).
    { intros nt Hvalid.
      pose proof (find_aggregate_state_max_spec gdata G (nonterminal_to_positive nt)) as Hvalid'.
      rewrite nonterminal_to_positive_to_nonterminal in Hvalid'.
      edestruct Hvalid' as [Hvalid'0 Hvalid'1].
      rewrite Hvalid'1 by (split; [ reflexivity | assumption ]).
      eauto. }
    intro nt.
    destruct (is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt) eqn:Hvalid.
    { revert nt Hvalid.
      pose proof (fun nt (pf : is_true (is_valid_nonterminal (@initial_nonterminals_data _ (@rdp_list_predata _ G)) nt))
                  => match eq_sym pf in (_ = b)
                           return (if b then initial_state nt else ⊥) =
                                  lookup_state (aggregate_state_max gdata G) nt
                                  -> _
                     with
                     | eq_refl => eq_rect _ (P nt) (Pinit _ pf) _
                     end (eq_sym (lookup_state_aggregate_state_max gdata G nt))) as Pinit'.
      unfold pre_Fix_grammar, pre_Fix_grammar_helper.
      let Rwf := lazymatch goal with |- appcontext[Fix ?Rwf _ _ ?v] => Rwf end in
      let v := lazymatch goal with |- appcontext[Fix Rwf _ _ ?v] => v end in
      pose proof (fun nt => IH nt (lookup_state v)) as IHv;
      specialize (fun nt pf => IHv nt (Pinit' _ pf));
        induction (Rwf v) as [a Ha IHa].
      rewrite Init.Wf.Fix_eq by (intros; edestruct Sumbool.sumbool_of_bool; trivial).
      edestruct Sumbool.sumbool_of_bool; [ intros; apply Pinit'; assumption | ].
      fold (pre_Fix_grammar_helper (gdata := gdata) G) in *.
      destruct (aggregate_state_eq (aggregate_step a) a) eqn:Heq.
      { change (is_true (aggregate_state_eq (aggregate_step a) a)) in Heq.
        intros nt Hvalid.
        remember (lookup_state (pre_Fix_grammar_helper G (aggregate_step a)) nt) as st eqn:Hst.
        rewrite pre_Fix_grammar_helper_fixed in Hst by (rewrite !Heq; reflexivity).
        rewrite Heq in Hst.
        subst.
        eauto. }
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
                 | _ => progress unfold lookup_state, option_map, option_rect in *
                 | [ H : forall nt, is_true (?P nt) -> _, H' : is_true (?P _) |- _ ]
                   => specialize (H _ H')
                 | [ |- ?P ?nt (_ ⊓ _) ] => apply P_glb
                 | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
                 | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end. } }
    { rewrite lookup_state_invalid_pre_Fix_grammar by assumption; eauto. }
  Qed.
End grammar_fixedpoint.
