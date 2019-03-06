Require Import Coq.omega.Omega.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.Enumerable.BoolProp.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Common.Gensym.
Require Import Fiat.Common.Tactics.BreakMatch.
Require Import Fiat.Common.Tactics.DestructHead.

Local Open Scope type_scope.

Definition default_nonterminal_carrierT : Type := nat.
(** (nonterminal, production_index, drop_count) *)
Definition default_production_carrierT : Type
  := default_nonterminal_carrierT * (nat * nat).

Global Instance dnc_BoolDecR : BoolDecR default_nonterminal_carrierT := _.
Global Instance dnc_BoolDec_bl : BoolDec_bl (@eq default_nonterminal_carrierT)
  := _.
Global Instance dnc_BoolDec_lb : BoolDec_lb (@eq default_nonterminal_carrierT)
  := _.

Local Ltac eassumption' :=
  idtac;
  match goal with
    | [ H : _ |- _ ] => solve [ refine H ]
  end.

Definition default_production_carrierT_beq : default_production_carrierT -> default_production_carrierT -> bool
  := Equality.beq.
Definition default_production_carrierT_bl
: forall {x y}, default_production_carrierT_beq x y = true -> x = y
  := Equality.bl.
Definition default_production_carrierT_lb
: forall {x y}, x = y -> default_production_carrierT_beq x y = true
  := Equality.lb.

Section grammar.
  Context {Char} {G : pregrammar' Char}.

  Local Notation valid_nonterminals := (List.map fst (pregrammar_productions G)).

  Definition some_invalid_nonterminal
    := gensym valid_nonterminals.

  Lemma some_invalid_nonterminal_invalid'
  : ~List.In some_invalid_nonterminal valid_nonterminals.
  Proof.
    apply gensym_fresh.
  Qed.
  Lemma some_invalid_nonterminal_invalid
  : ~List.In some_invalid_nonterminal (Valid_nonterminals G).
  Proof.
    intro H; apply some_invalid_nonterminal_invalid'.
    assumption.
  Qed.

  Definition default_to_nonterminal
  : default_nonterminal_carrierT -> String.string
    := fun nt => List.nth nt valid_nonterminals some_invalid_nonterminal.

  Definition default_of_nonterminal
  : String.string -> default_nonterminal_carrierT
    := fun nt => List.first_index_default
                   (string_beq nt)
                   (List.length valid_nonterminals)
                   valid_nonterminals.

  Lemma default_find_to_nonterminal idx
  : List.first_index_error
      (string_beq (default_to_nonterminal idx))
      valid_nonterminals
    = bool_rect
        (fun _ => option _)
        (Some idx)
        (None)
        (Compare_dec.leb (S idx) (List.length valid_nonterminals)).
  Proof.
    pose proof (nonterminals_unique G) as HNoDup.
    hnf in HNoDup.
    unfold pregrammar_nonterminals in *.
    destruct (Compare_dec.leb (S idx) (List.length valid_nonterminals)) eqn:H0; simpl;
      [ apply Compare_dec.leb_complete in H0
      | apply Compare_dec.leb_complete_conv in H0 ].
      { generalize dependent idx.
        unfold default_to_nonterminal, default_to_nonterminal, Valid_nonterminals, grammar_of_pregrammar, pregrammar_nonterminals.
        replace valid_nonterminals with (uniquize string_beq valid_nonterminals) by (rewrite HNoDup; reflexivity).
        induction valid_nonterminals as [|x xs IHxs].
        { simpl; intros; omega. }
        { simpl.
          simpl in *.
          destruct (list_bin string_beq x (uniquize string_beq xs)) eqn:H''; try assumption.
          { apply (f_equal (@List.length _)) in HNoDup.
            simpl in *.
            pose proof (uniquize_shorter xs string_beq) as H'.
            rewrite HNoDup in H'.
            exfalso; clear -H'.
            omega. }
          apply (f_equal (@List.tl _)) in HNoDup; simpl in *.
          specialize (IHxs HNoDup).
          intros [|idx].
          { simpl.
            rewrite (string_lb eq_refl); trivial. }
          { simpl; intros H'.
            specialize (IHxs idx (Le.le_S_n _ _ H')).
            rewrite first_index_helper_first_index_error, IHxs by omega.
            apply first_index_error_Some_correct in IHxs.
            repeat match goal with
                     | _ => exact (@string_lb)
                     | _ => progress simpl in *
                     | [ H : and _ _ |- _ ] => destruct H
                     | [ H : ex _ |- _ ] => destruct H
                     | [ |- context[if ?E then _ else _] ] => destruct E eqn:?
                     | _ => reflexivity
                     | [ |- Some _ = Some _ ] => apply f_equal
                     | [ |- 0 = S _ ] => exfalso
                     | [ H : string_beq _ _ = true |- _ ] => apply string_bl in H
                     | _ => progress subst
                     | [ H : _ = ?x |- _ ] => is_var x; subst x
                     | [ H : S _ = S _ |- _ ] => apply (f_equal pred) in H
                     | [ H : List.length (uniquize _ _) = List.length _ |- _ ]
                       => apply uniquize_length in H
                     | [ H : uniquize ?beq ?ls = ?ls, H' : context[uniquize ?beq ?ls] |- _ ]
                       => rewrite H in H'
                     | [ H : list_bin _ _ _ = false |- False ]
                       => rewrite list_in_lb in H; [ discriminate | | ]
                     | [ |- List.In (List.nth _ _ _) _ ] => apply List.nth_In; omega
                     | [ |- context[List.nth_error ?n ?ls] ] => destruct (List.nth_error n ls) eqn:?
                     | _ => congruence
                     | _ => progress unfold BoolFacts.Bool.bool_rect_nodep in *
                   end. } } }
      { unfold default_to_nonterminal, default_to_nonterminal.
        simpl.
        rewrite List.nth_overflow by omega.
        apply first_index_error_None_correct; intros elem H''.
        destruct (string_beq some_invalid_nonterminal elem) eqn:H'''; trivial.
        apply string_bl in H'''.
        subst.
        apply some_invalid_nonterminal_invalid' in H''; destruct H''. }
  Qed.

  Lemma list_to_productions_to_nonterminal nt
  : Lookup_string G (default_to_nonterminal nt)
    = Lookup_idx G nt.
  Proof.
    unfold Lookup_string, Lookup_idx.
    unfold list_to_productions at 1; simpl.
    unfold productions, production in *.
    rewrite <- find_first_index_error by exact bl.
    rewrite default_find_to_nonterminal.
    set (ls' := pregrammar_productions G); clearbody ls'.
    revert nt; induction ls' as [|x xs IHxs]; simpl; intro nt;
    destruct nt; simpl; trivial;
    rewrite <- IHxs; clear IHxs.
    edestruct @Compare_dec.leb; simpl; reflexivity.
  Qed.

  Lemma nth_error_default_to_nonterminal nt_idx
    : List.nth_error (pregrammar_productions G) nt_idx
      = if nt_idx <? List.length (pregrammar_productions G)
        then Some (default_to_nonterminal nt_idx, Lookup_idx G nt_idx)
        else None.
  Proof.
    destruct (nt_idx <? List.length (pregrammar_productions G)) eqn:Hlt.
    { apply Nat.ltb_lt in Hlt.
      unfold Lookup_idx, default_to_nonterminal.
      rewrite !nth_error_nth.
      repeat match goal with
             | _ => reflexivity
             | _ => discriminate
             | _ => omega
             | _ => break_innermost_match_step
             | _ => progress subst
             | _ => progress destruct_head' sig
             | _ => progress destruct_head' and
             | [ H : ?x = Some ?y, H' : ?x = Some ?z |- _ ]
               => assert (y = z) by congruence; (subst y || subst z)
             | [ H : ?x = Some _ |- ?x = _ ] => rewrite H
             | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ]
               => apply ListFacts.nth_error_map'_strong in H
             | [ H : List.nth_error (List.map ?f ?ls) ?idx = None |- _ ]
               => let H' := fresh in
                  destruct (List.nth_error ls idx) eqn:H';
                    [ eapply List.map_nth_error in H'; rewrite H in H'; congruence
                    | clear H ]
             | _ => progress destruct_head' prod
             | [ |- None = Some _ ] => exfalso
             | [ H : List.nth_error _ _ = None |- False ]
               => apply List.nth_error_None in H
             end. }
    { apply List.nth_error_None.
      apply Nat.ltb_ge in Hlt; assumption. }
  Qed.

  Section index.
    Context (idx : default_production_carrierT).

    Let nt_idx := fst idx.
    Let nts := (Lookup_idx G nt_idx).
    Let ps_idx := List.length nts - S (fst (snd idx)).
    Let drop_count := snd (snd idx).
    Let ps := (List.nth ps_idx nts nil).

    Definition default_to_production : production Char
    := List.drop drop_count ps.

    Definition default_production_tl : default_production_carrierT
      := (nt_idx,
          (fst (snd idx),
           if Compare_dec.leb (S drop_count) (List.length ps)
           then S drop_count
           else drop_count)).

    Definition default_production_carrier_valid : bool
      := ((Compare_dec.leb (S nt_idx) (List.length (pregrammar_productions G)))
            && ((Compare_dec.leb (S (fst (snd idx))) (List.length nts))
                  && (Compare_dec.leb drop_count (List.length ps))))%bool.
  End index.

  Global Instance default_production_carrier_valid_enumerable
  : Enumerable { idx : default_production_carrierT | is_true (default_production_carrier_valid idx) }.
  Proof.
    exact _.
  Defined.
End grammar.
