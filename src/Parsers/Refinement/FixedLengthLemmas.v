Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretation.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.

Set Implicit Arguments.

Local Open Scope grammar_fixedpoint_scope.

Definition length_result_lub (l1 l2 : nat) : lattice_for nat
  := if beq_nat l1 l2 then constant l1 else ⊤.

Global Instance length_result_lattice : grammar_fixedpoint_lattice_data nat.
Proof.
  refine {| prestate_lt x y := false;
            prestate_beq := beq_nat;
            preleast_upper_bound := length_result_lub |};
    try abstract (repeat match goal with
                         | [ |- is_true true ] => reflexivity
                         | _ => congruence
                         | [ |- Equivalence _ ] => split; hnf
                         | [ |- Proper _ _ ] => unfold Proper, respectful
                         | _ => progress intros
                         | _ => progress simpl in *
                         | _ => progress unfold length_result_lub, is_true in *
                         | _ => progress subst
                         | [ H : constant _ = constant _ |- _ ] => inversion H; clear H
                         | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true_iff in H
                         | _ => rewrite <- beq_nat_refl
                         | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
                         | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                         end).
  { unfold Basics.flip; constructor; simpl; intros ? H; exfalso; clear -H.
    abstract congruence. }
Defined.

Global Instance length_result_aidata {Char} : @AbstractInterpretation Char nat _.
Proof.
  refine {| on_terminal t := constant 1;
            on_nil_production := constant 0;
            precombine_production x y := constant (x + y) |}.
  { simpl; unfold state, state_beq, prestate_beq, length_result_lattice.
    abstract (
        repeat match goal with
               | _ => intro
               | _ => progress simpl in *
               | _ => progress unfold is_true in *
               | _ => progress subst
               | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true_iff in H
               | [ |- beq_nat _ _ = true ] => apply beq_nat_true_iff
               | _ => reflexivity
               end
      ). }
Defined.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition length_result_accurate
             (P : String -> Prop) (n : nat)
    : Prop
    := forall str, P str -> length str = n.

  Local Ltac t_Proper_step :=
    idtac;
    match goal with
    | _ => tauto
    | _ => congruence
    | [ |- is_true _ ] => reflexivity
    | _ => omega_with_min_max
    | _ => progress unfold respectful, pointwise_relation, length_result_accurate, length_result_accurate, ensemble_bottom, ensemble_top, ensemble_least_upper_bound, ensemble_on_terminal, ensemble_combine_production, lattice_for_related, not, length_result_lub, prestate_le in *
    | _ => intro
    | _ => progress subst
    | [ H : is_true (beq_nat _ _) |- _ ] => apply beq_nat_true_iff in H
    | _ => progress destruct_head lattice_for
    | [ |- iff _ _ ] => split
    | [ H : forall x y, _ -> (_ <-> _) |- _ ] => specialize (fun x => H x x (reflexivity _))
    | _ => progress split_iff
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => solve [ eauto using length_singleton with nocore
                 | exfalso; eauto with nocore ]
    | [ H : forall str, length str = ?v |- _ ] => apply not_all_lengths in H
    | [ H : forall v, True -> _ |- _ ] => specialize (fun v => H v I)
    | [ H : String -> False |- _ ] => apply not_not_string in H
    | [ H : forall a, ?x a = ?y a, H' : context[?x _] |- _ ] => setoid_rewrite H in H'
    | [ H : forall a, ?x a = ?y a, H' : context[?x _] |- _ ] => rewrite H in H'
    | [ H : forall a, ?x a = ?y a |- _ ] => is_var x; clear x H
    | [ H : constant _ = constant _ |- _ ] => inversion H; clear H
    | _ => progress unfold state_le in *
    | _ => progress simpl in *
    | [ H : forall v, (forall x y, True) -> _ |- _ ]
      => specialize (fun v => H v (fun _ _ => I))
    | [ H : forall P str, P str -> @?A str |- _ ]
      => specialize (fun str => H (fun _ => True) str I)
    | [ H : _ |- _ ] => rewrite Bool.orb_false_r in H
    | _ => rewrite Bool.orb_false_r
    | [ |- is_true (beq_nat _ _) ] => apply beq_nat_true_iff
    | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true_iff in H
    | [ H : forall P, (forall str, P str -> @?P' str) -> forall str', P str' -> @?Q' str' |- _ ]
      => specialize (H P' (fun str pf => pf))
    | [ H : forall str, length str = ?n -> length str = ?n' |- _ ]
      => let H' := fresh in
         destruct (strings_nontrivial n) as [? H'];
         specialize (H _ H')
    | [ H : forall str, length str = ?n -> ?T |- _ ]
      => let H' := fresh in
         destruct (strings_nontrivial n) as [? H'];
         specialize (H _ H')
    | [ H : forall str, ?P str -> @?Q str, H' : ?P ?str' |- _ ]
      => is_var P; pose proof (H _ H'); clear P H H'
    | _ => progress rewrite ?take_length, ?drop_length
    | _ => progress destruct_head or
    | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
    | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
    end.

  Local Ltac t_Proper := repeat t_Proper_step.

  Section instances.
    Local Obligation Tactic := t_Proper.
    Global Program Instance length_result_accurate_Proper0
      : Proper ((beq ==> iff) ==> eq ==> iff) length_result_accurate.
    Global Program Instance length_result_accurate_Proper1
      : Proper ((beq ==> iff) ==> prestate_beq ==> iff) length_result_accurate.
    Global Program Instance length_result_accurate_Proper2
      : Proper (pointwise_relation _ iff ==> eq ==> iff) length_result_accurate.
    Global Program Instance length_result_accurate_Proper3
      : Proper (pointwise_relation _ iff ==> prestate_beq ==> iff) length_result_accurate.
    Global Program Instance length_result_accurate_Proper4
      : Proper (pointwise_relation _ eq ==> eq ==> iff) length_result_accurate.
    Global Program Instance length_result_accurate_Proper5
      : Proper (pointwise_relation _ eq ==> prestate_beq ==> iff) length_result_accurate.
  End instances.

  Global Instance length_result_aicdata
    : AbstractInterpretationCorrectness length_result_accurate.
  Proof.
    split; try exact _;
      try solve [ t_Proper ].
  Qed.
End correctness.

Definition length_result := lattice_for nat.
Coercion collapse_length_result (v : length_result) : option nat
  := Eval cbv [collapse_lattice_for] in collapse_lattice_for v.

Local Hint Immediate compile_item_data_of_abstract_interpretation : typeclass_instances.

Definition length_of_any {Char} (G : pregrammar' Char)
           (compiled_productions : list (opt.productions state))
: String.string -> length_result
  := fun nt => lookup_state (fold_grammar G compiled_productions) (opt.compile_nonterminal nt).

Section has_only_terminals.
  Context {Char}
          {HSLM : StringLikeMin Char}
          {HSL : StringLike Char}
          {HSLP : StringLikeProperties Char}
          (G : pregrammar' Char)
          compiled_productions
          (compiled_productions_correct : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions)
          {n}
          nt
          (H : length_of_any G compiled_productions nt = constant n)
          (str : String).

  Lemma has_only_terminals_parse_of_item_length
        (p : parse_of_item G str (NonTerminal nt))
    : length str = n.
  Proof.
    unfold length_of_any in H.
    eapply fold_grammar_correct_item in p; [ | eassumption ].
    rewrite H in p.
    destruct p; intuition.
  Qed.

  Lemma has_only_terminals_parse_of_length
        (p : parse_of G str (Lookup G nt))
    : length str = n.
  Proof.
    unfold length_of_any in H.
    eapply fold_grammar_correct in p; [ | eassumption ].
    rewrite H in p.
    destruct p; intuition.
  Qed.
End has_only_terminals.
