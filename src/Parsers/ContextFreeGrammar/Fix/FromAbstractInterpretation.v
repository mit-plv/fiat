Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Correct.

Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
          {irdata : Reflective.interp_RCharExpr_data Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T}.
  Context (G : pregrammar Char).

  Class AbstractInterpretationCorrectness :=
    { related : Ensemble String -> T -> Prop;
      related_ext : Proper ((beq ==> iff) ==> state_beq ==> iff) related;
      related_monotonic : forall s0 s1, s0 <= s1 <-> (forall v, related v s0 -> related v s1);
      bottom_related : (related (Full_set _) ⊥);
      on_terminal_correct
      : forall P,
          related (fun str => exists ch, Reflective.interp_RCharExpr P ch /\ str ~= [ ch ])%string_like
                  (on_terminal P);
      on_nil_production_correct
      : related (fun str => length str = 0) on_nil_production;
      combine_production_Proper_eq
      : Proper (state_beq ==> state_beq ==> state_beq) combine_production;
      combine_production_Proper_le
      : Proper (state_le ==> state_le ==> state_le) combine_production;
      combine_production_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (fun str => exists n, P1 (take n str) /\ P2 (drop n str))
                       (combine_production st1 st2)
    }.

  Context {aicdata : AbstractInterpretationCorrectness}.

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition fold_grammar : aggregate_state (fixedpoint_by_abstract_interpretation G)
    := pre_Fix_grammar _ G.
(*
  Definition state_reachable

  Lemma fixedpoint_lower_bound_for_reachable

  Lemma fold_nt_correct'
    : forall nt, Pnt nt (lookup_state fold_grammar nt).
  Proof.
    unfold fold_grammar.
    intro.
    apply pre_Fix_grammar_fixedpoint_correct_stronger.
    { apply Pnt_init. }
    { apply Pnt_bottom. }
    { intros ?? Hinvalid Hbot Hvalid.
      apply Pnt_glb; [ assumption | solve [ eauto ] | ].
      unfold step_constraints, fixedpoint_from_fold.
      unfold fold_constraints.
      apply Pnt_lift; [ assumption | ].
      apply fold_productions'_correct.
      assumption. }
  Qed.


  Lemma fold_production'_correct
        f
        (IHf : forall nt, Pnt nt (f nt))
        pat
  : Ppat pat (fold_production' (fun nt => f (of_nonterminal nt)) pat).
  Proof.
    unfold fold_production'.
    induction pat; simpl.
    { apply Ppat_nil. }
    { edestruct (_ : item _).
      { apply Ppat_cons_t; trivial. }
      { apply Ppat_cons_nt; trivial. } }
  Qed.

  Lemma fold_productions'_correct
        f
        (IHf : forall nt, Pnt nt (f nt))
        pats
  : Ppats pats (fold_productions' (fun nt => f (of_nonterminal nt)) pats).
  Proof.
    unfold fold_productions'.
    induction pats as [ | x xs IHxs ]; intros.
    { simpl; apply Ppats_nil. }
    { simpl; apply Ppats_cons; trivial; [].
      { apply fold_production'_correct; trivial. } }
  Qed.

  Lemma fold_nt_correct'
    : forall nt, Pnt nt (lookup_state fold_grammar nt).
  Proof.
    unfold fold_grammar.
    intro.
    apply pre_Fix_grammar_fixedpoint_correct_stronger.
    { apply Pnt_init. }
    { apply Pnt_bottom. }
    { intros ?? Hinvalid Hbot Hvalid.
      apply Pnt_glb; [ assumption | solve [ eauto ] | ].
      unfold step_constraints, fixedpoint_from_fold.
      unfold fold_constraints.
      apply Pnt_lift; [ assumption | ].
      apply fold_productions'_correct.
      assumption. }
  Qed.*)
End fold_correctness.
