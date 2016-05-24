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
          {aidata : @AbstractInterpretation Char T}
          (related : Ensemble String -> T -> Prop)
          {aicdata : AbstractInterpretationCorrectness related}.
  Context (G : pregrammar Char).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition fold_grammar : aggregate_state (fixedpoint_by_abstract_interpretation G)
    := pre_Fix_grammar _ G.

  Section step.
    Context (state_of_parse : forall str pats, parse_of G str pats -> T)
            (state_of_parse_production : forall str pat, parse_of_production G str pat -> T)
            (state_of_parse_item : forall str it, parse_of_item G str it -> T).

    Definition state_of_parse_item'
               str it (p : parse_of_item G str it)
      : T
      := match p with
         | ParseTerminal ch P Hch Hstr => on_terminal P
         | ParseNonTerminal nt Hvalid p' => state_of_parse p'
         end.

    Definition state_of_parse_production'
               str pat (p : parse_of_production G str pat)
      : T
      := match p with
         | ParseProductionNil Hlen => on_nil_production
         | ParseProductionCons n pat pats p' p's
           => combine_production
                (state_of_parse_item p')
                (state_of_parse_production p's)
         end.

    Definition state_of_parse'
               str pats (p : parse_of G str pats)
      : T
      := match p with
         | ParseHead pat pats p' => state_of_parse_production p'
         | ParseTail pat pats p' => state_of_parse p'
         end.
  End step.

  Fixpoint state_of_parse str pats (p : parse_of G str pats) : T
    := @state_of_parse' (@state_of_parse) (@state_of_parse_production) str pats p
  with state_of_parse_production str pat (p : parse_of_production G str pat) : T
    := @state_of_parse_production' (@state_of_parse_production) (@state_of_parse_item) str pat p
  with state_of_parse_item str it (p : parse_of_item G str it) : T
    := @state_of_parse_item' (@state_of_parse) str it p.

  (*Lemma fold_nt_correct nt
    : related (fun str => inhabited (parse_of_item G str (NonTerminal (to_nonterminal nt))))
              (lookup_state fold_grammar nt).
  Proof.
    unfold fold_grammar.
    SearchAbout lookup_state

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
