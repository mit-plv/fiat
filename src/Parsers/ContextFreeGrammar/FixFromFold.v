Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fold.
Require Import Fiat.Parsers.ContextFreeGrammar.FixDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.FixFromFoldDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.FixCorrect.

Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section fold_correctness.
  Context {Char : Type} {T : Type}.
  Context {FGD : fold_grammar_data Char T}
          {fpdata : @grammar_fixedpoint_lattice_data T}
          (G : pregrammar' Char).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition fold_grammar : aggregate_state (fixedpoint_from_fold G)
    := pre_Fix_grammar _ G.

  Context {FGCD : fold_fix_grammar_correctness_data G}.

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
  Qed.
End fold_correctness.
