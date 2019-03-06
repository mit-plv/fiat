Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Common.List.ListMorphisms.

Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section general_fold.
  Context {Char : Type}
          {T0 T1 : Type}.
  Context {fpdata0 : @grammar_fixedpoint_lattice_data T0}
          {fpdata1 : @grammar_fixedpoint_lattice_data T1}.
  Context {aidata0 : AbstractInterpretation (Char:=Char) (fpdata:=fpdata0)}
          {aidata1 : AbstractInterpretation (Char:=Char) (fpdata:=fpdata1)}.

  Local Notation "R ==> S" := (respectful_hetero _ _ _ _ R (fun _ _ => S)) : signature_scope.
  Local Notation pointwise_relation T R := (fun f g => forall x : T, R (f x) (g x)).
  Local Notation Proper sig R := (sig%signature R R) (only parsing).

  Context (G : pregrammar' Char)
          (R : @state _ fpdata0 -> @state _ fpdata1 -> Prop)
          (R_bot : R ⊥ ⊥)
          (R_on_terminal : forall v, R (on_terminal v) (on_terminal v))
          (R_on_nil_production : R on_nil_production on_nil_production)
          (R_combine_production : Proper (R ==> R ==> R) combine_production)
          (R_lub : Proper (R ==> R ==> R) least_upper_bound).

  (*Lemma fold_item'_Proper_hetero
    : Proper (pointwise_relation _ R ==>  ==> R) (@fold_item').
  Proof.
    intros ?? H [?|?] ??; subst; simpl; trivial.
  Qed.

  Lemma fold_production'_Proper_hetero
    : Proper (pointwise_relation _ R ==> eq ==> R) (fold_production' G).
  Proof.
    clear -R_on_terminal R_on_nil_production R_combine_production.
    unfold fold_production'.
    intros ?? H ls x ?; subst x; simpl; trivial; [].
    induction ls as [|x xs IHxs]; trivial; [].
    simpl.
    apply R_combine_production; trivial; apply fold_item'_Proper_hetero; trivial.
  Qed.

  Lemma fold_productions'_Proper_hetero
    : Proper (pointwise_relation _ R ==> eq ==> R) (fold_productions' G).
  Proof.
    clear -R_on_terminal R_on_nil_production R_combine_production R_bot R_lub.
    unfold fold_productions'.
    intros ?? H ls x ?; subst x; simpl; trivial; [].
    induction ls as [|x xs IHxs]; trivial; [].
    simpl.
    apply R_lub; trivial; apply fold_production'_Proper_hetero; trivial.
  Qed.

  Lemma fold_constraints_Proper_hetero
    : Proper (pointwise_relation _ R ==> eq ==> R) (fold_constraints G).
  Proof.
    repeat intro; apply fold_productions'_Proper_hetero; repeat (trivial || subst).
  Qed.*)
End general_fold.
