Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretation.

Module DataflowInput.
  Section input_data.
    Context {Char : Type}.

    Record t :=
      { T : Type;
        fpdata : grammar_fixedpoint_lattice_data T;
        aidata : AbstractInterpretation (Char:=Char) }.
  End input_data.
  Global Arguments t : clear implicits.
End DataflowInput.

Module DataflowOutput.
  Definition t {Char} d G
    := @fold_grammar_data Char (DataflowInput.T d) (DataflowInput.fpdata d) (DataflowInput.aidata d) G.

  Section output_data.
    Context {Char : Type}
            {d : DataflowInput.t Char}
            {G : pregrammar' Char}
            (v : t d G).

    Definition t_data := Eval hnf in @fgd_fold_grammar _ _ _ _ _ v.
    Definition t_correct : Morphisms.pointwise_relation _ eq (lookup_state t_data) (lookup_state (fold_grammar G _))
      := fgd_fold_grammar_correct.
  End output_data.
  Coercion t_data : t >-> aggregate_state.
End DataflowOutput.
