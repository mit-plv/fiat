(** * Definition of ε, the CFG accepting only "" *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.

Set Implicit Arguments.

Section generic.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.

  Definition trivial_pregrammar : pregrammar' Char :=
    {| pregrammar_productions := (""%string, nil::nil)::nil |}.

  Definition trivial_grammar : grammar Char := trivial_pregrammar.

  Definition trivial_grammar_parses_empty_string {s} (H : length s = 0)
  : parse_of_grammar s trivial_grammar.
  Proof.
    hnf; simpl.
    apply ParseHead.
    constructor; assumption.
  Defined.

  Lemma trivial_grammar_parses_only_empty_string s : parse_of_grammar s trivial_grammar -> length s = 0.
  Proof.
    intro H; hnf in H; simpl in H.
    repeat match goal with
             | _ => reflexivity
             | _ => assumption
             | [ H : parse_of _ _ _ |- _ ] => inversion_clear H
             | [ H : parse_of_production _ _ _ |- _ ] => inversion_clear H
           end.
  Qed.
End generic.
