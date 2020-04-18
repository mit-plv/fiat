Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Bedrock.Platform.Cito.SemanticsUtil.
  Require Import Coq.Lists.List.

  Notation make_triples := (@make_triples ADTValue).

  Lemma make_triples_Word : forall pairs outs, length outs = length pairs -> map (@Word _) (make_triples pairs outs) = map fst pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_Word_ADTIn : forall pairs outs, length outs = length pairs -> map (fun x => (Word x, ADTIn x)) (make_triples pairs outs) = pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_ADTIn : forall pairs outs, length outs = length pairs -> map (@ADTIn _) (make_triples pairs outs) = map snd pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_length : forall pairs outs, length outs = length pairs -> length (make_triples pairs outs) = length pairs.
    induction pairs; destruct outs; simpl; intuition.
  Qed.

End ADTValue.
