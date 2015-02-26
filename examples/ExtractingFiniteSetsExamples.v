Require Import ADTSynthesis.FiniteSetADTs.FiniteSetADTImplementation.
Require Import ADTExamples.FiniteSetsExamples.

Require Import DFacadeToBedrock.
Require Import FiatADTs.
Require Import FiatRepInv.

Module Import FA := DFacadeToBedrock.Make FiatADTs.Adt FiatRepInv.Ri.

Require Import CompileUnit FiatImpl.

Module sumUnique.
  Definition input := sumUniqueImpl FiniteSetImpl.
  Definition output := compile input.
  Definition m1 := bedrock_module output.
  Definition m1_ok := bedrock_module_ok output.
  Definition m2 := bedrock_module_impl output.
  Definition m2_ok := bedrock_module_impl_ok output.

  Definition all1 := link m1 m2.

  Lemma all1_ok : moduleOk all1.
    link m1_ok m2_ok.
  Qed.

  Definition all := link all1 FiatImpl.m.

  Theorem all_ok : moduleOk all.
    link all1_ok FiatImpl.ok.
  Qed.
End sumUnique.
