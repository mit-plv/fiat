Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import CertifiedExtraction.Core.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.TuplesF.

Require Import CertifiedExtraction.Utils.

Require Import Bedrock.Memory.

Require Import Refactor.Basics.
Require Import Refactor.TupleToListW.
Require Import Refactor.EnsemblesOfTuplesAndListW.

Ltac Wrapper_t :=
  abstract (intros * H; inversion H; subst; clear H; f_equal;
            eauto with inj_db).

Instance QS_WrapTuple {N} : FacadeWrapper ADTValue (@RawTuple (MakeWordHeading N)).
Proof.
  refine {| wrap tp := Tuple (TupleToListW tp);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapTupleList {N} : FacadeWrapper ADTValue (list (@RawTuple (MakeWordHeading N))).
Proof.
  refine {| wrap tl := TupleList (List.map TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapWordList : FacadeWrapper ADTValue (list W).
Proof.
  refine {| wrap tl := WordList tl;
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBedrockTuple : FacadeWrapper QsADTs.ADTValue (TuplesF.tupl).
Proof.
  refine {| wrap tp := QsADTs.Tuple tp;
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBag0 {N} : FacadeWrapper ADTValue (FiatBag N).
Proof.
  refine {| wrap tl := Tuples0 (Word.natToWord 32 N) (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBag1 {N} (M: Word.word 32) : FacadeWrapper ADTValue (FiatBag N).
Proof.
  refine {| wrap tl := Tuples1 (Word.natToWord 32 N) M (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBag2 {N} (M: Word.word 32) (M': Word.word 32) : FacadeWrapper ADTValue (FiatBag N).
Proof.
  refine {| wrap tl := Tuples2 (Word.natToWord 32 N) M M' (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.
