Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import CertifiedExtraction.Core.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.TuplesF.

Require Import CertifiedExtraction.Utils.

Require Import Bedrock.Memory.

Require Import CertifiedExtraction.Extraction.QueryStructures.Basics.
Require Import CertifiedExtraction.Extraction.QueryStructures.TupleToListW.
Require Import CertifiedExtraction.Extraction.QueryStructures.EnsemblesOfTuplesAndListW.

Ltac Wrapper_t :=
  abstract (intros * H; inversion H; subst; clear H; f_equal;
            eauto with inj_db).

(* Disabled, since we now export it in Tuple.v *)
(* Instance QS_WrapFiatWTuple {N} : FacadeWrapper ADTValue (FiatWTuple N). *)
(* Proof. *)
(*   refine {| wrap tp := WTuple (TupleToListW tp); *)
(*             wrap_inj := _ |}; Wrapper_t. *)
(* Defined. *)

Instance QS_WrapWordList : FacadeWrapper ADTValue (list W).
Proof.
  refine {| wrap tl := WordList tl;
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapFiatWTupleList {N} : FacadeWrapper ADTValue (list (FiatWTuple N)).
Proof.
  refine {| wrap tl := WTupleList (List.map TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBedrockWTuple : FacadeWrapper QsADTs.ADTValue (TuplesF.tupl).
Proof.
  refine {| wrap tp := WTuple tp;
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapWBagOfTuples0 {N} : FacadeWrapper ADTValue (FiatWBag N).
Proof.
  refine {| wrap tl := WBagOfTuples0 (Word.natToWord 32 N) (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapWBagOfTuples1 {N} (M: Word.word 32) : FacadeWrapper ADTValue (FiatWBag N).
Proof.
  refine {| wrap tl := WBagOfTuples1 (Word.natToWord 32 N) M (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapWBagOfTuples2 {N} (M: Word.word 32) (M': Word.word 32) : FacadeWrapper ADTValue (FiatWBag N).
Proof.
  refine {| wrap tl := WBagOfTuples2 (Word.natToWord 32 N) M M' (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.
