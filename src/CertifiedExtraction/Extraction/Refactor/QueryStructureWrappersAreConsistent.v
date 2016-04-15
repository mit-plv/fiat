Require Import Fiat.CertifiedExtraction.Benchmarks.QueryStructureWrappers.
Require Import Fiat.CertifiedExtraction.ADT2CompileUnit.
Require Import CertifiedExtraction.Core.
Require Import Bedrock.Memory.
Require Import FacadeUtils.


(* FIXME: Just embed the definition of ‘Good’ into the ‘Wrapper’ typeclass *)

Definition Good_bool {av}
  : GoodWrapper av bool.
Proof.
  refine {| gWrap := _;
            gWrapTag := false |}; simpl; eauto.
Defined.

Definition Good_listW
  : GoodWrapper QsADTs.ADTValue (list W).
Proof.
  refine {| gWrap := WrapInstance (H := QS_WrapWordList);
            gWrapTag := true |};
    simpl; eauto.
Defined.

Definition Good_BedrockTuple
  : GoodWrapper QsADTs.ADTValue (list W).
Proof.
  refine {| gWrap := WrapInstance (H := QS_WrapBedrockTuple);
            gWrapTag := true
         |}; intros; unfold wrap; simpl; eauto.
Defined.

Definition Good_W {av}
  : GoodWrapper av W.
Proof.
  refine {| gWrap := _;
            gWrapTag := false
         |}; intros; unfold wrap; simpl; eauto.
Defined.

