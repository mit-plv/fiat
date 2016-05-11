Require Import Fiat.CertifiedExtraction.Extraction.QueryStructures.Wrappers.
Require Import Fiat.CertifiedExtraction.ADT2CompileUnit.
Require Import CertifiedExtraction.FacadeWrappers.
Require Import CertifiedExtraction.Core.
Require Import Bedrock.Memory.

(* FIXME: Just embed the definition of ‘Good’ into the ‘FacadeWrapper’ typeclass *)

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

Definition Good_BedrockWTuple
  : GoodWrapper QsADTs.ADTValue (TuplesF.GenericTuple W).
Proof.
  refine {| gWrap := WrapInstance (H := QS_WrapBedrockWTuple);
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
