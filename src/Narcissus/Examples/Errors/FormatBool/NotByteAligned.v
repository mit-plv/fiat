Require Import
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.Automation.Error
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.

Record msg := { data : bool }.
Definition format := format_bool ◦ data.
Definition invariant (_ : msg) := True.
Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
Defined.

Let dec' := Eval simpl in extractDecoder dec.
Print dec'.
Print Assumptions dec'.
