Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.AsciiOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.Formats.WithTerm.String
        Fiat.Narcissus.Formats.Lexeme
        Fiat.Narcissus.Formats.XML.

Require Import
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.Decision
        Fiat.Narcissus.Automation.NormalizeFormats
        Fiat.Narcissus.Automation.ExtractData
        Fiat.Narcissus.Automation.AlignedAutomation.
Require Import Fiat.Narcissus.Examples.TutorialPrelude.

Require Import
  Fiat.Narcissus.BinLib.AlignedString
  Fiat.Narcissus.BinLib.AlignedLexeme
  Fiat.Narcissus.BinLib.AlignedDelimiter
  Fiat.Narcissus.BinLib.WithTerm.String.

Require Import
        Coq.Strings.String.

Open Scope string_scope.
Open Scope format_scope.

Ltac new_encoder_rules ::=
  match goal with
  | |- context [ format_element ] => unfold format_element
  | |- context [ format_start_tag ] => unfold format_start_tag
  | |- context [ format_end_tag ] => unfold format_end_tag
  end.

Ltac apply_new_combinator_rule ::=
  match goal with
  | |- context [ format_element ] => unfold format_element
  | |- context [ format_start_tag ] => unfold format_start_tag
  | |- context [ format_end_tag ] => unfold format_end_tag
  end; apply_rules.

Module test1.
  Record msg := { data : string }.
  Definition format :=
    format_element "data" format_string ◦ data.
  Definition invariant (m : msg) := True.

  Definition enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Definition encode := encoder_impl enc_dec.
  Definition decode := decoder_impl enc_dec.
End test1.

Module test2.
  Record msg := { data : word 8 }.
  Definition format :=
    format_element "data" format_word ◦ data.
  Definition invariant (m : msg) := True.

  Definition enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Definition encode := encoder_impl enc_dec.
  Definition decode := decoder_impl enc_dec.
End test2.

Module test3.
  Record msg := { data : string }.
  (* <msg><data>...</data></msg> *)
  Definition format :=
    format_element "msg"
      (format_element "data" format_string) ◦ data.
  Definition invariant (m : msg) := True.

  Definition enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Definition encode := encoder_impl enc_dec.
  Definition decode := decoder_impl enc_dec.
End test3.

Module test4.
  Record msg := { sdata : string; wdata : word 8 }.
  (* <msg><sdata>..</sdata><wdata>..</wdata></msg> *)
  (* You can't add [◦ id] at the end! *)
  Definition format :=
    format_element "msg"
      (format_element "sdata" format_string ◦ sdata ++
         format_element "wdata" format_word ◦ wdata).
  Definition invariant (m : msg) := True.

  Definition enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Definition encode := encoder_impl enc_dec.
  Definition decode := decoder_impl enc_dec.
End test4.
