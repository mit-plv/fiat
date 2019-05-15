Narcissus: Correct-By-Construction Derivation of Decoders and Encoders from Binary Formats
======================================================================

This archive holds the source code of Narcissus, a Coq library for
synthesizing binary encoders and decoders from specifications.

## Dependencies:
  * To build the library:          Coq 8.7.2

## Compiling and running the code
  * To build the core library: `make narcissus`

## Getting Started:
  * A tour of Narcissus can be found in src/Narcissus/Examples/README.v
  * The examples from our mirage case study can be found in src/Narcissus/Examples/NetworkStack
  
## Paper-to-artifact correspondence guide
  * All examples from Section 1.1 (A tour of Narcissus) can be found in src/Narcissus/Examples/README.v
    - We also generate a checking (`AlignedEncode_Nil`) at the end of an encoder
      to make sure the buffer size is big enough, which we omitted in the paper
      for brevity.
    - The `>>>` notation is unfolded and reduced in the generated encoder. We
      still keep `>>>` in the paper to make it more readable.

  * The definitions of format, encoder, and decoder, in Section 2 (Naricssus, Formally):

  | Definition | File                         | Name    |
  |------------|------------------------------|---------|
  | FormatM    | src/Narcissus/Common/Specs.v | FormatM |
  | EncodeM    | src/Narcissus/Common/Specs.v | EncodeM |
  | DecodeM    | src/Narcissus/Common/Specs.v | DecodeM |
  
  * The formats for base types, in Figure 1 (Formats for base types included in Narcissus):

  | Base Type              | File                                 | Name of format               |
  |------------------------|--------------------------------------|------------------------------|
  | Booleans               | src/Narcissus/Formats/Bool.v         | format_bool                  |
  | Peano Numbers          | src/Narcissus/Formats/NatOpt.v       | format_nat                   |
  | Variable-Length List   | src/Narcissus/Formats/FixListOpt.v   | format_list                  |
  | Variable-Length String | src/Narcissus/Formats/StringOpt.v    | format_string_with_term_char |
  | Option Type            | src/Narcissus/Formats/Option.v       | format_option                |
  | Enumerated Types       | src/Narcissus/Formats/EnumOpt.v      | format_enum                  |
  | Fixed-Length Words     | src/Narcissus/Formats/WordOpt.v      | format_word                  |
  | Unspecified BitString  | src/Narcissus/Formats/ByteBuffer.v   | format_bytebuffer            |
  | Fixed-Length List      | src/Narcissus/Formats/Vector.v       | format_Vector                |
  | Fixed-Length String    | src/Narcissus/Formats/FixStringOpt.v | format_string                |
  | Ascii Character        | src/Narcissus/Formats/AsciiOpt.v     | format_ascii                 |
  | Variant Types          | src/Narcissus/Formats/SumTypeOpt.v   | format_SumType               |

  * The format combinators, in Section 2 (Naricssus, Formally):

  | Format combinator | File                                        | Name of format    |
  |-------------------|---------------------------------------------|-------------------|
  | ++                | src/Narcissus/Formats/Base/SequenceFormat.v | sequence_Format   |
  | ⊚                 | src/Narcissus/Formats/Base/FMapFormat.v     | Compose_Format    |
  | ◦                 | src/Narcissus/Formats/Base/FMapFormat.v     | Restrict_Format   |
  | ∩                 | src/Narcissus/Formats/Base/FMapFormat.v     | Projection_Format |
  | ∪                 | src/Narcissus/Formats/Base/UnionFormat.v    | Union_Format      |
  | ε                 | src/Narcissus/Formats/Empty.v               | empty_Format      |

  * The monadic operators (return, bind and the set-comprehension operator), in
    Section 2 (Naricssus, Formally), can be found in src/Computation/Core.v

  * The bitstring abstract data type, in Figure 2 (The ByteString interface),
    can be found in src/Narcissus/Common/Monoid.v, named `QueueMonoidOpt`.

  * The definitions and theorems of encoder/decoder correctness:
    - Our actual definitions have additional minor side conditions that are
      omitted in the paper for presentation purposes, such as the invariant on
      the state. The rules below may also have minor side conditions. See the
      corresponding definitions/theorems in the artifact for the complete
      formalism.

  | Definition                           | File                         | Name                 |
  |--------------------------------------|------------------------------|----------------------|
  | Definition 2.1 (Encoder Correctness) | src/Narcissus/Common/Specs.v | CorrectEncoder       |
  | Definition 2.2 (Decoder Correctness) | src/Narcissus/Common/Specs.v | CorrectDecoder_id    |
  | Theorem 2.3 (Decode Inverts Encode)  | src/Narcissus/Common/Specs.v | CorrectDecodeEncode' |
  | Theorem 2.4 (Encode Inverts Decode)  | src/Narcissus/Common/Specs.v | CorrectEncodeDecode' |

  * The encoder rules, in Figure 3 (Correctness rules for encoder combinators):
  
  | Rule     | File                                        | Name                             |
  |----------|---------------------------------------------|----------------------------------|
  | EncSeq   | src/Narcissus/Formats/Base/SequenceFormat.v | CorrectEncoder_sequence          |
  | EncComp  | src/Narcissus/Formats/Base/FMapFormat.v     | CorrectEncoder_Projection_Format |
  | EncEmpty | src/Narcissus/Formats/Empty.v               | CorrectEncoderEmpty              |
  | EncRest  | src/Narcissus/Formats/Base/FMapFormat.v     | CorrectEncoder_Restrict_Format   |
  | EncUnion | src/Narcissus/Formats/Base/UnionFormat.v    | CorrectEncoder_Union             |

  * The definition of `DecodeCM`, in Section 3.1 (Decoders), is simply `DecodeM
    (V * T) T`. Definition 3.1 (Decoder Combinator Soundness) and definition 3.2
    (Decoder Combinator Consistency) are defined in
    src/Narcissus/Common/Specs.v, named `CorrectDecoder`, as conjunction of
    these two definitons.

  * The decoder rules, in Figure 5 (Selected correctness rules for decoder
    combinators):
    - We use `CorrectDecoder` (the dotted roundtrip relation) directly in the
      actual definition for `CorrectDecoder_id` (the solid roundtrip relation),
      by choosing the equality relation as the view and the original format as
      the conformance format. This is explained in Section 3.1 (Decoders). It is
      also justified by the lemma `CorrectDecoder_equiv_CorrectDecoder_id` in
      src/Narcissus/Common/Specs.v

  | Rule       | File                               | Name                    |
  |------------|------------------------------------|-------------------------|
  | DecList    | src/Narcissus/Formats/FixListOpt.v | FixList_decode_correct  |
  | DecDone    | src/Narcissus/Formats/Empty.v      | CorrectDecoderEmpty     |
  | DecSeqProj | src/Narcissus/Formats/Sequence.v   | format_sequence_correct |

  * The decoder rules, in Figure 7 (Additional decoder combinator correctness rules):

  | Rule        | File                                        | Name                      |
  |-------------|---------------------------------------------|---------------------------|
  | DecCompose  | src/Narcissus/Formats/Base/FMapFormat.v     | Compose_decode_correct    |
  | DecViewDone | src/Narcissus/Formats/Empty.v               | ExtractViewFrom           |
  | DecInject   | src/Narcissus/Formats/Base/FMapFormat.v     | injection_decode_correct  |
  | DecSeq      | src/Narcissus/Formats/Base/SequenceFormat.v | Sequence_decode_correct   |
  | DecUnion    | src/Narcissus/Common/ComposeIf.v            | composeIf_format_correct' |

  * The definitions of byte-aligned encoders/decoders and their correctness, in
    Section 3.2 (Improving Performance of Encoders and Decoders):

  | Definition                                            | File                                      | Name                       |
  |-------------------------------------------------------|-------------------------------------------|----------------------------|
  | AlignEncodeM                                          | src/Narcissus/BinLib/AlignedEncodeMonad.v | AlignedEncodeM             |
  | AlignDecodeM                                          | src/Narcissus/BinLib/AlignedDecodeMonad.v | AlignedDecodeM             |
  | Definition 3.3 (Correctness of Byte-Aligned Encoders) | src/Narcissus/BinLib/AlignedEncodeMonad.v | EncodeMEquivAlignedEncodeM |
  | Definition 3.4 (Correctness of Byte-Aligned Decoders) | src/Narcissus/BinLib/AlignedDecodeMonad.v | DecodeMEquivAlignedDecodeM |
  
  * The byte-aligned decoder rules, in Figure 8 (A Selection of byte-alignment
    rules for decoders):

  | Rule           | File                                      | Name                              |
  |----------------|-------------------------------------------|-----------------------------------|
  | AlignDecSeq    | src/Narcissus/BinLib/AlignedDecodeMonad.v | Bind_DecodeMEquivAlignedDecodeM   |
  | AlignDecThrow  | src/Narcissus/BinLib/AlignedDecodeMonad.v | AlignedDecode_Throw               |
  | AlignDecByte   | src/Narcissus/BinLib/AlignWord.v          | AlignedDecodeCharM                |
  | AlignDecReturn | src/Narcissus/BinLib/AlignedDecodeMonad.v | Return_DecodeMEquivAlignedDecodeM |
  
  * The implementation of the automation algorithm, in Section 4 (Automation
    Derivations), can be found in src/Narcissus/Automation. Specifically, the
    entry point of `DeriveDecoder`, shown in Algorithm 1, is
    `synthesize_aligned_decoder` in src/Narcissus/Automation/AlignedAutomation.v
  
  * The combinators for IP Checksums, in Figure 10 (Format, encoder, and decoder
    combinator for IP Checksums):

  | Definition         | File                               | Name                               |
  |--------------------|------------------------------------|------------------------------------|
  | IP_Checksum_format | src/Narcissus/Formats/IPChecksum.v | format_IP_Checksum                 |
  | IP_Checksum_decode | src/Narcissus/Formats/IPChecksum.v | format_IP_Checksum                 |
  | DecChkSum          | src/Narcissus/Formats/IPChecksum.v | compose_IPChecksum_format_correct' |

  * The example of IPv4 header format, in Figure 11 (Format for IP version 4
    headers, using the IP Checksum format), can be found in
    src/Narcissus/Examples/NetworkStack/IPv4Header.v
