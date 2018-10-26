Require Import TutorialPrelude.
(******************************************************************************)
(*** A brief Narcissus tutorial ***)

(*+ Part I: the usual combinators +*)

(** ** Intuitive approach:

    - [type δ encoder = δ -> bytes]
    - [type δ decoder = bytes -> option δ] **)

(** ** Correctness:

    - [forall x, decode__δ (encode__δ x) = Some x]
    - [forall bits, decode__δ bits = None -> forall x, encode__δ bits = None]
    - [forall bits, decode__δ bits = Some x -> encode__δ x = bits] **)

(** ** Building blocks:

    - Primitives:
      [encode__word, decode__word]

    - Combinators:
      [encode__product: α encoder -> β encoder -> α×β encoder]
      [encode__sum: α encoder -> β encoder -> α+β encoder] **)

(******************************************************************************)
(*** Synthesizing decoders ***)

(** Start with a record definition: **)
Record weather_packet :=
  { stationID: word 16;
    reading: list (word 8) }.

(** Describe how to write the values out: **)
Definition format : FormatM weather_packet ByteString :=
     format_word ◦ stationID
  ++ format_const WO~1~0~1~0~1~0~1~1
  ++ format_unused_word 8
  ++ format_nat 8 ◦ length ◦ reading
  ++ format_list format_word ◦ reading.

(** Generate the encoder… **)
Definition encoder_with_proofs :
  CorrectAlignedEncoderFor format.
Proof. synthesize_aligned_encoder. Defined.

Definition encode {sz} pkt buf := (encoder_impl encoder_with_proofs) sz pkt buf.

(** …and the decoder **)
Definition decoder_with_proofs :
  CorrectAlignedDecoderFor (fun pkt => (| pkt.(reading) |) < pow2 8) format.
Proof. synthesize_aligned_decoder. Defined.

Definition decode {sz} v := (decoder_impl decoder_with_proofs) sz v.

(** All done! **)
Example packet :=
  {| stationID := WO~1~1~1~1~1~0~1~0~1~1~0~0~1~1~1~0;
     reading := [WO~0~1~0~0~0~1~1~0; WO~0~1~0~0~0~1~1~0]%list |}.

Definition buffer := initialize_Aligned_ByteString 8.

Compute (encode packet buffer).
Compute (decode (fst (fst (must (encode packet buffer))))).

(** The generated functions live in a state monad;
    here's what they look like: **)
Print encode.
Print decode.

(******************************************************************************)
(*+ Part II: Adding dependencies +*)

(** Most network formats are not context-free:

    +---------------+
    |       n       |
    +---------------+
    |  …𝘯 Records…  |
    |               | **)

(** To support these, we carry information about previous
    fields throughout the decoder derivation **)

(******************************************************************************)
(*+ Part III: Options & Variants +*)

(** Most network encodings are non-unique:

    - IPv4 headers have bits reserved for future use
    - Strings in DNS packets can be optionally compressed
    - The EtherType field in ethernet is either a magic
      constant or dataframe length **)

(** We use a relation instead of a function to specify the
    format, and we generate the encoder and the decoder.

    - Correctness:
      [forall pkt, encode pkt ∈ format pkt]
      [forall bits, decode bits = None -> forall pkt, bits ∉ format pkt]
      [forall pkt bits, bits ∈ format pkt -> decode bits = Some pkt] **)

