Require Import Fiat.Narcissus.Examples.TutorialPrelude.

(**
The following section presents the Narcissus framework through a series of increasingly complex examples showcasing its main features.  Details are purposefuly omitted; they will be revealed in section N.  The end result is a moderately complex description for the packet format used by an indoor temperature sensor to report measurements to a smart home controller.
**)

(**
We start with an extremely simple record, and a correspondingly simple format:
**)

Module Sensor0.
  Record sensor_msg :=
    { stationID: word 8; measurement: word 16 }.

  Let format :=
       format_word ◦ stationID
    ++ format_word ◦ measurement.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
     (stationID ▹ SetCurrentByte ≫
      measurement ▹ (low_bits 8 ▹ SetCurrentByte ≫
                     shift_right 8 ▹ SetCurrentByte)) v 0 r tt *)
  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      b0 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b0⋅b';
      return {| stationID := b; measurement := w |}) v 0 tt *)
End Sensor0.

(** All user input is contained in box 1. `sensor_msg` is a record type with two fields; the Coq `Record` command additionally defines two functions `stationID` and `measurement` (of type `sensor_msg → …`) to access these fields. `format` specifies how to encode instances of this record: `format_word` is a Narcissus primitive that writes out its input bit by bit, and `++` is a sequencing operator (write this, then that).  `invariant` specifies additional constraints on well-formed packets, but there are none here.  Box 2 calls the `derive_encoder_decoder_pair` tactic provided by Narcissus, which generates an encoder and a decoder along with proofs of correctness (it takes about two to five seconds to return); the rest is routine boilerplate.  Boxes 2 and 3 show generated code. In box 2, the generated encoder takes a packet and a byte buffer and returns the encoded packet or `None` if it did not fit in the supplied buffer. In box 3, the decoder takes a buffer, and returns a packet or None if the buffer did not contain a valid encoding. Both generated programs live in stateful error monads, offering primitives to read (GetCurrentByte), skip (SkipCurrentByte), and write (SetCurrentByte) a single byte.  The encoder uses `low_bits` and `shift_right` to extract the low and high bits of the `measurement` field, and the decoder reassembles these two bytes using a shift and an addition, using the `⋅` operator: this byte-alignment transformation is part of the `derive_encoder_decoder_pair` logic. **)

(** We now introduce a twist: to preserve 16-bit alignment, we introduce 8 bits of padding after encoding `stationID`; these bits will be reserved for future use. **)

Module Sensor1.
  Record sensor_msg :=
    { stationID: word 8; measurement: word 16 }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_word ◦ measurement.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
    (stationID ▹ SetCurrentByte ≫
     const WO~0~0~0~0~0~0~0~0 ▹ SetCurrentByte ≫
     measurement ▹ (low_bits 8 ▹ SetCurrentByte ≫
                    shift_right 8 ▹ SetCurrentByte)) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      _ <- SkipCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      return {| stationID := b; measurement := w |}) v 0 tt *)
End Sensor1.

(** Notice the asymmetry that these 8 under-specified bits introduce: although the encoder always writes `0x00`, the decoder accepts any value.  This is crucial because the `format_unused_word` specification allows conforming encoders to output any 8-bits value; as a result, the decoder must accept all 8-bit values.  In that sense, the encoder and decoder that Narcissus generates are not inverse of each other: the encoder is one among a family of functions permitted by the formatting specification, and the decoder is the inverse of the *entire family*, accepting any output produced by a conforming encoder. **)

(** Our next enhancement is to introduce a version number field in our packet, and to tag each measurement with a `kind`, `"TEMPERATURE"` or `"HUMIDITY"`.  To save space, we allocate 2 bits for the `kind` tag, and 14 bits to the actual measurement. **)

Module Sensor2.

  Let kind :=
      EnumType ["TEMPERATURE"; "HUMIDITY"].

  Record sensor_msg :=
    { stationID: word 8; measurement: (kind * word 14) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_enum [WO~0~0; WO~0~1] ◦ (Basics.compose fst measurement)
    ++ format_word ◦ (Basics.compose snd measurement).

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  Let decode := decoder_impl enc_dec.
End Sensor2.

(** The use of `format_const` in the specification forces conforming encoders must write out the value 0x7e2, encoded over 16 bits.  Accordingly, the generated decoder throws an exception if its input does not contain that exact sequence.  The argument passed to `format_enum` specifies which bit patterns to use to represent each tag (`0b00` for `"TEMPERATURE"`, `0b01` for `"HUMIDITY"`), and the decoder uses this mapping to reconstruct the appropriate enum member. **)

(** We use the next iteration to illustrate data dependencies and input restrictions.  To do so, we replace our single data point with a list of measurements (for conciseness, we remove tags and use 16-bit words).  We start as before, but we quickly run into an issue : **)

Module Sensor3.
  Record sensor_msg :=
    { stationID: word 8; measurements: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ measurements.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. all:simpl. Abort.
End Sensor3.

(** The derivation fails, leaving multiple Coq goals unsolved.  The most relevant is equivalent to the following:

<<
forall msg : sensor_msg,
  stationID msg = sid ->
  length msg.(measurements) = ?Goal
>>

It shows one of the side-conditions build by Narcissus as it generates the decoder.  On the left of the arrow is all that is known about an abstract incoming packet after decoding its stationID to the abstract value `sID`; on the right what needs to be known about the packet to be able to decode the list of measurements; namely, that this list has a known length, equal to some undetermined value `?Goal` (an “evar” in Coq parlance). In brief: we forgot to encode the length of the `measurements` list, and this prevents Narcissus from generating a decoder.

Our attempted fix, unfortunately, only gets us half of the way there (`format_nat 16 ◦ length` specifies that the length of the list should be truncated to 16 bits and written out):
**)

Module Sensor4.
  Record sensor_msg :=
    { stationID: word 8; measurements: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 16 ◦ length ◦ measurements
    ++ format_list format_word ◦ measurements.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. all:simpl. Abort.
End Sensor4.

(** Again, decoder generation fails and spills out an unsolvable goal:

<<
forall data : sensor_msg,
  invariant data /\ stationID data = proj ->
  length data.(measurements) < pow2 16
>>

The problem is that, since we encode the list's length on 16 bits, the round-trip property that Narcissus attempts to prove only holds if the list has less than \(2^{16}\) elements: larger lists have their length truncated, and it becomes impossible for the decoder to know for cetain how many elements it should decode.  What we need is an input restriction: a predicate defining which messages we may encode; to this end, we update our example as follows:
**)

Module Sensor5.
  Record sensor_msg :=
    { stationID: word 8; measurements: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 8 ◦ (Basics.compose length measurements)
    ++ format_list format_word ◦ measurements.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(measurements)) < pow2 8.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
     (stationID ▹ SetCurrentByte ≫
      const WO~0~0~0~0~0~0~0~0 ▹ SetCurrentByte ≫
      const WO~0~0~0~0~0~1~1~1 ▹ SetCurrentByte ≫
      const WO~1~1~1~0~0~0~1~0 ▹ SetCurrentByte ≫
      measurements ▹ Datatypes.length ▹ natToWord 8 ▹ SetCurrentByte ≫
      measurements ▹ AlignedEncodeList (fun n => low_bits 8 ▹ SetCurrentByte ≫
                                                 shift_right 8 ▹ SetCurrentByte) sz) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      _ <- SkipCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
       then
        b2 <- GetCurrentByte;
        l <- ListAlignedDecodeM
               (fun numBytes : nat =>
                w0 <- GetCurrentByte;
                w' <- w1 <- GetCurrentByte;
                      w' <- return WO;
                      return w1⋅w';
                return w0⋅w') (wordToNat b2);
        return {| stationID := b; measurements := l |}
       else fail)) v 0 tt *)
End Sensor5.

Module Sensor6.

  Inductive reading :=
  | Temperature (_ : word 14)
  | Humidity (_ : word 14).

  Let format_reading m s :=
    match m with
    | Temperature t => ret (serialize (Word.combine WO~0~0 t) s)
    | Humidity h => ret (serialize (Word.combine WO~0~1 h) s)
    end.

  Let enc_reading sz :=
    (fun buf idx m => @SetCurrentBytes _ _ sz 2 buf idx match m with
         | Temperature t => Word.combine WO~0~0 t
         | Humidity h => Word.combine WO~0~1 h
         end).

  Lemma enc_readingCorrect
    : CorrectAlignedEncoder format_reading enc_reading.
  Proof.
    unfold enc_reading, format_reading.
    eapply refine_CorrectAlignedEncoder.
    2: eapply CorrectAlignedEncoderForFormatMChar_f; eauto.
    intros; destruct s; simpl;
      rewrite refine_Projection_Format;
      reflexivity.
  Qed.

  Let dec_reading :=
    fun t ctx =>
    `(w, rest, ctx') <- decode_word t ctx;
      if weqb (split1 2 14 w) WO~0~0
      then Some (Temperature (split2 2 14 w), rest, ctx')
      else (if weqb (split1 2 14 w) WO~0~1 then
              Some (Humidity (split2 2 14 w), rest, ctx')
            else None).

  Lemma dec_readingCorrect
    : CorrectDecoder _ (fun _ => True) (fun _ _ => True) format_reading dec_reading (fun _ => True).
  Proof.
    unfold format_reading, dec_reading; split; intros.
    - destruct data; eapply encode_Word_decode_correct in H2; eauto;
        destruct_ex; intuition; try rewrite H3; simpl;
          eexists; rewrite split2_combine; eauto.
    - eapply DecodeBindOpt2_inv in H1; destruct_ex; intuition.
      destruct (weqb (split1 2 14 x) WO~0~0) eqn:? .
      + destruct (shatter_word_S x) as [? [x' ?] ];
          destruct (shatter_word_S x') as [? [x'' ?] ];
          subst; apply weqb_true_iff in Heqb; injections;
            unfold split2; simpl.
        eapply (@encode_Word_decode_correct _ _ _ _ _ _ (fun _ => True)) in H2;
          unfold cache_inv_Property; intuition eauto.
      + destruct (weqb (split1 2 14 x) WO~0~1) eqn:? ; try discriminate;
          destruct (shatter_word_S x) as [? [x' ?] ];
          destruct (shatter_word_S x') as [? [x'' ?] ];
          subst.
        apply weqb_true_iff in Heqb0; injections;
          unfold split2; simpl;
            eapply (@encode_Word_decode_correct _ _ _ _ _ _ (fun _ => True)) in H2;
          unfold cache_inv_Property; intuition eauto.
  Qed.

  Record sensor_msg :=
    { stationID: word 8; measurements: list reading }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 8 ◦ (Basics.compose length measurements)
    ++ format_list format_reading ◦ measurements.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(measurements)) < pow2 8.

  Ltac new_encoder_rules ::= apply enc_readingCorrect.
  Ltac new_decoder_rules ::= apply dec_readingCorrect.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  Let decode := decoder_impl enc_dec.
End Sensor6.
