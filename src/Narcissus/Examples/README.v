Require Import Fiat.Narcissus.Examples.TutorialPrelude.

Set Warnings "-local-declaration".

(**
The following section presents the Narcissus framework through a series of increasingly complex examples showcasing its main features.  Details are purposefuly omitted; they will be revealed in section N.  The end result is a moderately complex description for the packet format used by an indoor temperature sensor to report measurements to a smart home controller.
**)

(**
We start with an extremely simple record, and a correspondingly simple format:
**)

(*Module Example.

Require Import ilist
        SumType.

Definition instr : Type := SumType [word 8 : Type; word 8 : Type].

Definition instr_codes : t (word 8) 2 :=
  [ natToWord 8 5; natToWord 8 43].

Let invariant (i : instr) := True.

Definition format_instr : FormatM instr ByteString :=
  format_enum instr_codes ◦ (SumType_index _) ++ (* Format the tag for the instructions *)
  format_SumType _ (icons format_word (icons format_word inil)) ◦ (@id _) (* Format the argment for the instructions *)
.

Let no_align_decode : CorrectDecoderFor invariant format_instr.
 Proof.
   Solver.start_synthesizing_decoder.
   NormalizeFormats.normalize_format; apply_rules.
   last_failing_goal.
   revert H.
   match goal with
     | |- context [ CorrectDecoder (T := ?B) _ _ _ _ (format_SumType (m := ?n)  ?types _) _ _ _ ] =>
          let cache_inv_H := fresh in
          intros cache_inv_H; (first
           [ let types' := eval unfold types in types in
             ilist_of_evar (fun T : Type => T -> CacheFormat -> Comp (B * CacheFormat)) types'
              ltac:(fun formatrs' =>
                      ilist_of_evar (fun T : Type => B -> CacheDecode -> option (T * B * CacheDecode)) types'
                       ltac:(fun decoders' =>
                               ilist_of_evar (fun T : Type => Ensembles.Ensemble T) types'
                                ltac:(fun invariants' =>
                                        ilist_of_evar (fun T : Type => T -> B -> Prop) types'
                                                  ltac:(fun cache_invariants' =>
                                                          eapply (SumType_decode_correct types) with
                                                            (formatrs := formatrs') (
                                                           decoders := decoders') (invariants := invariants')
                                                           (cache_invariants := cache_invariants')))));
              apply_rules
           | ilist_of_evar (fun T : Type => T -> CacheFormat -> Comp (B * CacheFormat)) types
              ltac:(fun formatrs' =>
                      ilist_of_evar (fun T : Type => B -> CacheDecode -> option (T * B * CacheDecode)) types
                       ltac:(fun decoders' =>
                               ilist_of_evar (fun T : Type => Ensembles.Ensemble T) types
                                ltac:(fun invariants' =>
                                                 Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
                                                  ltac:(fun cache_invariants' =>
                                                          eapply (SumType_decode_correct types) with
                                                            (formatrs := formatrs') (
                                                              decoders := decoders') (invariants := invariants')
                                                            (cache_invariants := cache_invariants'))))) ]);
          [ simpl; repeat (apply IterateBoundedIndex.Build_prim_and; intros ** ); try exact I; apply_rules
                          | apply cache_inv_H ]; intros
             end.
            intros; simpl.
            unfold IsProj in H1.
            intuition eauto.
            destruct s; simpl; eauto.
            intros; apply_rules.
            simpl; intros;
              eapply CorrectDecoderEmpty.
            unfold Basics.compose in *;
              simpl in *;
              let a' := fresh in
              intros a'; repeat destruct a' as [? a'];
                (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
                simpl in *; intros;
                  (* Decompose data predicate *)
                  decompose_source_predicate;
                  (* Substitute any inferred equalities; decomposing *)
                  (* any product types that might have been built up *)
                  (* along the way *)
                  subst_projections.
            eapply H1.
            decide_data_invariant.
            simpl.
            instantiate (1 := fun _ => True).
            instantiate (1 := fun _ => True).
            apply unfold_cache_inv_Property; compute; intuition.
            cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
            Defined.


Inductive instr : Type :=
  | ADDI: word 8 -> instr    (* 05 iw *)
  | SUBI: word 8 -> instr.   (* 2D iw *)


Definition *)

Module Sensor0.
  Record sensor_msg :=
    { stationID: word 8; data: word 16 }.

  Let format :=
       format_word ◦ stationID
    ++ format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.  Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
     (stationID ⋙ SetCurrentByte ≫
      data ⋙ (low_bits 8 ⋙ SetCurrentByte ≫
      shift_right 8 ⋙ SetCurrentByte)) v 0 r tt *)
  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      b0 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b0⋅b';
      return {| stationID := b; data := w |}) v 0 tt *)
End Sensor0.

(** All user input is contained in box 1. `sensor_msg` is a record type with two fields; the Coq `Record` command additionally defines two functions `stationID` and `data` (of type `sensor_msg → …`) to access these fields. `format` specifies how to encode instances of this record: `format_word` is a Narcissus primitive that writes out its input bit by bit, and `++` is a sequencing operator (write this, then that).  `invariant` specifies additional constraints on well-formed packets, but there are none here.  Box 2 calls the `derive_encoder_decoder_pair` tactic provided by Narcissus, which generates an encoder and a decoder along with proofs of correctness (it takes about two to five seconds to return); the rest is routine boilerplate.  Boxes 2 and 3 show generated code. In box 2, the generated encoder takes a packet and a byte buffer and returns the encoded packet or `None` if it did not fit in the supplied buffer. In box 3, the decoder takes a buffer, and returns a packet or None if the buffer did not contain a valid encoding. Both generated programs live in stateful error monads, offering primitives to read (GetCurrentByte), skip (SkipCurrentByte), and write (SetCurrentByte) a single byte.  The encoder uses `low_bits` and `shift_right` to extract the low and high bits of the `data` field, and the decoder reassembles these two bytes using a shift and an addition, using the `⋅` operator: this byte-alignment transformation is part of the `derive_encoder_decoder_pair` logic. **)

(** We now introduce a twist: to preserve 16-bit alignment, we introduce 8 bits of padding after encoding `stationID`; these bits will be reserved for future use. **)

Module Sensor1.
  Record sensor_msg :=
    { stationID: word 8; data: word 16 }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
    (stationID ⋙ SetCurrentByte ≫
     const WO~0~0~0~0~0~0~0~0 ⋙ SetCurrentByte ≫
     data ⋙ (low_bits 8 ⋙ SetCurrentByte ≫
             shift_right 8 ⋙ SetCurrentByte)) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      _ <- SkipCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      return {| stationID := b; data := w |}) v 0 tt *)
End Sensor1.

(** Notice the asymmetry that these 8 under-specified bits introduce: although the encoder always writes `0x00`, the decoder accepts any value.  This is crucial because the `format_unused_word` specification allows conforming encoders to output any 8-bits value; as a result, the decoder must accept all 8-bit values.  In that sense, the encoder and decoder that Narcissus generates are not inverse of each other: the encoder is one among a family of functions permitted by the formatting specification, and the decoder is the inverse of the *entire family*, accepting any output produced by a conforming encoder. **)

(** Our next enhancement is to introduce a version number field in our packet, and to tag each measurement with a `kind`, `"TEMPERATURE"` or `"HUMIDITY"`.  To save space, we allocate 2 bits for the `kind` tag, and 14 bits to the actual measurement. **)

(* The rules for higher-order types (lists, sums, sequences. *)
Module Sensor2.

  Let kind :=
      EnumType ["TEMPERATURE"; "HUMIDITY"].

  Record sensor_msg :=
    { stationID: word 8; data: (kind * word 14) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_enum [WO~0~0; WO~0~1] ◦ fst ◦ data
    ++ format_word ◦ snd ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.  Defined.

  Let encode := encoder_impl enc_dec.
  (* (stationID ▹ SetCurrentByte ≫
     const WO~0~0~0~0~0~0~0~0 ▹ SetCurrentByte ≫
     const WO~0~0~0~0~0~1~1~1 ▹ SetCurrentByte ≫
     const WO~1~1~1~0~0~0~1~0 ▹ SetCurrentByte ≫
     (fun (v4 : ByteBuffer.t sz) (idx4 : nat) (r4 : sensor_msg) =>
      (low_bits 8 ▹ SetCurrentByte ≫
       shift_right 8 ▹ SetCurrentByte) v4 idx4 (Word.combine ((snd ∘ data) r4) ((Vector.nth [WO~0~0; WO~0~1] ∘ (fst ∘ data)) r4)))) v
  0 r tt *)
  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : ByteBuffer.t sz) =>
     (b <- GetCurrentByte;
     _ <- GetCurrentByte;
     b1 <- GetCurrentByte;
     b' <- GetCurrentByte;
     w <- return b1⋅b';
     (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
     then
        b2 <- GetCurrentByte;
        b'0 <- GetCurrentByte;
        w0 <- return b2⋅b'0;
        Ifopt if weqb (split2 14 2 w0) WO~0~0
        then Some Fin.F1
        else
        match (if weqb (split2 14 2 w0) WO~0~1 then Some Fin.F1 else None) with
          | Some f => Some (Fin.FS f)
          | None => None
          end as a' Then return {| stationID := b; data := (a', split1 14 2 w0) |} Else fail
  else fail)) v 0 tt *)
End Sensor2.

(** The use of `format_const _` in the specification forces conforming encoders must write out the value 0x7e2, encoded over 16 bits.  Accordingly, the generated decoder throws an exception if its input does not contain that exact sequence.  The argument passed to `format_enum` specifies which bit patterns to use to represent each tag (`0b00` for `"TEMPERATURE"`, `0b01` for `"HUMIDITY"`), and the decoder uses this mapping to reconstruct the appropriate enum member. **)

(** We use the next iteration to illustrate data dependencies and input restrictions.  To do so, we replace our single data point with a list of measurements (for conciseness, we remove tags and use 16-bit words).  We start as before, but we quickly run into an issue : **)

Module Sensor3.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof.
    derive_encoder_decoder_pair.
    last_failing_goal.
    all:simpl.
  Abort.
End Sensor3.

(** The derivation fails, leaving multiple Coq goals unsolved.  We forgot to encode the length of the `data` list, and this prevents Narcissus from generating a decoder.  Our attempted fix, unfortunately, only gets us half of the way there (`format_nat 8 ◦ length` specifies that the length of the list should be truncated to 8 bits and written out): **)

Module Sensor4.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_nat 8 ◦ length ◦ data
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.
         last_failing_goal.
         all:simpl.
  Abort.
End Sensor4.

(** Again, decoder generation fails and produces an unsolvable goal. The problem is that, since we encode the list's length on 8 bits, the round-trip property that Narcissus attempts to prove only holds if the list has less than \(2^{8}\) elements: larger lists have their length truncated, and it becomes impossible for the decoder to know for cetain how many elements it should decode.  What we need is an input restriction: a predicate defining which messages we may encode; to this end, we update our example as follows:
**)

Module Sensor5.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_nat 8 ◦ length ◦ data
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(data)) < pow2 8.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : ByteBuffer.t sz) =>
     (stationID ⋙ SetCurrentByte ≫
      data ⋙ Datatypes.length ⋙ natToWord 8 ⋙ SetCurrentByte ≫
      const WO~0~0~0~0~0~1~1~1 ⋙ SetCurrentByte ≫
      const WO~1~1~1~0~0~0~1~0 ⋙ SetCurrentByte ≫
      data ⋙ AlignedEncodeList (fun n : nat => low_bits 8 ⋙ SetCurrentByte ≫
                                               shift_right 8 ⋙ SetCurrentByte) sz) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : ByteBuffer.t sz) =>
     (b <- GetCurrentByte;
      b0 <- GetCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
       then
        l <- ListAlignedDecodeM
               (fun numBytes : nat =>
                w0 <- GetCurrentByte;
                w' <- w1 <- GetCurrentByte;
                      w' <- return WO;
                      return w1⋅w';
                return w0⋅w') (wordToNat b0);
        return {| stationID := b; data := l |}
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
      split; try reflexivity;
        intros; eapply format_word_inhabited'; intros; eauto.
  Qed.

  Let dec_reading :=
    fun t ctx =>
    `(w, rest, ctx') <- decode_word t ctx;
      if weqb (split1 2 14 w) WO~0~0
      then Some (Temperature (split2 2 14 w), rest, ctx')
      else (if weqb (split1 2 14 w) WO~0~1 then
              Some (Humidity (split2 2 14 w), rest, ctx')
            else None).

  Transparent weqb.

  Lemma dec_readingCorrect
    : CorrectDecoder _ (fun _ => True) (fun _ => True) eq format_reading dec_reading (fun _ => True)
                     format_reading.
  Proof.
    eapply format_decode_correct_EquivFormatAndView
        with (fun m => format_word (match m with
                                 | Temperature t => Word.combine WO~0~0 t
                                 | Humidity h => Word.combine WO~0~1 h
                                 end)); eauto.
    unfold flip, EquivFormat, format_reading. intros; destruct s; reflexivity.

    apply_bijection_rule' with (fun w =>
                                  if weqb (split1 2 14 w) WO~0~0
                                  then Some (Temperature (split2 2 14 w))
                                  else (if weqb (split1 2 14 w) WO~0~1 then
                                          Some (Humidity (split2 2 14 w))
                                        else None));
      intuition eauto.
    - apply Word_decode_correct. try apply unfold_cache_inv_Property; intuition eauto.
    - destruct s; simpl; rewrite split2_combine; auto.
    - destruct weqb eqn:?; injections. apply weqb_true_iff in Heqb.
      rewrite <- Heqb. apply Word.combine_split.
      destruct (weqb _ WO~0~1) eqn:?; try discriminate; injections. apply weqb_true_iff in Heqb0.
      rewrite <- Heqb0. apply Word.combine_split.
    - intuition eauto.
    - derive_decoder_equiv; easy.
  Qed.

  Opaque weqb.
  Record sensor_msg :=
    { stationID: word 8; data: list reading }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 8 ◦ length ◦ data
    ++ format_list format_reading ◦ data.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(data)) < pow2 8.

  Ltac new_encoder_rules ::= apply enc_readingCorrect.
  Ltac apply_new_base_rule ::= apply dec_readingCorrect.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.
  Defined.

  Let encode := encoder_impl enc_dec.
  Let decode := decoder_impl enc_dec.

End Sensor6.
