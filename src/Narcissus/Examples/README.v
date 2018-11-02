Require Import Fiat.Narcissus.Examples.TutorialPrelude.

Ltac derive_encoder_decoder_pair :=
  econstructor;
  [ synthesize_aligned_encoder |
    synthesize_aligned_decoder ].

Record EncoderDecoderPair {A : Type}
       (format : FormatM A ByteString)
       (predicate : A -> Prop) :=
  { enc : CorrectAlignedEncoderFor format;
    dec : CorrectAlignedDecoderFor predicate format }.

Arguments enc {_} [_] [_].
Arguments dec {_} [_] [_].

Notation encoder_impl x :=
  (simplify (encoder_impl' x.(enc))) (only parsing).

Notation decoder_impl x :=
  (simplify (decoder_impl' x.(dec))) (only parsing).

Open Scope AlignedDecodeM.

Require Import Fiat.Common.EnumType
        Fiat.Narcissus.Formats.EnumOpt.

Notation "'fail'" := ThrowAlignedDecodeM.

(**
The following section presents the Narcissus framework through a series of increasingly complex examples showcasing its main features.  Details are purposefuly omitted; they will be revealed in section N.  The end result is a moderately complex description for the packet format used by an indoor temperature sensor to report measurements to a smart home controller.
**)

(**
We start with an extremely simple record, and a correspondingly simple format:
**)

Module Sensor0.
  Record sensor_msg :=
    { stationID: word 8;
      measurement: word 16 }.

  Definition format :=
       format_word ◦ stationID
    ++ format_word ◦ measurement.

  Definition invariant (msg: sensor_msg) :=
    True.

  Definition encoder_decoder :
    EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl encoder_decoder.
  Let decode := decoder_impl encoder_decoder.
  (* decode = 
       fun (sz : nat) (v : t Core.char sz) =>
       (b <- GetCurrentByte;
        b0 <- GetCurrentByte;
        b' <- GetCurrentByte;
        w <- return b0⋅b';
        return {| stationID := b; measurement := w |}) v 0 tt
            : forall sz : nat, t Core.char sz -> option (sensor_msg * nat * CacheDecode) *)
End Sensor0.

(** All user input is contained in box 1. `sensor_msg` is a record type with two fields; the Coq `Record` command additionally defines two functions `stationID` and `measurement` (of type `sensor_msg → …`) to access these fields. `format` specifies how to encode instances of this record: `format_word` is a Narcissus primitive that writes out its input bit by bit, and `++` is a sequencing operator (write this, then that).  `invariant` specifies additional constraints on well-formed packets, but there are none here.  Box 2 calls the `derive_encoder_decoder_pair` tactic provided by Narcissus, which generates an encoder and a decoder along with proofs of correctness (it takes about two to five seconds to return); the rest is routine boilerplate.  Boxes 3 and 4 show generated code. In box 3, the generated encoder takes a packet and a byte buffer and returns the encoded packet or None if it did not fit in the supplied buffer. In box 4, the decoder takes a buffer, and returns a packet or None if the buffer did not contain a valid encoding. Both generated programs live in stateful error monads, offering primitives to read (GetCurrentByte), skip (SkipCurrentByte), and write (SetCurrentByte) a single byte.  The encoder uses `split1` and `split2` to extract the high and low bites of the `measurement` field, and the decoder reassembles these two bytes using a shift and an addition, using the `⋅` operator: this byte-alignment transformation is part of the `derive_encoder_decoder_pair` logic. **)

(** We now introduce a twist: to preserve 16-bit alignment, we introduce 8 bits of padding after encoding `stationID`; these bits will be reserved for future use. **)

Module Sensor1.
  Record sensor_msg :=
    { stationID: word 8;
      measurement: word 16 }.

  Definition format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_word ◦ measurement.

  Definition invariant (msg: sensor_msg) :=
    True.

  Definition encoder_decoder :
    EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl encoder_decoder.
  Let decode := decoder_impl encoder_decoder.
End Sensor1.

(** Notice the asymmetry that these 8 under-specified bits introduce: although the encoder always writes `0x00`, the decoder accepts any value.  This is crucial because the `format_unused_word` specification allows conforming encoders to output any 8-bits value; as a result, the decoder must accept all 8-bit values.  In that sense, the encoder and decoder that Narcissus generates are not inverse of each other: the encoder is one among a family of functions permitted by the formatting specification, and the decoder is the inverse of the *entire family*, accepting any output produced by a conforming encoder. **)

(** Our next enhancement is to introduce a version number field in our packet, and to tag each measurement with a `kind`, `"TEMPERATURE"` or `"HUMIDITY"`.  To save space, we allocate 2 bits for the `kind` tag, and 14 bits to the actual measurement. **)

Module Sensor2.
  Let kind := EnumType ["TEMPERATURE"; "HUMIDITY"].
  Record sensor_msg :=
    { stationID: word 6;
      measurement: (kind * word 14) }.

  Definition format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_enum [WO~0~0; WO~0~1] ◦ fst ◦ measurement
    ++ format_word ◦ snd ◦ measurement
    ++ format_word ◦ snd ◦ measurement.

  Definition invariant (msg: sensor_msg) :=
    True.

  Definition encoder_decoder :
    EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Abort.

  (* Let encode := encoder_impl encoder_decoder. *)
  (* Let decode := decoder_impl encoder_decoder. *)
End Sensor2.

(** The use of `format_const` in the specification forces conforming encoders must write out the value 0x7e2, encoded over 16 bits.  Accordingly, the generated decoder throws an exception if its input does not contain that exact sequence.  The argument passed to `format_enum` specifies which bit patterns to use to represent each tag (`0b00` for `"TEMPERATURE"`, `0b01` for "HUMIDITY"), and the decoder uses this mapping to reconstruct the appropriate enum member. **)

(** Our last example gives us an occasion to illustrate data dependencies and input restrictions.  To do so, we replace our single data point with a list of measurements (for conciseness, we remove tags and use 16-bit words).  We start as before, but we quickly run into an issue : **)

Module Sensor3.
  Record sensor_msg :=
    { stationID: word 8;
      measurements: list (word 16) }.

  Definition format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ measurements.

  Definition invariant (msg: sensor_msg) :=
    True.

  Definition encoder_decoder :
    EncoderDecoderPair format invariant.
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
    { stationID: word 8;
      measurements: list (word 16) }.

  Definition format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 16 ◦ length ◦ measurements
    ++ format_list format_word ◦ measurements.

  Definition invariant (msg: sensor_msg) :=
    True.

  Definition encoder_decoder :
    EncoderDecoderPair format invariant.
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
    { stationID: word 8;
      measurements: list (word 16) }.

  Definition format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 8 ◦ length ◦ measurements
    ++ format_list format_word ◦ measurements.

  Definition invariant := fun (msg: sensor_msg) =>
                           length (msg.(measurements)) < pow2 8. (* FIXME make format_nat 8 work *)

  Definition encoder_decoder :
    EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl encoder_decoder.

  (* Notation "x |> y" := (Projection_AlignedEncodeM y x _) (right associativity, at level 2). *)
  Goal Some (projT1 (enc encoder_decoder)) = None.
    simpl.
    unfold Projection_AlignedEncodeM.

    Transparent mult.
    Arguments mult: simpl nomatch.

    Transparent plus.
    Arguments plus: simpl nomatch.

    Definition Projection_AlignedEncodeM'
               {S' S'' : Type}
               {cache : Cache}
               {sz}
               (encode : AlignedEncodeM (S := S'') sz)
               (f : S' -> S'')
      : AlignedEncodeM (S := S') sz :=
      fun v idx s' env =>
        encode v idx (f s') env.

    Lemma cleanup_aligned_encoder_init {cache S2}:
      forall (sz : nat) (v : t Core.char sz) idx (r : S2) ch,
      forall (f: @AlignedEncodeM cache _ sz)
        (g: @AlignedEncodeM cache S2 sz)
        (h: forall sz, @AlignedEncodeM cache _ sz)
        (h': @AlignedEncodeM cache S2 sz),
        (let hsz := h sz in h' = h sz) ->
        (AppendAlignedEncodeM f g) v idx r ch = h' v idx r ch ->
        (AppendAlignedEncodeM f g) v idx r ch = h sz v idx r ch.
    Proof. intros; congruence. Qed.

    Lemma cleanup_aligned_encoder_bind {cache S2}:
      forall (sz : nat) (v : t Core.char sz) idx (r : S2) ch,
      forall (f f' g g': @AlignedEncodeM cache S2 sz),
        (forall v idx r ch, g v idx r ch = g' v idx r ch) ->
        (forall v idx r ch, f v idx r ch = f' v idx r ch) ->
        (AppendAlignedEncodeM f g) v idx r ch =
        (AppendAlignedEncodeM f' g') v idx r ch.
    Proof. compute; intros * Hg Hf. rewrite Hf; destruct (f' _ _ _ _); congruence. Qed.

      Lemma cleanup_aligned_encoder_bind_projection {cache S1 S2 sz}:
        forall (f f' g g': @AlignedEncodeM cache S2 sz)
          (h: @AlignedEncodeM cache S1 sz) proj,
          (forall v idx r ch, f v idx r ch = f' v idx r ch) ->
          (forall v idx r ch, g v idx r ch = g' v idx r ch) ->
          (let cleaned_up := (AppendAlignedEncodeM f' g') in
           forall v idx r1 ch, cleaned_up v idx (proj r1) ch = h v idx r1 ch) ->
          forall (v : t Core.char sz) idx (r1: S1) r2 ch,
            r2 = proj r1 -> (AppendAlignedEncodeM f g) v idx r2 ch = h v idx r1 ch.
      Proof.
        intros f f' g g' h proj Hf Hg Hh v idx r1 r2 ch eq.
        specialize (Hh v idx r1 ch); compute in *.
        rewrite eq, Hf in *; destruct (f' _ _ _ _); congruence.
      Qed.

    Lemma cleanup_aligned_encoder_assoc {cache S1}:
      forall (sz : nat) (r : S1) (v : t Core.char sz) ch idx,
      forall (f1 f2 g: @AlignedEncodeM cache S1 sz)
        x,
        (AppendAlignedEncodeM f1 (AppendAlignedEncodeM f2 g)) v idx r ch = x ->
        (AppendAlignedEncodeM (AppendAlignedEncodeM f1 f2) g) v idx r ch = x.
    Proof. compute; intros; destruct (f1 _ _ _ _); [ destruct (f2 _ _ _ _) | ]; congruence. Qed.

    Lemma cleanup_aligned_encoder_distribute {cache S1 S2}:
      forall (sz : nat) (r : S1) (v : t Core.char sz) ch idx,
      forall (f1 f2: @AlignedEncodeM cache S2 sz)
        (g: @AlignedEncodeM cache S1 sz)
        x proj,
        (AppendAlignedEncodeM
           (fun v idx r => f1 v idx (proj r))
           (AppendAlignedEncodeM (fun v idx r => f2 v idx (proj r)) g)) v idx r ch = x ->
        (AppendAlignedEncodeM (fun v idx r => (AppendAlignedEncodeM f1 f2) v idx (proj r)) g) v idx r ch = x.
    Proof. compute; intros; destruct (f1 _ _ _ _); [ destruct (f2 _ _ _ _) | ]; congruence. Qed.

    Ltac cleanup_single_encoder :=
      match goal with
      | [  |- forall v idx s ce, @?f v idx s ce = @?g v idx s ce ] =>
        change (forall v idx s ce, f v idx s ce = g v idx s ce); intros;
          repeat change (fun x => ?h x) with h;
          change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx ?cst) with
              (fun (v : Tv) (idx : Tidx) (s : Ts) => f v idx ((const cst) s));
          change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx (?g s)) with
              (Projection_AlignedEncodeM' f g);
          change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx (?g1 (?g2 s))) with
              (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' f g1) g2);
          change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx (?g1 (?g2 (?g3 s)))) with
              (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' f g1) g2) g3)
      end.

    Ltac derive_clean_encoder__reflexivity :=
      match goal with
      | [ |- ?x = ?proj ?y ] =>
        is_evar proj;
        let ty := type of y in
        match (eval pattern y in x) with ?fx _ => unify fx (@const _ ty x) end;
        simple apply (eq_refl ((const x) y))
      | _ => reflexivity
      end.

    Lemma AlignedEncodeList_morphism {cache: Cache} {A: Type}:
      forall (encA encA': forall sz, AlignedEncodeM sz) sz,
        (forall v idx r ch, encA sz v idx r ch = encA' sz v idx r ch) ->
        (forall r v idx ch,
            @AlignedEncodeList cache A encA sz v idx r ch =
            @AlignedEncodeList cache A encA' sz v idx r ch).
    Proof.
      intros * Heq; induction r; simpl; intros.
      - reflexivity.
      - rewrite Heq; destruct (encA' _ _ _ _ _); simpl; congruence.
    Qed.

    Ltac cleanup_encoder_break_bind :=
      repeat (intros;
              (simple eapply cleanup_aligned_encoder_assoc ||
               simple eapply cleanup_aligned_encoder_distribute ||
               simple eapply cleanup_aligned_encoder_bind ||
               eapply AlignedEncodeList_morphism ||
               (simple eapply cleanup_aligned_encoder_bind_projection;
                [ .. | intro | derive_clean_encoder__reflexivity ]))).

    Ltac exact_computed t :=
      let t' := (eval compute in t) in exact t'.

    Ltac cleanup_encoder_postprocess :=
      simpl;
      repeat change (fun x => ?h x) with h;
      repeat change (wzero ?sz) with (ltac:(let w0 := (eval compute in (wzero sz)) in exact w0));
      repeat ((change (@split1' (S ?sz1) ?sz2 (WS ?b ?w)) with
                   (ltac:(exact_computed (@split1' (S sz1) sz2 (WS b w))))) ||
              (change (@split2' (S ?sz1) ?sz2 (WS ?b ?w)) with
                   (ltac:(exact_computed (@split2' (S sz1) sz2 (WS b w)))))).

    Ltac derive_clean_encoder :=
      intros;
      unfold SetCurrentBytes;
      eapply cleanup_aligned_encoder_init; [
        match goal with
        | [ |- _ ?v ?idx ?r ?ch = _ ] => refine (eq_trans (y := (_: AlignedEncodeM _) v idx r ch) _ _)
        end;
        [ cleanup_encoder_break_bind;
          cleanup_single_encoder;
          reflexivity
        | cleanup_encoder_postprocess;
          reflexivity ]
      | reflexivity ].

    Notation "y ∘ x" := (Projection_AlignedEncodeM' y x) (left associativity, at level 40).

    Fail match goal with
    | [  |- Some ?f = None ] =>
      let g := constr:(
                ltac:(eexists; derive_clean_encoder)
                : { g : (forall sz : nat, @AlignedEncodeM _ _ sz)
                        & forall (sz : nat) (v : Vector.t Core.char sz) (r: sensor_msg) idx ch, f sz v idx r ch = g sz v idx r ch }) in
      let gg := (eval simpl in (projT1 g)) in
      pose gg
    end.

    match goal with
    | [  |- Some ?f = None ] =>
      assert { g : (forall sz : nat, @AlignedEncodeM _ _ sz)
                        & forall (sz : nat) (v : Vector.t Core.char sz) (r: sensor_msg) idx ch, f sz v idx r ch = g sz v idx r ch }
    end.
    eexists.

      intros;
      unfold SetCurrentBytes;
      eapply cleanup_aligned_encoder_init; [ reflexivity | ];
      match goal with
      | [ |- _ ?v ?idx ?r ?ch = _ ] => refine (eq_trans (y := (_: AlignedEncodeM _) v idx r ch) _ _)
      end;
      [ cleanup_encoder_break_bind
      | cleanup_encoder_postprocess ].

      intros; eapply cleanup_aligned_encoder_init.
      2: cleanup_encoder_break_bind.
      all: try (cleanup_single_encoder; reflexivity).
      reflexivity.
      Focus 2.
      cleanup_encoder_break_bind.
      
      clear.

    derive_clean_encoder.
          intros;
      eapply cleanup_aligned_encoder_init; [ reflexivity | ];
      repeat (intros;
              (simple eapply cleanup_aligned_encoder_assoc ||
               simple eapply cleanup_aligned_encoder_distribute ||
               simple eapply cleanup_aligned_encoder_bind ||
               (simple eapply cleanup_aligned_encoder_bind_projection;
                [ .. | intro | derive_clean_encoder__reflexivity ])));
      cleanup_single_encoder
      eapply cleanup_aligned_encoder_init; [ reflexivity | ].
    repeat (intros; (simple eapply cleanup_aligned_encoder_assoc ||
                     simple eapply cleanup_aligned_encoder_distribute ||
                     simple eapply cleanup_aligned_encoder_bind ||
                     simple eapply cleanup_aligned_encoder_bind_projection)).
    (intros; (simple eapply cleanup_aligned_encoder_bind)).
    (intros; (simple eapply cleanup_aligned_encoder_bind)).
    (intros; (simple eapply cleanup_aligned_encoder_bind)).
    (intros; (simple eapply cleanup_aligned_encoder_bind)).
      (* cleanup_single_encoder. *)

    Focus 3.
    intros.

    Lemma cleanup_aligned_encoder_bind' {cache S2}:
      forall (sz : nat) (v : t Core.char sz) idx (r : S2) ch,
      forall (f f' g g': @AlignedEncodeM cache S2 sz) x,
        (forall v idx r ch, g v idx r ch = g' v idx r ch) ->
        (forall v idx r ch, f v idx r ch = f' v idx r ch) ->
        (AppendAlignedEncodeM f' g') v idx r ch = x ->
        (AppendAlignedEncodeM f g) v idx r ch = x.
    Proof. compute; intros * Hg Hf. rewrite Hf; destruct (f' _ _ _ _); congruence. Qed.
    unfold AppendAlignedEncodeM at 1.
    simple eapply cleanup_aligned_encoder_bind'.
    intros; simple eapply cleanup_aligned_encoder_bind'.
    eapply (cleanup_aligned_encoder_assoc sz r2 v2 ch1 idx1).













    
  Let decode := decoder_impl encoder_decoder.
End Sensor5.

(**

decode = 
fun (sz : nat) (v : t Core.char sz) =>
(b <- GetCurrentByte;
 _ <- SkipCurrentByte;
 b1 <- GetCurrentByte;
 b' <- GetCurrentByte;
 w <- return b1⋅b';
 (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
  then
   b2 <- GetCurrentByte;
   l <- ListAlignedDecodeM (fun numBytes : nat => w0 <- GetCurrentByte;
                                                  w' <- w1 <- GetCurrentByte;
                                                        w' <- return WO;
                                                        return w1⋅w';
                                                  return w0⋅w') (wordToNat b2);
   return {| stationID := b; measurements := l |}
  else fail)) v 0 tt

**)
