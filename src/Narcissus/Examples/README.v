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
  Goal Some (encoder_impl encoder_decoder) = None.
    unfold "|>".

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
      forall (sz : nat) (r : S2) (v : t Core.char sz) ch idx,
      forall (f: @AlignedEncodeM cache _ sz)
        (g: @AlignedEncodeM cache S2 sz)
        (h: forall sz, S2 -> Vector.t Core.char sz -> _)
        (h': @AlignedEncodeM cache S2 sz),
        h' v idx r ch = h sz r v ->
        (AppendAlignedEncodeM f g) v idx r ch = h' v idx r ch ->
        (AppendAlignedEncodeM f g) v idx r ch = h sz r v.
    Proof. intros; congruence. Qed.

    Lemma cleanup_aligned_encoder_projection {cache S1 S2}:
      forall (sz : nat) (r : S2) (v : t Core.char sz) ch idx,
      forall (f: @AlignedEncodeM cache S1 sz)
        (g: @AlignedEncodeM cache S2 sz)
        proj x,
        (AppendAlignedEncodeM
           (Projection_AlignedEncodeM' f proj)
           g) v idx r ch = x ->
        (AppendAlignedEncodeM
           (fun (v0 : t Core.char sz) (idx : nat) (s : S2) (env : CacheFormat) =>
              f v0 idx (proj s) env)
           g) v idx r ch = x.
    Proof. compute; intros; congruence. Qed.

    Lemma cleanup_aligned_encoder_bind {cache S2}:
      forall (sz : nat) (r : S2) (v : t Core.char sz) ch idx,
      forall (f g h: @AlignedEncodeM cache S2 sz),
        (forall v idx r ch, g v idx r ch = h v idx r ch) ->
        (AppendAlignedEncodeM f g) v idx r ch =
        (AppendAlignedEncodeM f h) v idx r ch.
    Proof. compute; intros; destruct (f _ _ _ _); congruence. Qed.

    Lemma cleanup_aligned_encoder_assoc {cache S1 S2}:
      forall (sz : nat) (r : S2) (v : t Core.char sz) ch idx,
      forall (f1 f2: @AlignedEncodeM cache S1 sz)
        (g: @AlignedEncodeM cache S2 sz)
        proj x,
        (AppendAlignedEncodeM
           (fun (v0 : t Core.char sz) (idx : nat) (s : S2) (env : CacheFormat) =>
              f1 v0 idx (proj s) env)
           (AppendAlignedEncodeM
              (fun (v0 : t Core.char sz) (idx : nat) (s : S2) (env : CacheFormat) =>
                 f2 v0 idx (proj s) env)
              g)) v idx r ch = x ->
        (AppendAlignedEncodeM
           (fun (v0 : t Core.char sz) (idx : nat) (s : S2) (env : CacheFormat) =>
              (AppendAlignedEncodeM f1 f2) v0 idx (proj s) env)
           g) v idx r ch = x.
    Proof. compute; intros; destruct (f1 _ _ _ _); [ destruct (f2 _ _ _ _) | ]; congruence. Qed.

    Ltac derive_clean_encoder :=
      intros;
      eapply cleanup_aligned_encoder_init; [ reflexivity | ];
      repeat (intros; first [ eapply cleanup_aligned_encoder_assoc |
                              eapply cleanup_aligned_encoder_projection;
                              [ | eapply cleanup_aligned_encoder_bind ] ]);
      reflexivity.

    Notation "x |> y" := (Projection_AlignedEncodeM' y x) (right associativity, at level 2).

    Ltac exact_computed t :=
      let t' := (eval compute in t) in exact t'.

    Definition const {A B} (a: A) := fun (_: B) => a.

    Ltac cleanup_encoder enc :=
      let nm := fresh in
      pose enc as nm;
      simpl in nm;
      repeat change (fun x => ?h x) with h in nm;
      repeat change (wzero ?sz) with (ltac:(let w0 := (eval compute in (wzero sz)) in exact w0)) in nm;
      repeat ((change (@split1' (S ?sz1) ?sz2 (WS ?b ?w)) with
                   (ltac:(exact_computed (@split1' (S sz1) sz2 (WS b w)))) in nm) ||
              (change (@split2' (S ?sz1) ?sz2 (WS ?b ?w)) with
                   (ltac:(exact_computed (@split2' (S sz1) sz2 (WS b w)))) in nm));
      repeat change (fun (_: ?B) => ?cst) with (ltac:(let A := (type of cst) in exact (@const A B cst))) in nm.

    match goal with
    | [  |- Some ?f = None ] => pose f
    end.

    (* unfold split1', split2' in nm; simpl in nm; *)
    (* fold @split1' in nm; fold @split2' in nm. *)

    (* unfold SetCurrentBytes; simpl. *)

    unfold SetCurrentBytes.
    (* match goal with *)
    (* | [  |- Some ?f = None ] => *)
    (*   let g := constr:( *)
    (*             ltac:(eexists; derive_clean_encoder) *)
    (*             : { g : (forall sz : nat, sensor_msg -> t Core.char sz -> option (t Core.char sz * nat * @CacheFormat _)) *)
    (*                     & forall (sz : nat) (r : sensor_msg) (v : t Core.char sz), f sz r v = g sz r v }) in *)
    (*   cleanup_encoder (projT1 g) *)
    (* end. *)

    Goal True.
      pose (fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
       ((fun (v0 : t Core.char sz) (idx : nat) (s' : sensor_msg) (env : CacheFormat) =>
         SetCurrentByte v0 idx (stationID s') env)>>
        (fun (v0 : t Core.char sz) (idx : nat) (_ : sensor_msg) => SetCurrentByte v0 idx (wzero 8))>>
        (fun (v0 : t Core.char sz) (idx : nat) (_ : sensor_msg) (env : CacheFormat) =>
         SetCurrentBytes (sz := 2) v0 idx WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0 env)>>
        (fun (v0 : t Core.char sz) (idx : nat) (s' : sensor_msg) (env : CacheFormat) =>
         SetCurrentByte v0 idx (natToWord 8 (| measurements s' |)) env)>>
        (fun (v0 : t Core.char sz) (idx : nat) (s' : sensor_msg) (env : CacheFormat) =>
         AlignedEncodeList (fun n : nat => SetCurrentBytes (sz := 2)) sz v0 idx (measurements s') env))%AlignedEncodeM v 0 r
         tt) as f.
      assert { g : (forall sz : nat, sensor_msg -> t Core.char sz -> option (t Core.char sz * nat * @CacheFormat test_cache))
                                    & forall (sz : nat) (r : sensor_msg) (v : t Core.char sz), f sz r v = g sz r v }.
      eexists; intros.
      eapply cleanup_aligned_encoder_init; [ reflexivity | ].
      repeat (intros; first [ eapply cleanup_aligned_encoder_assoc |
                              eapply cleanup_aligned_encoder_bind ]).
      

      unfold SetCurrentBytes.
      repeat change (fun x => ?h x) with h.
      change (fun (v : t Core.char ?sz) (idx : nat) (s' : ?T) => ?f v idx ?cst) with
          (fun (v : t Core.char sz) (idx : nat) (s' : T) => f v idx ((const cst) s')).
      change (fun (v : t Core.char ?sz) (idx : nat) (s' : _) => ?f v idx (?g s')) with
          (Projection_AlignedEncodeM' (sz := sz) f g).
      change (fun (v : t Core.char ?sz) (idx : nat) (s' : _) => ?f v idx (?g1 (?g2 s'))) with
          (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' f g1) g2).
      change (fun (v : t Core.char ?sz) (idx : nat) (s' : _) => ?f v idx (?g1 (?g2 (?g3 s')))) with
          (Projection_AlignedEncodeM' (sz := sz) (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' f g1) g2) g3).
      
      apply cleanup_aligned_encoder_bind; intros.
          (Projection_AlignedEncodeM' (sz := sz) f g).
      change (fun (v : t Core.char ?sz) (idx : nat) (s' : sensor_msg) =>
                ?f v idx (?g s') env) with
          (Projection_AlignedEncodeM' (sz := sz) f g).
      
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_projection;
                       eapply cleanup_aligned_encoder_bind ]).

      (intros; first [ eapply cleanup_aligned_encoder_assoc
                     |
                     eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc;
                       [ | eapply cleanup_aligned_encoder_projection] |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc;
                       [ | eapply cleanup_aligned_encoder_projection] |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc;
                       [ | eapply cleanup_aligned_encoder_projection] |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc;
                       [ | eapply cleanup_aligned_encoder_projection] |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc;
                       [ | eapply cleanup_aligned_encoder_projection] |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc;
                       [ | eapply cleanup_aligned_encoder_projection] |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_projection |
                       eapply cleanup_aligned_encoder_bind ]).
      Focus 2.
            (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_projection |
                       eapply cleanup_aligned_encoder_bind ]).

      unfold SetCurrentBytes.
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      (intros; first [ eapply cleanup_aligned_encoder_assoc |
                       eapply cleanup_aligned_encoder_bind ]).
      derive_clean_encoder.
        intros;
        [ reflexivity | ].
      unfold SetCurrentBytes.
      cleanup_encoder enc
      intros;
        first [eapply cleanup_aligned_encoder_bind |
               eapply cleanup_aligned_encoder_bind_const ].
      Show Proof.
      intros.

      repeat change (fun (v : Vector.t Core.char _) (idx : nat) (_ : ?tmsg) (env : @CacheFormat ?cache) =>
                       ?f v idx ?x env)
        with (fun (v : Vector.t Core.char _) (idx : nat) (s : tmsg) (env : @CacheFormat cache) =>
                f v idx ((fun _ => x) s) env).

      eapply cleanup_aligned_encoder_bind.
      unfold SetCurrentBytes.
      intros.

      eapply cleanup_aligned_encoder_assoc.
      eapply cleanup_aligned_encoder_bind.
      intros.
      eapply cleanup_aligned_encoder_assoc.
      eapply cleanup_aligned_encoder_bind.
      intros.
      eapply cleanup_aligned_encoder_bind.
      intros.
      eapply cleanup_aligned_encoder_bind.

      
      Show Proof.
      (* FIXME remove bind_const *)
      

      
      simpl.
        Show Proof.


        
        reflexivity.

      Show Proof.

    reflexivity.
    
    stationID -> SetCurrentByte;
    (const w0) -> SetCurrentByte;
    (const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0) -> SetCurrentBytes;
    measurements . length . natToWord 8 -> setCurrentByte;
    measurements . AlignedEncodeList SetCurrentBytes

    
    stationID |> (@SetCurrentByte test_cache test_cache_add_nat)

    
    unfold "|>".

    Definition cmp {A S sz cache} {cacheAdd: CacheAdd cache nat} (writer: AlignedEncodeM (S := S) sz) (f: A -> _) :=
      (fun (v0 : t Core.char sz) (idx : nat) (a: _) (env : CacheFormat) =>
       writer v0 idx (f a) env).

    Set Printing Implicit.
    Locate ">>".
    (* Unset Printing Notations. *)
    match goal with
    | [  |- Some ?f = None ] =>
      assert { g : (forall sz : nat, sensor_msg -> t Core.char sz -> option (t Core.char sz * nat * @CacheFormat test_cache))
                   & forall (sz : nat) (r : sensor_msg) (v : t Core.char sz), f sz r v = g sz r v }
    end.
    eexists.
    intros.
    Open Scope AlignedEncodeM.

    Lemma 
    
    simpl.
      let g :  :=
          ltac:(unshelve econstructor) in
      
      change f with
          (fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
             ltac:(let body := (eval cbv beta in (f sz r v)) in
                   match body with
                   | context[@AppendAlignedEncodeM test_cache sensor_msg _ ?y _] =>
                     let body := (change y with
                         (fun (v0 : t Core.char sz) (idx : nat) (s' : sensor_msg) (env : @CacheFormat test_cache) =>
                            ltac:(let ybody := (eval cbv beta in (y v0 idx s' env)) in
                                  match body with
                                  | ?f v0 idx (@?g s') env =>
                                    exact (idtac (fun x => f v0 idx x env) (g s'))
                                  end)) in body) in
                     exact body
                   end))
    end.
    match goal with
    | [  |- context [(fun (v0 : t Core.char _) (idx : nat) (s' : sensor_msg) (env : CacheFormat) =>
                       @?f v0 idx s' env)] ] => idtac
                                                 (* pose wrt; pose f *)
                                                 (* let C' := context C[cmp (wrt sz c) f] in *)
                                                 (* change C' *)
    end.
    Notation "[[[ xyz ===> f ]]]" :=
      ().
    
  Locate "|>".
  Print 
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
