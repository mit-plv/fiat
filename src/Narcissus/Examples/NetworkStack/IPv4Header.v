Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Our source data type for IP packets. *)
Definition IPv4_Packet :=
  @Tuple <"TotalLength" :: word 16,
          "ID" :: word 16,
          "DF" :: bool, (* Don't fragment flag *)
          "MF" :: bool, (*  Multiple fragments flag *)
          "FragmentOffset" :: word 13,
          "TTL" :: word 8,
          "Protocol" :: EnumType ["ICMP"; "TCP"; "UDP"],
          "SourceAddress" :: word 32,
          "DestAddress" :: word 32,
          "Options" :: list (word 32)>.

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
   WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
   WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Header_Len (ip4 : IPv4_Packet) := 5 + |ip4!"Options"|.

Definition IPv4_Packet_Format (ip4 : IPv4_Packet)  :=
          (format_word (natToWord 4 4)
    ThenC format_nat 4 (IPv4_Packet_Header_Len ip4)
    ThenC format_unused_word 8 (* TOS Field! *)
    ThenC format_word ip4!"TotalLength"
    ThenC format_word ip4!"ID"
    ThenC format_unused_word 1 (* Unused flag! *)
    ThenC format_bool ip4!"DF"
    ThenC format_bool ip4!"MF"
    ThenC format_word ip4!"FragmentOffset"
    ThenC format_word ip4!"TTL"
    ThenC format_enum ProtocolTypeCodes ip4!"Protocol"
    DoneC)
    ThenChecksum IPChecksum_Valid' OfSize 16
    ThenCarryOn (format_word ip4!"SourceAddress"
    ThenC format_word ip4!"DestAddress"
    ThenC format_list format_word ip4!"Options"
    DoneC)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4!"Options"|) 11 /\
  lt (20 + 4 * |ipv4!"Options"|) (wordToNat ipv4!"TotalLength").

(* Step One: Synthesize an encoder and a proof that it is correct. *)

Definition ipv4_encoder :
  CorrectAlignedEncoderFor IPv4_Packet_Format IPv4_Packet_OK.
Proof.
  synthesize_aligned_encoder.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition ipv4_encoder_impl r {sz} v :=
  Eval simpl in (projT1 ipv4_encoder r sz v 0 tt).

Definition IPv4_Packet_formatd_measure (ipv4_b : ByteString)
  : nat :=
  match (`(u, b') <- decode_unused_word' 4 ipv4_b;
           decode_word' 4 b') with
  | Some n => 32 * wordToNat (fst n)
  | None => 0
  end.

Lemma IPv4_Packet_Headiner_Len_Bound
  : forall (a : IPv4_Packet) (a_OK : IPv4_Packet_OK a),
    BinNat.N.lt (BinNat.N.of_nat (IPv4_Packet_Header_Len a)) (Npow2 4).
Proof.
  unfold IPv4_Packet_Header_Len.
  intros; unfold IPv4_Packet_OK in a_OK.
  destruct a_OK.
  rewrite <- BinNat.N.compare_lt_iff.
  rewrite Nnat.N2Nat.inj_compare.
  rewrite Nnat.Nat2N.id.
  rewrite <- Compare_dec.nat_compare_lt.
  simpl.
  unfold BinPos.Pos.to_nat; simpl.
  auto with arith.
Qed.

Lemma IPv4_Packet_Header_Len_eq
  : forall data len,
    IPv4_Packet_Header_Len data = len
    -> ((|data!"Options" |) = len - 5).
Proof.
  unfold IPv4_Packet_Header_Len; intros.
  apply Minus.plus_minus.
  rewrite H; reflexivity.
Qed.

Lemma computes_to_compose_decode_unused_word
  : forall (sz : nat) (w : word sz) (ctx ctx'' : CacheFormat)
           (rest : CacheFormat -> Comp (ByteString * CacheFormat))
           (b : ByteString),
    (format_word w ThenC rest) ctx ↝ (b, ctx'') ->
    exists (b' : ByteString) (ctx' : CacheFormat),
      rest ctx' ↝ (b', ctx'') /\
      (forall ext : ByteString, decode_unused_word' sz (mappend b ext) = Some ((), mappend b' ext)).
Proof.
Admitted.

Lemma computes_to_compose_decode_word
     : forall (sz : nat) (w : word sz) (ctx ctx'' : CacheFormat)
         (rest : CacheFormat -> Comp (ByteString * CacheFormat))
         (b : ByteString),
       (format_word w ThenC rest) ctx ↝ (b, ctx'') ->
       exists (b' : ByteString) (ctx' : CacheFormat),
         rest ctx' ↝ (b', ctx'') /\
         (forall ext : ByteString, decode_word' sz (mappend b ext) = Some (w, mappend b' ext)).
Proof.
Admitted.

Lemma IPv4_Packet_Header_Len_OK
  : forall ip4 (ctx ctx' ctx'' : CacheFormat) c b b'' ext,
    (format_word (natToWord 4 4)
    ThenC format_nat 4 (IPv4_Packet_Header_Len ip4)
    ThenC format_unused_word 8 (* TOS Field! *)
    ThenC format_word ip4!"TotalLength"
    ThenC format_word ip4!"ID"
    ThenC format_unused_word 1 (* Unused flag! *)
    ThenC format_bool ip4!"DF"
    ThenC format_bool ip4!"MF"
    ThenC format_word ip4!"FragmentOffset"
    ThenC format_word ip4!"TTL"
    ThenC format_enum ProtocolTypeCodes ip4!"Protocol"
    DoneC) ctx ↝ (b, ctx') ->
    (format_word ip4!"SourceAddress"
    ThenC format_word ip4!"DestAddress"
    ThenC format_list format_word ip4!"Options"
    DoneC) ctx' ↝ (b'', ctx'') ->
    IPv4_Packet_OK ip4 ->
    (fun _ => 128) ip4 + (fun a => 16 + |ip4!"Options"| * 32) ip4 + (bin_measure mempty) + 16 = IPv4_Packet_formatd_measure (mappend (mappend b (mappend (format_checksum _ _ _ 16 c) b'')) ext).
Proof.
  intros.
  set (k := mempty); simpl in k; subst k.
  simpl bin_measure.
  rewrite AlignedByteString.length_ByteString_id.
  unfold IPv4_Packet_formatd_measure.
  pose proof mappend_assoc as H'; simpl in H';
    rewrite <- !H'.
  eapply computes_to_compose_decode_unused_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold DecodeBindOpt, BindOpt, If_Opt_Then_Else.
  eapply computes_to_compose_decode_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold fst.
  rewrite wordToNat_natToWord_idempotent; try reflexivity;
    eauto using IPv4_Packet_Headiner_Len_Bound.
  unfold IPv4_Packet_Header_Len.
  rewrite Mult.mult_plus_distr_l.
  omega.
Qed.

Hint Resolve IPv4_Packet_Header_Len_eq : data_inv_hints.

(* A (hopefully) more convenient IP_Checksum lemma *)

Definition decode_IPChecksum
  : ByteString -> CacheDecode -> option (() * ByteString * CacheDecode) :=
  decode_unused_word 16.

Definition encode_word {sz} (w : word sz) : ByteString :=
  encode_word' sz w ByteString_id.

Definition IPChecksum (b b' : ByteString) : ByteString :=
  let b'' := if Peano_dec.eq_nat_dec (padding b) 0 then mempty
             else encode_word (wzero (8 - (padding b))) in
  mappend b''
            (encode_word (wnot (onesComplement
                                  (ByteString2ListOfChar (bin_measure (mappend b b')) (BoundedByteStringToByteString(mappend b b')))))).

Definition IPChecksum_Valid_dec (n : nat) (b : ByteString)
  : {IPChecksum_Valid' n b} + {~IPChecksum_Valid' n b} := weq _ _.

Lemma CorrectAlignedDecoderForIPChecksumThenC {A}
      predicate
      (format_A format_B : FormatM A ByteString)
      (len_format_A : A -> nat)
      (len_format_A_OK : forall a' b ctx ctx',
          computes_to (format_A a' ctx) (b, ctx')
          -> length_ByteString b = len_format_A a')
  : CorrectAlignedDecoderFor
      predicate
      (fun a => (format_A a) ThenC format_unused_word 16 ThenC (format_B a))
    -> CorrectAlignedDecoderFor
      predicate
      (fun a => (format_A a) ThenChecksum IPChecksum_Valid' OfSize 16 ThenCarryOn (format_B a)).
  Proof.
    intros H; destruct H as [ ? [ [? ?] ?] ].
  Admitted.

Lemma length_ByteString_compose :
  forall format1 format2 b (ctx ctx' : CacheFormat) n n',
    computes_to (compose _ format1 format2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (format1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (format2 ctx) (b, ctx')
                           -> length_ByteString b = n')
    -> length_ByteString b = n + n'.
Proof.
  unfold compose, Bind2; intros; computes_to_inv; injections.
  destruct v; destruct v0.
  rewrite length_ByteString_enqueue_ByteString; erewrite H0, H1; eauto.
Qed.

Lemma length_ByteString_composeChecksum :
  forall sz checksum_Valid format1 format2 b (ctx ctx' : CacheFormat) n n' ,
    computes_to (composeChecksum _ _ _ sz checksum_Valid format1 format2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (format1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (format2 ctx) (b, ctx')
                           -> length_ByteString b = n')
    -> length_ByteString b = n + n' + sz.
Proof.
  unfold composeChecksum, Bind2; intros; computes_to_inv; injections.
  destruct v; destruct v0.
  rewrite !length_ByteString_enqueue_ByteString; simpl.
  unfold format_checksum.
  erewrite AlignedAutomation.length_encode_word'; simpl; rewrite AlignedByteString.length_ByteString_id.
  erewrite H0, H1; eauto; omega.
Qed.

Lemma length_ByteString_composeIf :
  forall format1 format2 b (ctx ctx' : CacheFormat) n P,
    computes_to (composeIf _ _ _ P format1 format2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (format1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (format2 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> length_ByteString b = n.
Proof.
  unfold composeIf, Bind2; intros; computes_to_inv; injections.
  destruct v; simpl in *; eauto.
Qed.

Lemma length_ByteString_ret :
  forall b' b (ctx ctx' : CacheFormat),
    computes_to (ret (b', ctx)) (b, ctx')
    -> length_ByteString b = length_ByteString b'.
Proof.
  intros; computes_to_inv; injections; reflexivity.
Qed.

Lemma length_ByteString_unused_word
  : forall sz (b : ByteString) (ctx ctx' : CacheFormat),
    format_unused_word sz ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold format_unused_word, format_unused_word'; simpl.
  intros; computes_to_inv; injections.
  rewrite AlignedAutomation.length_encode_word'; simpl.
  rewrite AlignedByteString.length_ByteString_id.
  omega.
Qed.

Lemma length_ByteString_word
  : forall sz (w : word sz) (b : ByteString) (ctx ctx' : CacheFormat),
    WordOpt.format_word w ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold WordOpt.format_word; simpl.
  intros; computes_to_inv; injections.
  rewrite AlignedAutomation.length_encode_word'.
  simpl; rewrite AlignedByteString.length_ByteString_id; omega.
Qed.

Lemma length_ByteString_bool
  : forall (b' : bool) (b : ByteString) (ctx ctx' : CacheFormat),
    format_bool b' ctx ↝ (b, ctx')
    -> length_ByteString b = 1.
Proof.
  intros; eapply AlignedAutomation.length_ByteString_bool; eauto.
Qed.

Lemma length_ByteString_format_list {A}
  : forall format_A l (b : ByteString) (ctx ctx' : CacheFormat) n,
    (forall (a : A) (b : ByteString) (ctx ctx' : CacheFormat),
        computes_to (format_A a ctx) (b, ctx')
        -> length_ByteString b = n)
    -> format_list format_A l ctx ↝ (b, ctx')
    -> length_ByteString b = (length l) * n.
Proof.
  induction l; simpl; intros; computes_to_inv.
  - injections; reflexivity.
  - unfold Bind2 in H0; computes_to_inv; injections.
    destruct v; destruct v0; simpl in *.
    erewrite length_ByteString_enqueue_ByteString.
    erewrite H; eauto.
    rewrite Mult.mult_succ_l.
    erewrite <- IHl; eauto with arith.
Qed.

Lemma ByteString_enqueue_padding_eq
  : forall a b,
    padding (ByteString_enqueue a b) =
    NPeano.modulo (S (padding b)) 8.
Proof.
  intros.
Admitted.

Lemma queue_into_ByteString_padding_eq
  : forall l,
    padding (queue_into_ByteString l) = NPeano.modulo (length l) 8.
Proof.
Admitted.

Lemma ByteString_enqueue_ByteString_padding_eq
  : forall b b',
    padding (ByteString_enqueue_ByteString b b') = NPeano.modulo (padding b + padding b') 8.
Proof.
  Admitted.

Definition length_ByteString_ByteString_id
  : length_ByteString ByteString_id = 0 := eq_refl.

Lemma length_ByteString_format_option {A}
  : forall format_Some format_None a_opt
           (b : ByteString) (ctx ctx' : CacheFormat) n,
    (forall (a : A) (b : ByteString) (ctx ctx' : CacheFormat),
        computes_to (format_Some a ctx) (b, ctx')
        -> length_ByteString b = n)
    -> (forall (b : ByteString) (ctx ctx' : CacheFormat),
           computes_to (format_None () ctx) (b, ctx')
           -> length_ByteString b = n)
    -> Option.format_option format_Some format_None a_opt ctx ↝ (b, ctx')
    -> length_ByteString b = n.
Proof.
  destruct a_opt; simpl; intros; computes_to_inv.
  - eapply H; eauto.
  - eauto.
Qed.

Ltac calculate_length_ByteString :=
  intros;
   match goal with
   | H:_ ↝ _
     |- _ =>
         (first
          [ eapply (length_ByteString_composeChecksum _ _ _ _ _ _ _ _ _ H);
             try (simpl mempty; rewrite length_ByteString_ByteString_id)
          | eapply (length_ByteString_composeIf _ _ _ _ _ _ _ H);
             try (simpl mempty; rewrite length_ByteString_ByteString_id)
          | eapply (length_ByteString_compose _ _ _ _ _ _ _ H);
             try (simpl mempty; rewrite length_ByteString_ByteString_id)
          | eapply (fun H' H'' => length_ByteString_format_option _ _ _ _ _ _ _ H' H'' H)
          | eapply (length_ByteString_unused_word _ _ _ _ H)
          | eapply (length_ByteString_bool _ _ _ _ H)
          | eapply (length_ByteString_word _ _ _ _ _ H)
          | eapply (fun H' => length_ByteString_format_list _ _ _ _ _ _ H' H)
          | eapply (length_ByteString_ret _ _ _ _ H) ]);
          clear H
   end.


  Lemma AlignedDecode_Throw {A}
    : DecodeMEquivAlignedDecodeM (fun (_ : ByteString) (_ : CacheDecode) => None)
                                 (fun sz : nat => ThrowAlignedDecodeM (A := A)).
  Proof.
    unfold DecodeMEquivAlignedDecodeM; intuition; try discriminate.
  Qed.
  
  Lemma AlignedDecode_ifb {A : Type}
        (decode_A : DecodeM A ByteString)
        (cond : bool)
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM
        decode_A
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
        (fun bs cd => if cond
                      then decode_A bs cd
                      else None)
        (fun sz => if cond
                   then aligned_decoder sz
                   else ThrowAlignedDecodeM).
  Proof.
    intros; destruct cond; simpl; eauto using AlignedDecode_Throw.
  Qed.

  Lemma AlignedDecode_Sumb {A : Type}
        (decode_A : DecodeM A ByteString)
        (P : Prop)
        (cond : {P} + {~P})
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM
        decode_A
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
        (fun bs cd => if cond
                      then decode_A bs cd
                      else None)
        (fun sz => if cond
                   then aligned_decoder sz
                   else ThrowAlignedDecodeM).
  Proof.
    intros; destruct cond; simpl; eauto using AlignedDecode_Throw.
  Qed.

  Definition SkipCurrentByte (* Gets the current byte and increments the current index. *)
             {n : nat}
    : AlignedDecodeM () n :=
    fun v idx c => Ifopt (nth_opt v idx) as b Then Some ((), S idx, addD c 8) Else None.

  Lemma AlignedDecodeUnusedCharM
    : DecodeMEquivAlignedDecodeM
           (decode_unused_word (monoidUnit := ByteString_QueueMonoidOpt) 8)
           (fun numBytes => SkipCurrentByte).
  Proof.
    unfold DecodeMEquivAlignedDecodeM, BindAlignedDecodeM, DecodeBindOpt2, BindOpt; intros;
      unfold decode_unused_word, decode_unused_word'.
    split; [ | split ]; intros.
    - pattern numBytes_hd, v; eapply Vector.caseS; simpl; intros.
      unfold SkipCurrentByte; simpl.
      destruct (nth_opt t n); simpl; eauto.
  Admitted.

  Lemma AlignedDecodeBindCharM' {A C : Type}
        (t : word 8 -> DecodeM C ByteString)
        (t' : word 8 -> forall {numBytes}, AlignedDecodeM C numBytes)
        decode_w
    : (forall v cd,
          decode_word (monoidUnit := ByteString_QueueMonoidOpt) (sz := 8) v cd
          = decode_w v cd)
      -> (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))        
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_w v cd;
                          t a b0 cd')
           (fun numBytes => b <- GetCurrentByte; t' b)%AlignedDecodeM.
  Proof.
    intros; eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; eauto.
    apply AlignedDecodeCharM.
    simpl. intros; eapply AlignedDecodeMEquiv_refl.
  Qed.


  Lemma AlignedDecode_assoc {A B C : Type}
        (decode_A : DecodeM A ByteString)
        (decode_B : A -> DecodeM B ByteString)
        (decode_C : A -> B -> DecodeM C ByteString)
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM
        (fun bs cd => `(ab, bs', cd') <- (`(a, bs', cd') <- decode_A bs cd;
                                            `(b, bs', cd') <- decode_B a bs' cd';
                                            Some (a, b, bs', cd'));
                      decode_C (fst ab) (snd ab) bs' cd')
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => `(a, bs', cd') <- decode_A bs cd;
                           `(b, bs', cd') <- decode_B a bs' cd';
                           decode_C a b bs' cd')
           aligned_decoder.
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans; eauto;
      intros; simpl; try reflexivity.
    simpl; destruct (decode_A b cd) as [ [ [? ?] ?] | ]; simpl; eauto.
    destruct (decode_B a b0 c) as [ [ [? ?] ?] | ]; simpl; eauto.
  Qed.
  
  Lemma AlignedDecodeBindUnusedCharM {C : Type}
        (t : unit -> DecodeM C ByteString)
        (t' : unit -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (DecodeMEquivAlignedDecodeM (t ()) (@t' ()))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_unused_word (monoidUnit := ByteString_QueueMonoidOpt) 8 v cd;
                          t a b0 cd')
           (fun numBytes => b <- SkipCurrentByte; @t' b numBytes)%AlignedDecodeM.
  Proof.
    intro; eapply Bind_DecodeMEquivAlignedDecodeM; eauto using AlignedDecodeUnusedCharM.
    intro; destruct a; eauto.
  Qed.
  Arguments wordToNat : simpl never.  

Definition EthernetHeader_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.

  unfold IPv4_Packet_Format.
  eapply CorrectAlignedDecoderForIPChecksumThenC.
  cbv beta; unfold Domain; simpl; repeat calculate_length_ByteString.
  unfold IPv4_Packet_OK.
  Arguments plus : simpl never.
  start_synthesizing_decoder.
  normalize_compose AlignedByteString.ByteStringQueueMonoid.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  admit.
  repeat decode_step idtac.
  repeat decode_step idtac.
  cbv beta; synthesize_cache_invariant.
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply @AlignedDecode_CollapseWord; eauto.
  eapply @AlignedDecodeBindCharM; intros.
  intros; apply @AlignedDecode_Sumb.  
  eapply @AlignedDecodeBindUnusedCharM; simpl.
  eapply DecodeMEquivAlignedDecodeM_trans.
  2: intros; reflexivity.
  eapply @AlignedDecodeBind2CharM; intros; eauto.
  eapply @AlignedDecodeBind2CharM; intros; eauto.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply AlignedDecode_assoc.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply AlignedDecode_assoc.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply AlignedDecode_assoc.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  
  
  setoid_rewrite <- @DecodeBindOpt2_assoc.
  Locate "`(".
  
  
  
  

  unfold monoid.
  eauto.

  cbv beta; align_decoders.

Defined.

Definition IPv4_decoder_impl :=
  Eval simpl in (fst (proj1_sig EthernetHeader_decoder)).

Definition pkt' : list char :=
  [WO~1~0~1~0~0~0~1~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~1~1~0~0~1~0~0;
   WO~1~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~1~1;
   WO~0~0~0~1~0~1~0~1;

   WO~0~1~1~1~1~0~1~1;
   WO~0~1~0~1~0~0~0~0;

   WO~0~0~0~0~0~0~1~1;
   WO~0~0~0~1~0~1~0~1;

   WO~0~1~1~1~1~0~1~1;
   WO~1~0~0~0~0~0~0~0]%list.

Definition pkt : list char :=
    Eval compute in map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0].

Compute (InternetChecksum.checksum pkt).

Definition address : list char :=
  Eval compute in map (@natToWord 8) [172;16;254;1].

Lemma zero_lt_eight : (lt 0 8)%nat.
Proof. omega. Qed.

Definition fiat_ipv4_decode (buffer: list char) : option (IPv4_Packet * list char) :=
  let bs := {| padding := 0; front := WO; paddingOK := zero_lt_eight; byteString := buffer |} in
  match IPv4_decoder_impl bs () with
  | Some (pkt', bs, _) => Some (pkt', bs.(byteString))
  | None => None
  end.

Compute (fiat_ipv4_decode pkt).

Compute (InternetChecksum.checksum pkt).
