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
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Stores.EmptyStore.

Require Import Bedrock.Word.

Definition decode_IPChecksum
  : ByteString -> CacheDecode -> option (() * ByteString * CacheDecode) :=
  decode_unused_word (sz := 16).

Definition encode_word {sz} (w : word sz) : ByteString :=
  encode_word' sz w ByteString_id.

Definition IPChecksum (b b' : ByteString) : ByteString :=
  let b'' := if Peano_dec.eq_nat_dec (padding b) 0 then mempty
             else encode_word (wzero (8 - (padding b))) in
  mappend b''
          (encode_word (wnot (onesComplement
                                (ByteString2ListOfChar (bin_measure (mappend b b')) (BoundedByteStringToByteString(mappend b b')))))).

Fixpoint Vector_checksum_bound n {sz} (bytes :Vector.t (word 8) sz) acc : InternetChecksum.W16 :=
  match n, bytes with
  | 0, _ => acc
  | _, Vector.nil => acc
  | S 0, Vector.cons x _ _ => InternetChecksum.add_bytes_into_checksum x (wzero _) acc
  | _, Vector.cons x _ Vector.nil => InternetChecksum.add_bytes_into_checksum x (wzero _) acc
  | S (S n'), Vector.cons x _ (Vector.cons y _ t) =>
    (Vector_checksum_bound n' t (InternetChecksum.add_bytes_into_checksum x y acc))
  end.

Definition Vector_checksum_bound' n {sz} (bytes : Vector.t (word 8) sz) : InternetChecksum.W16 :=
  InternetChecksum.Vector_fold_left_pair InternetChecksum.add_bytes_into_checksum n bytes (wzero _) (wzero _).

Lemma Vector_checksum_bound'_ok' :
  forall n {sz} (bytes :Vector.t (word 8) sz) acc,
    Vector_checksum_bound n bytes acc =
    InternetChecksum.Vector_fold_left_pair InternetChecksum.add_bytes_into_checksum n bytes acc (wzero _).
Proof.
  fix IH 3.
  destruct bytes as [ | hd sz [ | hd' sz' tl ] ]; intros; simpl.
  - destruct n as [ | [ | ] ]; reflexivity.
  - destruct n as [ | [ | ] ]; reflexivity.
  - destruct n as [ | [ | ] ]; simpl; try reflexivity.
    rewrite IH; reflexivity.
Qed.

Lemma Vector_checksum_bound'_ok :
  forall n {sz} (bytes :Vector.t (word 8) sz),
    Vector_checksum_bound n bytes (wzero _) = Vector_checksum_bound' n bytes.
Proof.
  intros; apply Vector_checksum_bound'_ok'.
Qed.

Definition IPChecksum_Valid_dec (n : nat) (b : ByteString)
  : {IPChecksum_Valid' n b} + {~IPChecksum_Valid' n b} := weq _ _.

Definition calculate_IPChecksum {S} {sz}
  : AlignedEncodeM (S := S) sz :=
  (fun v =>
     (let checksum := InternetChecksum.Vector_checksum' v in
      (fun v idx s => SetByteAt (n := sz) 10 v 0 (wnot (split2 8 8 checksum)) ) >>
      (fun v idx s => SetByteAt (n := sz) 11 v 0 (wnot (split1 8 8 checksum)))) v)%AlignedEncodeM.

  Lemma CorrectAlignedEncoderForIPChecksumThenC
        {S}
        (format_A format_B : FormatM S ByteString)
        (encode_A : forall sz, AlignedEncodeM sz)
        (encode_B : forall sz, AlignedEncodeM sz)
        (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
        (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
    : CorrectAlignedEncoder
        (format_B ThenChecksum IPChecksum_Valid' OfSize 16 ThenCarryOn format_A)
        (fun sz => encode_B sz >>
                   (fun v idx s => SetCurrentByte v idx (wzero 8)) >>
                   (fun v idx s => SetCurrentByte v idx (wzero 8)) >>
                   encode_A sz >>
                   calculate_IPChecksum)% AlignedEncodeM.
  Proof.
  Admitted.

Lemma CorrectAlignedDecoderForIPChecksumThenC {A}
      predicate
      (format_A format_B : FormatM A ByteString)
      (len_format_A : A -> nat)
      (len_format_A_OK : forall a' b ctx ctx',
          computes_to (format_A a' ctx) (b, ctx')
          -> length_ByteString b = len_format_A a')
  : CorrectAlignedDecoderFor
      predicate
      (format_A ++ format_unused_word 16 ++ format_B)%format
    -> CorrectAlignedDecoderFor
         predicate
         (format_A ThenChecksum IPChecksum_Valid' OfSize 16 ThenCarryOn format_B).
Proof.
  intros H; destruct H as [ ? [ [? ?] [ ? ?] ] ]; simpl in *.
  eexists (fun sz v => if weq (Vector_checksum_bound' 20 v) (wones 16) then x sz v  else ThrowAlignedDecodeM v).
  admit.
Defined.

Definition Pseudo_Checksum_Valid
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : Vector.t (word 8) 2)
           (protoCode : word 8)
           (n : nat)
           (b : ByteString)
  := onesComplement (wzero 8 :: protoCode ::
                                      (ByteString2ListOfChar (96 + n) (BoundedByteStringToByteString b))
                                      ++ to_list srcAddr ++ to_list destAddr ++ to_list udpLength)%list
     = wones 16.

Definition calculate_PseudoChecksum {S} {sz}
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : Vector.t (word 8) 2)
           (protoCode : word 8)
           (idx' : nat)
  : AlignedEncodeM (S := S) sz :=
  (fun v =>
     (let checksum := InternetChecksum.Vector_checksum' (Vector.cons _ (wzero 8) _ (Vector.cons _ protoCode _
                                                          (append v (append srcAddr (append destAddr udpLength))))) in
      (fun v idx s => SetByteAt (n := sz) idx' v 0 (wnot (split2 8 8 checksum)) ) >>
      (fun v idx s => SetByteAt (n := sz) (1 + idx') v 0 (wnot (split1 8 8 checksum)))) v)%AlignedEncodeM.

Lemma CorrectAlignedEncoderForPseudoChecksumThenC
      {S}
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : Vector.t (word 8) 2)
      (protoCode : word 8)
      (idx : nat)
      (format_A format_B : FormatM S ByteString)
      (encode_A : forall sz, AlignedEncodeM sz)
      (encode_B : forall sz, AlignedEncodeM sz)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
      (idxOK : forall (s : S) (b : ByteString) (env env' : CacheFormat),
          format_B s env ∋ (b, env') -> length_ByteString b = idx)
  : CorrectAlignedEncoder
      (format_B ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode) OfSize 16 ThenCarryOn format_A)
      (fun sz => encode_B sz >>
                          (fun v idx s => SetCurrentByte v idx (wzero 8)) >>
                          (fun v idx s => SetCurrentByte v idx (wzero 8)) >>
                          encode_A sz >>
                          calculate_PseudoChecksum srcAddr destAddr udpLength protoCode (NPeano.div idx 8))% AlignedEncodeM.
Proof.
  admit.
Defined.

Lemma CorrectAlignedDecoderForUDPChecksumThenC {A}
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : Vector.t (word 8) 2)
      protoCode
      predicate
      (format_A format_B : FormatM A ByteString)
      (len_format_A : A -> nat)
      (len_format_A_OK : forall a' b ctx ctx',
          computes_to (format_A a' ctx) (b, ctx')
          -> length_ByteString b = len_format_A a')
  : CorrectAlignedDecoderFor
      predicate
      (format_A ++ format_unused_word 16 ++ format_B)%format
    -> CorrectAlignedDecoderFor
         predicate
         (format_A ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode) OfSize 16 ThenCarryOn format_B).
Proof.
  intros H; destruct H as [ ? [ [? ?] [ ? ?] ] ]; simpl in *.
  eexists (fun sz v => if weq (Vector_checksum_bound' (96 + sz * 8)
                                                     (Vector.cons _ (wzero 8) _ (Vector.cons _ protoCode _
                                                                      (append v (append srcAddr (append destAddr udpLength)))))) (wones 16)
                                                     
                       then x sz v  else ThrowAlignedDecodeM v).
  admit.
Defined.
