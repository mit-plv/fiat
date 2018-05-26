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
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore.

Require Import Bedrock.Word.

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
  eexists _, (_, _).
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
