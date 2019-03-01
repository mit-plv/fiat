Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.Option
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.InternetChecksum
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.BaseFormats.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Definition onesComplement (chars : list char) : word 16 :=
  InternetChecksum.checksum chars.

Fixpoint append_bit {sz} (b : bool) (w : word sz) : word (S sz) :=
  match sz return word sz -> word (S sz) with
  | 0 => fun _ => WS b WO
  | S n' => fun w => WS (whd w) (append_bit b (wtl w))
  end w.

Fixpoint monoid_dequeue_word {B}
         {monoid : Monoid B}
         {monoid_opt : QueueMonoidOpt monoid bool}
         (sz : nat)
         (b : B)
  : (word sz * B) :=
  match sz with
  | 0 => (WO, b)
  | S sz' =>
    match dequeue_opt b with
    | Some (v, b') =>
      let (w', b'') := monoid_dequeue_word sz' b' in
      (append_bit v w', b'')
    | _ => (wzero (S sz'), b)
    end
  end.

Lemma monoid_dequeue_empty
  : forall sz,
    monoid_dequeue_word sz mempty = (wzero _, mempty).
Proof.
  simpl; unfold ByteString_id; induction sz; reflexivity.
Qed.

Lemma ByteString_dequeue_mappend_opt
  : forall (t : bool) (b b' b'' : ByteString),
    ByteString_dequeue b = Some (t, b') ->
    ByteString_dequeue (ByteString_enqueue_ByteString b b'') = Some (t, ByteString_enqueue_ByteString b' b'').
Proof.
  intros ? ? ? ? ;
    rewrite (ByteString_into_queue_eq b),
    (ByteString_into_queue_eq b'),
    (ByteString_into_queue_eq b'').
  rewrite !ByteString_enqueue_ByteString_into_BitString.
  rewrite !ByteString_dequeue_into_BitString.
  destruct (ByteString_into_queue b) eqn : ?; intros; try discriminate;
    injections.
  simpl.
  rewrite <- !ByteString_enqueue_ByteString_into_BitString.
  rewrite H0; reflexivity.
Qed.

Lemma monoid_dequeue_enqueue_word
  : forall (w : word (0 + 1 * 8)) (ext : ByteString) OK,
    monoid_dequeue_word _ (ByteString_enqueue_ByteString (ByteStringToBoundedByteString (word_into_ByteString OK w)) ext) = (w, ext).
Proof.
  simpl; intros; shatter_word w.
  unfold word_into_ByteString; simpl.
  do 8 match goal with
         |- context [ByteString_dequeue (ByteString_enqueue_ByteString ?z _)] =>
         let H := fresh in
         destruct (ByteString_dequeue z) as [ [? ?] | ] eqn:H;
           unfold ByteString_dequeue in H; simpl in H;
             [ erewrite ByteString_dequeue_mappend_opt; try eassumption;
               injections | discriminate ];
             match goal with
               |- context [ {| padding := _;
                               front := _;
                               paddingOK := ?H;
                               byteString := _ |} ] =>
               generalize H; intros; simpl
             end
       end.
  repeat f_equal.
  pose proof (mempty_left ext) as H7; simpl in H7; rewrite <- H7 at -1.
  unfold ByteString_id; repeat f_equal.
  apply le_uniqueness_proof.
Qed.

Fixpoint ByteString2ListOfChar (n : nat)
         (b : ByteString) : list char :=
  match n with
  | 0 => nil
  | S (S (S (S (S (S (S (S n'))))))) =>
    let (c, b') := monoid_dequeue_word 8 b in
    cons c (ByteString2ListOfChar n' b')
  | S n' =>
    let (c, b') := monoid_dequeue_word 8 b in
    cons c (ByteString2ListOfChar n' b')
  end.

Lemma ByteString2ListOfChar_push_char
  : forall n c b PaddingOK,
    ByteString2ListOfChar
      (8 + n)
      (ByteString_enqueue_ByteString {| front := WO;
                                        paddingOK := PaddingOK;
                                        byteString := [c] |}
                                     b) = (c :: (ByteString2ListOfChar n b))%list.
Proof.
  Local Opaque monoid_dequeue_word.
  intros.
  simpl.
  replace {| padding := 0; front := WO; paddingOK := PaddingOK; byteString := [c] |} with (ByteStringToBoundedByteString (word_into_ByteString PaddingOK (c : word (0 + 1 * 8)))).
  rewrite monoid_dequeue_enqueue_word.
  reflexivity.
  unfold char in c; shatter_word c.
  reflexivity.
Qed.

Lemma ByteBuffer_to_list_append
  : forall sz1 l1 sz2 l2,
    ByteBuffer.to_list (l1 ++ l2)%vector =
    (ByteBuffer.to_list (n := sz1) l1 ++ ByteBuffer.to_list (n := sz2) l2)%list.
Proof.
  induction l1.
  - reflexivity.
  - intros; simpl; rewrite <- IHl1.
    reflexivity.
Qed.

Lemma ByteString2ListOfChar_eq
  : forall (b ext : ByteString),
    padding b = 0 ->
    ByteString2ListOfChar (bin_measure b) (mappend b ext) =
    Core.byteString (BoundedByteStringToByteString b).
Proof.
  simpl; intros.
  destruct b; simpl in *; subst.
  unfold length_ByteString; simpl padding; rewrite plus_O_n.
  simpl Core.byteString.
  revert front paddingOK; induction byteString; intros.
  - reflexivity.
  - simpl numBytes in *.
    rewrite Mult.mult_succ_r, NPeano.Nat.add_comm.
    rewrite Mult.mult_comm.
    do 8 rewrite plus_Sn_m.
    rewrite plus_O_n.
    symmetry.
    unfold ByteBuffer.to_list, to_list in *; simpl.
    rewrite <- (IHbyteString WO paddingOK) at 1.
    replace (ByteString_enqueue_ByteString {| padding := 0; front := front; paddingOK := paddingOK; byteString := h :: byteString |} ext)
    with
      (ByteString_enqueue_ByteString
         (ByteStringToBoundedByteString (word_into_ByteString (m := 1) paddingOK h)) (ByteString_enqueue_ByteString {| padding := 0; front := front; paddingOK := paddingOK; byteString := byteString |} ext) ).
    rewrite (fun ext => monoid_dequeue_enqueue_word h ext paddingOK).
    rewrite mult_comm; shatter_word front; reflexivity.
    rewrite ByteString_enqueue_ByteString_assoc.
    f_equal.
    shatter_word front.
    unfold char in h; shatter_word h.
    unfold word_into_ByteString; simpl.
    unfold ByteStringToBoundedByteString, ByteBuffer.of_list, of_list; simpl.
    unfold ByteString_enqueue_ByteString; simpl.
    match goal with
      |- context [ ?w :: byteString] =>
      generalize w
    end.
    intros.
    assert (forall byteString m (l : ByteBuffer.t m), ByteBuffer.fold_left ByteString_enqueue_char
    {| padding := 0; front := WO; paddingOK := paddingOK; numBytes := m; byteString := l |} byteString =
  {| padding := 0; front := WO; paddingOK := paddingOK; numBytes := m + n; byteString := Vector.append l byteString |}).
    { clear; induction byteString.
      - simpl; intros; rewrite Vector_append_nil_r'.
        revert l; rewrite (plus_n_O m); simpl; reflexivity.
      - simpl; intros.
        assert (m + 1 + n = m + (1 + n)) by omega.
        pose proof (Vector_append_assoc _ _ _ H l [h] byteString)%vector.
        simpl in H0; rewrite H0; clear H0.
        revert H.
        simpl.
        replace (ByteString_enqueue_char {| padding := 0; front := WO; paddingOK := paddingOK; numBytes := m; byteString := l |} h)
          with {| padding := 0; front := WO; paddingOK := paddingOK; numBytes := m + 1; byteString := l ++ [h]|}%vector.
        generalize (l ++ [h])%vector.
        rewrite (plus_comm m 1).
        simpl.
        rewrite <- (plus_n_Sm m n).
        intros.
        destruct H; simpl.
        apply IHbyteString.
        unfold char in h; shatter_word h.
        unfold ByteString_enqueue_char.
        rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq
                {| padding := 0; front := WO; paddingOK := paddingOK; numBytes := m; byteString := l |}).
        rewrite <- ByteStringToBoundedByteString_enqueue_word.
        simpl.
        Local Transparent Core.ByteString_enqueue_word.
        simpl.
        unfold Core.ByteString_enqueue at 6.
        simpl.
        unfold Core.ByteString_enqueue at 5.
        simpl.
        unfold Core.ByteString_enqueue at 4.
        simpl.
        unfold Core.ByteString_enqueue at 3.
        simpl.
        unfold Core.ByteString_enqueue at 2.
        simpl.
        unfold Core.ByteString_enqueue at 1.
        simpl.
        rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq
                      {| padding := 0; front := WO; paddingOK := paddingOK; numBytes := m + 1; byteString := l ++ _ |})%vector.
        f_equal.
        unfold BoundedByteStringToByteString.
        simpl.
        f_equal.
        apply le_uniqueness_proof.
        unfold eq_rec_r; simpl.
        rewrite (ByteBuffer_to_list_append _ l _ [_]); reflexivity.
    }
    apply H7.
Qed.

Corollary ByteString2ListOfChar_eq'
  : forall (b : ByteString),
    padding b = 0 ->
    ByteString2ListOfChar (bin_measure b) b =
    Core.byteString (BoundedByteStringToByteString b).
Proof.
  intros.
  erewrite <- ByteString2ListOfChar_eq with (ext := mempty); auto.
Qed.

Definition monoid : Monoid ByteString :=
  ByteStringQueueMonoid.

Lemma onesComplement_commute :
  forall b b',
    (exists n, length b = 2 * n)
    -> (exists n, length b' = 2 * n)
    -> onesComplement (b ++ b') = onesComplement (b' ++ b).
Proof.
  intros; unfold onesComplement.
  eapply checksum_app; eauto.
Qed.

Definition encode_word {sz} (w : word sz) : ByteString :=
  encode_word' sz w ByteString_id.

Lemma length_encode_word' sz :
  forall (w : word sz) (b : ByteString),
    bin_measure (encode_word' _ w b) = sz + bin_measure b.
Proof.
  induction sz; intros;
    rewrite (shatter_word w); simpl.
  - reflexivity.
  - pose proof measure_enqueue as H'; simpl in H'.
    unfold encode_word in *; simpl in *.
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (ByteString_enqueue _ _)).
    rewrite length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite <- ByteString_enqueue_ByteStringToBoundedByteString_eq'.
    rewrite length_ByteString_enqueue.
    rewrite <- length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite ByteStringToBoundedByteString_BoundedByteStringToByteString_eq.
    erewrite <- IHsz.
    reflexivity.
Qed.

Lemma length_ByteString_id :
  length_ByteString ByteString_id = 0.
Proof.
  reflexivity.
Qed.

Corollary length_encode_word {sz} :
  forall (w : word sz),
    bin_measure (encode_word w) = sz.
Proof.
  unfold encode_word.
  intros; rewrite length_encode_word'.
  simpl; rewrite length_ByteString_id; omega.
Qed.

Definition IPChecksum (b b' : ByteString) : ByteString :=
  let b'' := if Peano_dec.eq_nat_dec (padding b) 0 then mempty
             else encode_word (wzero (8 - (padding b))) in
  mappend b''
            (encode_word (wnot (onesComplement
                                  (ByteString2ListOfChar (bin_measure (mappend b b')) (mappend b b'))))).

Lemma length_ByteString_IPChecksum
  : forall b b',
    padding b = 0
    -> length_ByteString (IPChecksum b b') = 16.
Proof.
  unfold IPChecksum; simpl; intros.
  rewrite length_ByteString_enqueue_ByteString.
  rewrite H; find_if_inside; try congruence.
  rewrite length_encode_word.
  rewrite length_ByteString_id; reflexivity.
Qed.

Lemma length_ByteString_into_BitString_measure :
  forall b,
| ByteString_into_BitString b | = bin_measure b.
Proof.
  simpl.
  intros; rewrite <- length_BitString_into_ByteString; f_equal.
  rewrite <- ByteString_into_BitString_eq; reflexivity.
Qed.

Lemma padding_eq_mod_8
  : forall b : ByteString, padding b = length_ByteString b mod 8.
Proof.
  intros; unfold length_ByteString.
  rewrite <- Nat.add_mod_idemp_r, mult_comm, NPeano.Nat.mod_mul, <- plus_n_O by omega.
  rewrite NPeano.Nat.mod_small; destruct b; eauto.
Qed.

Lemma ByteString_enqueue_padding_eq
  : forall a b,
    padding (ByteString_enqueue a b) =
    NPeano.modulo (S (padding b)) 8.
Proof.
  intros.
  rewrite padding_eq_mod_8.
  unfold length_ByteString.
  rewrite <- Nat.add_mod_idemp_r, mult_comm, NPeano.Nat.mod_mul, <- plus_n_O by omega.
  destruct b; simpl.
  destruct padding as [ | [ | [ | [ | [ | [ | [ | [ | ?] ] ] ] ] ] ] ]; try omega;
    shatter_word front; reflexivity.
Qed.

Lemma encode_word'_padding' :
  forall sz (w : word sz) bs,
    padding (encode_word' _ w bs) = NPeano.modulo (sz + padding bs) 8.
Proof.
  intros.
  rewrite <- padding_mod_8.
  revert bs; induction w; intros.
  - reflexivity.
  - simpl encode_word'.
    rewrite ByteString_enqueue_padding_eq.
    replace (S n + padding bs) with (1 + (n + padding bs)) by omega.
    rewrite <- Nat.add_mod_idemp_r by omega.
    rewrite <- IHw.
    rewrite !Nat.add_mod_idemp_r by omega.
    replace (S (padding (encode_word' n w bs))) with
        (1 + (padding (encode_word' n w bs))) by omega.
    rewrite <- Nat.add_mod_idemp_r at 1 by omega.
    rewrite NPeano.Nat.mod_mod by omega.
    rewrite Nat.add_mod_idemp_r by omega; reflexivity.
Qed.

Lemma encode_word'_padding :
  forall sz (w : word sz),
    padding (encode_word' _ w mempty) = NPeano.modulo sz 8.
Proof.
  intros.
  rewrite encode_word'_padding'.
  simpl padding.
  rewrite <- plus_n_O; reflexivity.
Qed.

Definition IPChecksum_Valid (n : nat) (b : ByteString) : Prop :=
  onesComplement (ByteString2ListOfChar n b) = wones 16.

Local Notation "x ++ y" := (mappend x y) : comp_scope.

Definition format_IP_Checksum
           {S}
           (format1 : FormatM S ByteString)
           (format2 : FormatM S ByteString)
           (a : S) (ctx : _)  :=
  (`(p, ctx) <- format1 a ctx;
    `(q, ctx) <- format2 a (addE ctx 16);
    c <- { c : word 16 | forall ext,
             IPChecksum_Valid (bin_measure (p ++ (encode_word c) ++ q))
                              (p ++ (encode_word c) ++ q ++ ext) };
    ret (p ++ (encode_word c) ++ q, ctx))%comp.

Definition IPChecksum_Valid_dec (n : nat) (b : ByteString)
  : {IPChecksum_Valid n b} + {~IPChecksum_Valid n b} := weq _ _.

Definition decode_IPChecksum
  : ByteString -> CacheDecode -> option (() * ByteString * CacheDecode) :=
  decode_unused_word (sz := 16).

Lemma ByteString2ListOfChar_Over :
  forall (b ext : ByteString),
    padding b = 0
    -> ByteString2ListOfChar (bin_measure b)
                             (mappend b ext) =
       ByteString2ListOfChar (bin_measure b) b.
Proof.
  intros; rewrite ByteString2ListOfChar_eq; eauto.
  intros; rewrite ByteString2ListOfChar_eq'; eauto.
Qed.

Lemma padding_eq_length
  : forall b,
    padding b = (bin_measure b) - (8 * (numBytes b)).
Proof.
  destruct b; simpl.
  unfold length_ByteString; simpl.
  omega.
Qed.

Definition IPv4_Packet_format_measure (ipv4_b : ByteString)
  : nat :=
  match (`(u, b') <- decode_unused_word' 4 ipv4_b;
           decode_word' 4 b') with
  | Some n => 32 * wordToNat (fst n)
  | None => 0
  end.

Lemma ByteString_pop_eq_push
  : forall b b' b'',
    ByteString_pop b = Some (b', b'')
    -> b = ByteString_push b' b''.
Proof.
  destruct b; unfold ByteString_pop; simpl.
  destruct padding; simpl.
  - destruct byteString; simpl; intros.
    + discriminate.
    + injections.
      unfold ByteString_push; simpl.
      f_equal.
      rewrite (shatter_word front); reflexivity.
      eapply le_uniqueness_proof.
      rewrite (shatter_word c); simpl; f_equal.
  - intros; rewrite (shatter_word front); injections.
    unfold ByteString_push; simpl.
    destruct (Peano_dec.eq_nat_dec padding 7).
    subst; elimtype False; omega.
    f_equal.
    eapply le_uniqueness_proof.
Qed.

Lemma SW_word_inj {sz}
  : forall b b' w w',
    SW_word b w = SW_word (sz := sz) b' w'
    -> b = b'.
Proof.
  induction w; intros; simpl in *.
  - shatter_word w'; simpl in *; injections; auto.
  - destruct (shatter_word_S w') as (?, (?, ?)); subst;
      simpl in *.
    injection H; intros; subst.
    eapply Eqdep_dec.inj_pair2_eq_dec in H0;
      eauto using Peano_dec.eq_nat_dec.
Qed.

Lemma SW_word_inj' {sz}
  : forall b b' w w',
    SW_word b w = SW_word (sz := sz) b' w'
    -> w = w'.
Proof.
  induction w; intros; simpl in *.
  - shatter_word w'; simpl in *; injections; auto.
  - destruct (shatter_word_S w') as (?, (?, ?)); subst;
      simpl in *.
    injection H; intros; subst.
    eapply Eqdep_dec.inj_pair2_eq_dec in H0;
      eauto using Peano_dec.eq_nat_dec.
    f_equal; eauto.
Qed.

Definition IPChecksum_ByteAligned (b : ByteString) :=
  padding b = 0 /\ exists n, numBytes b = 2 * n.

Lemma length_ByteString_IPChecksum_ByteAligned
  : forall b,
    NPeano.modulo (length_ByteString b) 16 = 0
    -> IPChecksum_ByteAligned b.
Proof.
  destruct b; unfold length_ByteString.
  unfold Core.padding, Core.byteString.
  intros; assert (padding = 0).
  rewrite NPeano.Nat.mod_mul_r with (b := 8) (c := 2) in H by eauto.
  apply Plus.plus_is_O in H; destruct H.
  apply Mult.mult_is_O in H0; destruct H0.
  congruence.
  rewrite Mult.mult_comm, NPeano.Nat.mod_add in H by eauto.
  destruct padding as [ | [ | [ | [ | [ | [ | [ | [ | [ ] ] ] ] ] ] ] ] ] ;
    eauto; simpl in H; try omega.
  unfold IPChecksum_ByteAligned; intuition eauto.
  subst; rewrite plus_O_n in H.
  eapply NPeano.Nat.mod_divides in H; eauto.
  destruct H.
  simpl.
  exists x.
  unfold AlignedByteString.numBytes in H.
  omega.
Qed.

Lemma IPChecksum_ByteAligned_length_ByteString
  : forall b,
    IPChecksum_ByteAligned b
    -> NPeano.modulo (length_ByteString b) 16 = 0.
Proof.
  destruct b; unfold length_ByteString.
  unfold AlignedByteString.padding, AlignedByteString.numBytes.
  intros; destruct H; simpl in H.
  rewrite H, plus_O_n.
  destruct_ex.
  simpl AlignedByteString.numBytes in H0.
  rewrite H0.
  rewrite Mult.mult_assoc.
  unfold mult at 2.
  simpl plus.
  rewrite Mult.mult_comm, NPeano.Nat.mod_mul; eauto.
Qed.

Lemma normalize_formatr_term {A}
  : forall (formatr formatr' : A -> CacheFormat -> Comp (_ * CacheFormat))
           (a : A)
           (ctx ctx' : CacheFormat)
           (b : ByteString),
    formatr a ctx ↝ (b, ctx')
    -> (forall a ctx, refineEquiv (formatr a ctx) (formatr' a ctx))
    -> formatr' a ctx ↝ (b, ctx').
Proof.
  intros; eapply H0; eauto.
Qed.

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
  rewrite length_ByteString_enqueue_ByteString.
  erewrite H0, H1; eauto.
Qed.

Lemma length_ByteString_composeChecksum {S} :
  forall (s : S) sz checksum_Valid format1 format2 b (ctx ctx' : CacheFormat) n n' ,
    computes_to (composeChecksum _ _ _ _ sz checksum_Valid _ format1 format2 s ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (format1 s ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (format2 s ctx) (b, ctx')
                           -> length_ByteString b = n')
    -> length_ByteString b = n + n' + sz.
Proof.
  unfold composeChecksum, Bind2; intros; computes_to_inv; injections.
  destruct v; destruct v0.
  rewrite !length_ByteString_enqueue_ByteString; simpl.
  unfold format_checksum.
  erewrite length_encode_word'; simpl; rewrite length_ByteString_id.
  erewrite H0, H1; eauto; omega.
Qed.

Lemma length_ByteString_composeIf {S} :
  forall format1 format2 b s (ctx ctx' : CacheFormat) n,
    computes_to (composeIf format1 format2 s ctx) (b, ctx')
    -> (forall (s : S) ctx b ctx', computes_to (format1 s ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall (s : S) ctx b ctx', computes_to (format2 s ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> length_ByteString b = n.
Proof.
  unfold composeIf, Union_Format, Bind2; intros; computes_to_inv; injections.
  rewrite unfold_computes in H; destruct_ex.
  revert H H0 H1; pattern x; apply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv; simpl.
  repeat apply IterateBoundedIndex.Build_prim_and; eauto.
Qed.

Transparent pow2.
Arguments pow2 : simpl never.

Lemma computes_to_compose_proj_decode_word {S}
  : forall s sz (f : S -> word sz) (ctx ctx'' : CacheFormat)
           (rest : CacheFormat -> Comp (ByteString * CacheFormat))
           (b : ByteString),
    computes_to ((((WordOpt.format_word ◦ f) s) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_word' sz (mappend b ext) = Some (f s, mappend b' ext).
Proof.
  unfold composeChecksum, compose, Bind2; intros; computes_to_inv; injections.
  eapply EquivFormat_Projection_Format in H.
  unfold format_word in *; computes_to_inv; subst.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  unfold decode_word'; intros.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof (monoid_dequeue_encode_word' (T := ByteString)) as H''; simpl in H''.
  intros; rewrite H''; reflexivity.
Qed.

Lemma computes_to_compose_proj_decode_nat {S}
  : forall s sz (f : S -> nat) (ctx ctx'' : CacheFormat)
           (rest : CacheFormat -> Comp (ByteString * CacheFormat))
           (b : ByteString),
    computes_to ((((format_nat sz ◦ f) s) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_word' sz (mappend b ext) = Some (natToWord _ (f s), mappend b' ext).
Proof.
  unfold composeChecksum, compose, Bind2; intros; computes_to_inv; injections.
  eapply EquivFormat_Projection_Format in H.
  unfold format_nat, format_word in *; computes_to_inv; subst.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  unfold decode_word'; intros.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof (monoid_dequeue_encode_word' (T := ByteString)) as H''; simpl in H''.
  intros; rewrite H''; reflexivity.
Qed.

Lemma computes_to_proj_decode_nat {S}
  : forall s sz (f : S -> nat) (ctx ctx'' : CacheFormat)
           (b : ByteString),
    computes_to ((((format_nat sz ◦ f) s)) ctx) (b, ctx'')
    -> forall ext,
        decode_word' sz (mappend b ext) = Some (natToWord _ (f s), ext).
Proof.
  unfold composeChecksum, compose, Bind2; intros; computes_to_inv; injections.
  eapply EquivFormat_Projection_Format in H.
  unfold format_nat, format_word in *; computes_to_inv; subst.
  simpl in *; repeat split; eauto.
  injections.
  unfold decode_word'; intros.
  pose proof (monoid_dequeue_encode_word' (T := ByteString)) as H''; simpl in H''.
  intros; rewrite H''; reflexivity.
Qed.

Lemma computes_to_compose_proj_decode_unused_word {S}
  : forall s sz (f : S -> word sz) (ctx ctx'' : CacheFormat)
           (rest : CacheFormat -> Comp (ByteString * CacheFormat))
           (b : ByteString),
    computes_to ((((WordOpt.format_word ◦ f) s) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_unused_word' sz (mappend b ext) = Some ((), mappend b' ext).
Proof.
  unfold composeChecksum, compose, Bind2; intros; computes_to_inv; injections.
  eapply EquivFormat_Projection_Format in H.
  unfold format_word in *; computes_to_inv; subst.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  unfold decode_unused_word'; intros.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof (monoid_dequeue_encode_word' (T := ByteString)) as H''; simpl in H''.
  intros; rewrite H''; reflexivity.
Qed.

Lemma computes_to_compose_decode_word
  : forall sz (w : word sz) (ctx ctx'' : CacheFormat)
           (rest : CacheFormat -> Comp (ByteString * CacheFormat))
           (b : ByteString),
    computes_to (((WordOpt.format_word w) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_word' sz (mappend b ext) = Some (w, mappend b' ext).
Proof.
  unfold composeChecksum, compose, Bind2, WordOpt.format_word; intros; computes_to_inv; injections.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  intros; rewrite <- monoid_dequeue_word_eq_decode_word'.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof (monoid_dequeue_encode_word' (T := ByteString)) as H''; simpl in H'';
    intros; rewrite H''; reflexivity.
Qed.

Lemma computes_to_compose_decode_unused_word
  : forall sz (w : word sz) (ctx ctx'' : CacheFormat)
           (rest : CacheFormat -> Comp (ByteString * CacheFormat))
           (b : ByteString),
    computes_to (((WordOpt.format_word w) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_unused_word' sz (mappend b ext) = Some ((), mappend b' ext).
Proof.
  unfold composeChecksum, compose, Bind2, WordOpt.format_word; intros; computes_to_inv; injections.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  unfold decode_unused_word'; intros.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof (monoid_dequeue_encode_word' (T := ByteString)) as H''; simpl in H'';
    intros; rewrite H''; reflexivity.
Qed.

Arguments mult : simpl never.
Arguments decode_word' : simpl never.

Lemma length_ByteString_ret :
  forall b' b (ctx ctx' : CacheFormat),
    computes_to (ret (b', ctx)) (b, ctx')
    -> length_ByteString b = length_ByteString b'.
Proof.
  intros; computes_to_inv; injections; reflexivity.
Qed.

Lemma length_ByteString_unused_word {S}
  : forall sz (s : S) (b : ByteString) (ctx ctx' : CacheFormat),
    format_unused_word sz s ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold format_unused_word; simpl.
  unfold FMapFormat.Compose_Format.
  intros; rewrite unfold_computes in H; destruct_ex; intuition.
  unfold format_word in H0; computes_to_inv; injections.
  rewrite length_encode_word'; simpl.
  rewrite length_ByteString_id.
  omega.
Qed.

Lemma length_ByteString_word
  : forall sz (w : word sz) (b : ByteString) (ctx ctx' : CacheFormat),
    WordOpt.format_word w ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold WordOpt.format_word; simpl.
  intros; computes_to_inv; injections.
  rewrite length_encode_word'.
  simpl; rewrite length_ByteString_id; omega.
Qed.

Lemma length_ByteString_bool
  : forall (b' : bool) (b : ByteString) (ctx ctx' : CacheFormat),
    format_bool b' ctx ↝ (b, ctx')
    -> length_ByteString b = 1.
Proof.
  unfold format_bool; simpl.
  intros; computes_to_inv; injections.
  reflexivity.
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


Lemma queue_into_ByteString_padding_eq
  : forall l,
    padding (queue_into_ByteString l) = NPeano.modulo (length l) 8.
Proof.
  intro; replace (length l) with (length l + bin_measure ByteString_id)
    by (simpl; rewrite length_ByteString_id; omega).
  unfold queue_into_ByteString; generalize ByteString_id.
  induction l; intros; simpl fold_left.
  - apply padding_eq_mod_8.
  - simpl fold_left.
    rewrite IHl.
    replace bin_measure with length_ByteString by reflexivity.
    rewrite <- NPeano.Nat.add_mod_idemp_r by omega.
    rewrite <- NPeano.Nat.add_mod_idemp_r with (b := length_ByteString _) by omega.
    rewrite <- !padding_eq_mod_8.
    rewrite ByteString_enqueue_padding_eq.
    rewrite NPeano.Nat.add_mod_idemp_r by omega.
    f_equal.
    simpl; omega.
Qed.

Lemma ByteString_enqueue_ByteString_padding_eq
  : forall b b',
    padding (ByteString_enqueue_ByteString b b') = NPeano.modulo (padding b + padding b') 8.
Proof.
  intros.
  rewrite (ByteString_into_queue_eq b),
  (ByteString_into_queue_eq b').
  rewrite ByteString_enqueue_ByteString_into_BitString.
  rewrite queue_into_ByteString_app.
  generalize (queue_into_ByteString (ByteString_into_queue b)).
  induction (ByteString_into_queue b'); intros; simpl fold_left.
  - rewrite <- NPeano.Nat.add_mod_idemp_r by omega.
    replace (padding (queue_into_ByteString []%list) mod 8) with 0 by reflexivity.
    rewrite NPeano.Nat.mod_small; destruct b0; simpl; eauto.
    omega.
  - rewrite IHb0.
    rewrite !queue_into_ByteString_padding_eq.
    rewrite !NPeano.Nat.add_mod_idemp_r by omega.
    rewrite ByteString_enqueue_padding_eq.
    rewrite plus_comm.
    rewrite !NPeano.Nat.add_mod_idemp_r by omega.
    f_equal; simpl length; omega.
Qed.

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
    -> format_option format_Some format_None a_opt ctx ↝ (b, ctx')
    -> length_ByteString b = n.
Proof.
  destruct a_opt; simpl; intros; computes_to_inv.
  - eapply H; eauto.
  - eauto.
Qed.

(* A (hopefully) more convenient IP_Checksum lemma *)
Lemma compose_IPChecksum_format_correct
  : forall (A : Type)
           (B := ByteString)
           (trans : Monoid B := monoid)
           (trans_opt : QueueMonoidOpt trans bool :=
              ByteString_QueueMonoidOpt)
           (calculate_checksum := IPChecksum)
           (checksum_Valid := IPChecksum_Valid)
           (checksum_Valid_dec := IPChecksum_Valid_dec)
           (P : CacheDecode -> Prop)
           (P_inv : (CacheDecode -> Prop) -> Prop)
           (decodeChecksum := decode_IPChecksum),
    cache_inv_Property P P_inv ->
    forall (predicate : A -> Prop)
           (format1 : A -> CacheFormat -> Comp (B * CacheFormat))
           (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
           (formatd_A_measure : B -> nat)
           (len_format1 : A -> nat)
           (len_format2 : A -> nat),
      (forall a' b ctx ctx',
          computes_to (format1 a' ctx) (b, ctx')
          -> length_ByteString b = len_format1 a')
      -> (forall a b ctx ctx',
             computes_to (format2 a ctx) (b, ctx')
             -> length_ByteString b = len_format2 a)
      -> (forall a, NPeano.modulo (len_format1 a) 8 = 0)
      -> (forall a, NPeano.modulo (len_format2 a) 8 = 0)
      -> (forall (a : A) (ctx ctx' ctx'' : CacheFormat) c (b b'' ext : B),
             format1 a ctx ↝ (b, ctx') ->
             format2 a ctx' ↝ (b'', ctx'') ->
             predicate a ->
             len_format1 a + len_format2 a + 16 = formatd_A_measure (mappend (mappend b (mappend (format_checksum _ _ _ 16 c) b'')) ext)) ->
      forall decodeA : B -> CacheDecode -> option (A * B * CacheDecode),
        (cache_inv_Property P P_inv ->
         CorrectDecoder monoid predicate predicate eq (format1 ++ format_unused_word 16 ++ format2)%format decodeA P (format1 ++ format_unused_word 16 ++ format2)%format) ->
        CorrectDecoder monoid predicate predicate eq
                       (format1 ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn format2)
                       (fun (bin : B) (env : CacheDecode) =>
                          if checksum_Valid_dec (formatd_A_measure bin) bin
                          then
                            decodeA bin env
                          else None) P
                       (format1 ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn format2).
Proof.
  intros.
  eapply composeChecksum_format_correct; eauto.
  - intros; rewrite !mappend_measure.
    simpl; rewrite (H0 _ _ _ _ H6).
    simpl; rewrite (H1 _ _ _ _ H7).
    erewrite <- H4; eauto; try omega.
    unfold format_checksum.
    rewrite length_encode_word'.
    simpl; omega.
  - unfold IPChecksum_Valid in *; intros; simpl.
    rewrite ByteString2ListOfChar_Over.
    * rewrite ByteString2ListOfChar_Over in H9.
      eauto.
      simpl.
      apply H0 in H7.
      pose proof (H2 data).
      rewrite <- H7 in H10.
      rewrite !ByteString_enqueue_ByteString_padding_eq.
      rewrite padding_eq_mod_8, H10.
      pose proof (H3 data).
      unfold format_checksum.
      rewrite encode_word'_padding.
      rewrite <- (H1 _ _ _ _ H8) in H11.
      rewrite padding_eq_mod_8, H11.
      reflexivity.
    * rewrite !ByteString_enqueue_ByteString_padding_eq.
      apply H0 in H7.
      pose proof (H2 data).
      rewrite <- H7 in H10.
      rewrite padding_eq_mod_8, H10.
      pose proof (H3 data).
      unfold format_checksum.
      rewrite encode_word'_padding.
      rewrite <- (H1 _ _ _ _ H8) in H11.
      rewrite padding_eq_mod_8, H11.
      reflexivity.
Qed.

Lemma injection_decode_correct' {S V V' T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (inj : V -> option V')
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (View'_Predicate : V' -> Prop)
      (format : FormatM S T)
      (view : S -> V -> Prop)
      (view' : S -> V' -> Prop)
      (view_format : FormatM V T)
      (view'_format : FormatM V' T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid Source_Predicate View_Predicate
                                    view format decode_V P view_format)
      (view'_OK : forall s v, Source_Predicate s -> view s v -> exists v', inj v = Some v' /\ view' s v')
      (View'_Predicate_OK : forall v, View_Predicate v
                                 -> forall v', inj v = Some v' -> View'_Predicate v')
      (view'_format_OK : forall v env t env' xenv' t',
          Equiv env env' ->
          P env' ->
          Equiv (snd t) xenv' ->
          decode_V (mappend (fst t) t') env' = Some (v, t', xenv') ->
          computes_to (view_format v env) t ->
          View_Predicate v
          -> forall v', inj v = Some v' -> computes_to (view'_format v' env) t )
  : CorrectDecoder monoid Source_Predicate View'_Predicate
                   view'
                   format (Compose_Decode' decode_V (fun s => match inj (fst s) with
                                                           | Some s' => Some (s', snd s)
                                                           | None => None
                                                           end))
                   P view'_format.
Proof.
  unfold CorrectDecoder, Projection_Format, Compose_Decode'; split; intros.
  { pose proof (proj2 decode_V_OK) as H'.
    apply proj1 in decode_V_OK; eapply decode_V_OK with (ext := ext) in H1; eauto.
    destruct_ex; intuition; subst; eauto.
    destruct (view'_OK s x); eauto. intuition.
    eexists _, _; intuition eauto. rewrite H2; simpl; eauto.
    rewrite H7; auto.
    eapply view'_format_OK; eauto.
    eapply H' in H2; eauto.
    split_and; destruct_ex; split_and; eauto.
  }
  { destruct (decode_V t env') as [ [ [? ?] ?] |] eqn: ? ;
      simpl in *; try discriminate; destruct inj eqn:?; try discriminate; injections.
    generalize Heqo; intros.
    apply proj2 in decode_V_OK;
      eapply decode_V_OK in Heqo; eauto.
    intuition; destruct_ex; split_and; eexists _, _; intuition eauto.
    subst.
    eapply view'_format_OK; eauto.
  }
Qed.

Lemma injection_decode_correct {S V V' T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (inj : V -> V')
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (View'_Predicate : V' -> Prop)
      (format : FormatM S T)
      (view : S -> V -> Prop)
      (view' : S -> V' -> Prop)
      (view_format : FormatM V T)
      (view'_format : FormatM V' T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid Source_Predicate View_Predicate
                                    view format decode_V P view_format)
      (view'_OK : forall s v, Source_Predicate s -> view s v -> view' s (inj v))
      (View'_Predicate_OK : forall v, View_Predicate v
                                      -> View'_Predicate (inj v))
      (view'_format_OK : forall v env t env' xenv' t',
          Equiv env env' ->
          P env' ->
          Equiv (snd t) xenv' ->
          decode_V (mappend (fst t) t') env' = Some (v, t', xenv') ->
          computes_to (view_format v env) t
          -> View_Predicate v
          -> computes_to (view'_format (inj v) env) t )
  : CorrectDecoder monoid Source_Predicate View'_Predicate
                   view'
                   format (Compose_Decode decode_V (fun s => (inj (fst s), snd s)))
                   P view'_format.
Proof.
  eapply (injection_decode_correct' (fun v => Some (inj v)));
    intuition eauto; injections; intuition eauto.
Qed.

(* A (hopefully) more convenient IP_Checksum lemma *)
Lemma compose_IPChecksum_format_correct'
  : forall (A : Type)
           (B := ByteString)
           (trans : Monoid B := monoid)
           (trans_opt : QueueMonoidOpt trans bool :=
              ByteString_QueueMonoidOpt)
           (calculate_checksum := IPChecksum)
           (checksum_Valid := IPChecksum_Valid)
           (checksum_Valid_dec := IPChecksum_Valid_dec)
           (P : CacheDecode -> Prop)
           (P_inv : (CacheDecode -> Prop) -> Prop)
           (P_invM : (CacheDecode -> Prop) -> Prop)
           (decodeChecksum := decode_IPChecksum),
    cache_inv_Property P (fun P => P_inv P /\ P_invM P) ->
    forall (predicate : A -> Prop)
           (format1 : FormatM A B)
           (format2 : FormatM A B)
           (subformat : FormatM A B)
           (format_measure : FormatM nat B)
           (decode_measure : DecodeM (nat * B) B)
           (len_format1 : A -> nat)
           (len_format2 : A -> nat)
           View_Predicate,
      (forall a' b ctx ctx',
          computes_to (format1 a' ctx) (b, ctx')
          -> length_ByteString b = len_format1 a')
      -> (forall a b ctx ctx',
             computes_to (format2 a ctx) (b, ctx')
             -> length_ByteString b = len_format2 a)
      -> (forall a, NPeano.modulo (len_format1 a) 8 = 0)
      -> (forall a, NPeano.modulo (len_format2 a) 8 = 0)
      -> forall decodeA : B -> CacheDecode -> option (A * B * CacheDecode),
        (cache_inv_Property P P_inv ->
         CorrectDecoder monoid predicate predicate eq (format1 ++ format_unused_word 16 ++ format2)%format decodeA P (format1 ++ format_unused_word 16 ++ format2)%format)
      -> (cache_inv_Property P P_invM ->
          CorrectRefinedDecoder monoid predicate View_Predicate
                                (fun a n => len_format1 a + 16 + len_format2 a = n * 8)
                                (format1 ++ format_unused_word 16 ++ format2)%format
                                subformat
                                decode_measure P
                                format_measure)%format
      -> (Prefix_Format _ (format1 ++ format_unused_word 16 ++ format2) subformat)%format
      -> CorrectDecoder monoid predicate predicate eq
                       (format1 ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn format2)
                       (fun (bin : B) (env : CacheDecode) =>
                          `(n, _, _) <- decode_measure bin env;
                            if checksum_Valid_dec (n * 8) bin then
                              decodeA bin env
                            else None) P
                       (format1 ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn format2).
Proof.
  intros.
  eapply format_decode_correct_alt.
  7: { eapply (composeChecksum_format_correct'
                 A _ monoid _ 16 IPChecksum_Valid).
       - eapply H.
       - rename H6 into H4'; rename H5 into H6; rename H4 into H5; rename H6 into H4.
           specialize (H4 (proj2 H)).
         split.
         2: eauto.
         eapply injection_decode_correct with (inj := fun n => mult n 8).
         4: simpl.
         eapply H4.
         + intros.
           instantiate (1 := fun a n => len_format1 a + 16 + len_format2 a = n).
           eapply H8.
         + intros; instantiate (1 := fun v => View_Predicate (Nat.div v 8)).
           cbv beta.
           rewrite Nat.div_mul; eauto.
         + intros; apply unfold_computes; intros.
           split.
           2: rewrite unfold_computes in H11; intuition.
           intros.
           rewrite unfold_computes in H11; intuition.
           instantiate (1 := fun v env t => format_measure (Nat.div v 8) env t).
           cbv beta; rewrite Nat.div_mul; eauto.
       - simpl; intros.
         destruct t1; destruct t2; simpl fst in *; simpl snd in *.
         apply unfold_computes in H8; apply unfold_computes in H9.
         erewrite H0; eauto.
         apply unfold_computes in H10; erewrite (H1 _ b0); eauto.
         unfold format_checksum; rewrite length_encode_word', measure_mempty.
         rewrite <- H7; omega.
       - eauto.
       - unfold IPChecksum_Valid in *; intros; simpl.
         rewrite ByteString2ListOfChar_Over.
         * rewrite ByteString2ListOfChar_Over in H10.
           eauto.
           simpl.
           apply H0 in H8.
           pose proof (H2 data).
           rewrite <- H8 in H11.
           rewrite !ByteString_enqueue_ByteString_padding_eq.
           rewrite padding_eq_mod_8, H11.
           pose proof (H3 data).
           unfold format_checksum.
           rewrite encode_word'_padding.
           rewrite <- (H1 _ _ _ _ H9) in H12.
           rewrite padding_eq_mod_8, H12.
           reflexivity.
         * rewrite !ByteString_enqueue_ByteString_padding_eq.
           apply H0 in H8.
           pose proof (H2 data).
           rewrite <- H8 in H11.
           rewrite padding_eq_mod_8, H11.
           pose proof (H3 data).
           unfold format_checksum.
           rewrite encode_word'_padding.
           rewrite <- (H1 _ _ _ _ H9) in H12.
           rewrite padding_eq_mod_8, H12.
           reflexivity. }
  all: try unfold flip, pointwise_relation, impl;
    intuition eauto using EquivFormat_reflexive.
  instantiate (1 := IPChecksum_Valid_dec).
  unfold Compose_Decode.
  destruct (decode_measure a a0) as [ [ [? ?] ? ] | ]; simpl; eauto.
Qed.

Lemma build_aligned_ByteString_nil
  :   build_aligned_ByteString [] = ByteString_id.
Proof.
  unfold build_aligned_ByteString, ByteString_id; simpl.
  f_equal.
  eapply le_uniqueness_proof.
Qed.

Lemma InternetChecksum_To_ByteBuffer_Checksum {sz}
  : forall m (v : Vector.t _ sz),
    InternetChecksum.checksum
      (ByteString2ListOfChar ((m * 2) * 8) (build_aligned_ByteString v))
    = InternetChecksum.ByteBuffer_checksum_bound (m * 2) v.
Proof.
  intros; rewrite <- ByteBuffer_checksum_bound_ok.
  revert sz v.
  induction m.
  - intros; reflexivity.
  - intros; simpl.
    destruct v.
    + simpl.
      rewrite build_aligned_ByteString_nil.
      rewrite monoid_dequeue_empty.
      destruct m.
      reflexivity.
      simpl.
      rewrite monoid_dequeue_empty.
      rewrite monoid_dequeue_empty.
      rewrite monoid_dequeue_empty.
      simpl; fold mult.
      assert (checksum (ByteString2ListOfChar (m * 2 * 8) ByteString_id) = wzero 16).
      { clear; induction m; simpl; eauto.
        fold mult.
        rewrite monoid_dequeue_empty.
        simpl; rewrite monoid_dequeue_empty.
        simpl; rewrite IHm.
        reflexivity. }
      rewrite !H.
      reflexivity.
    + pose proof (monoid_dequeue_enqueue_word h (build_aligned_ByteString v)) .
      pose proof (build_aligned_ByteString_append v [h]) as H'; simpl in H';
        rewrite H'; clear H'.
      assert (lt 0 8)%nat as OK by omega.
      replace (build_aligned_ByteString [h]) with
          (ByteStringToBoundedByteString (word_into_ByteString (m := 1) OK h)).
      rewrite H.
      destruct v.
      * simpl; rewrite build_aligned_ByteString_nil.
        rewrite monoid_dequeue_empty.
        fold mult.
        simpl.
        rewrite <- build_aligned_ByteString_nil.
        rewrite IHm.
        f_equal.
        destruct m; reflexivity.
      * pose proof (monoid_dequeue_enqueue_word h0 (build_aligned_ByteString v)) .
        pose proof (build_aligned_ByteString_append v [h0]) as H'; simpl in H';
          rewrite H'; clear H'.
        replace (build_aligned_ByteString [h0]) with
            (ByteStringToBoundedByteString (word_into_ByteString (m := 1) OK h0)).
        rewrite H0.
        simpl.
        fold mult.
        rewrite IHm.
        clear; generalize (wzero 16); revert h h0 n v.
        induction m; simpl; intros; eauto.
        destruct v; eauto.
        destruct v; eauto.
        rewrite add_bytes_into_checksum_swap; eauto.
        fold mult.
        rewrite add_bytes_into_checksum_swap.
        rewrite <- !IHm; reflexivity.
        unfold char in h0; shatter_word h0.
        clear; simpl.
        unfold word_into_ByteString, build_aligned_ByteString, ByteStringToBoundedByteString.
        simpl.
        f_equal.
        apply le_uniqueness_proof.
      * unfold char in h; shatter_word h.
        clear; simpl.
        unfold word_into_ByteString, build_aligned_ByteString, ByteStringToBoundedByteString.
        simpl.
        f_equal.
        apply le_uniqueness_proof.
Qed.

Ltac calculate_length_ByteString :=
  intros;
  match goal with
  | H : computes_to _ _ |- _ =>
    first [ eapply (length_ByteString_composeChecksum _ _ _ _ _ _ _ _ _ H);
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
          | eapply (length_ByteString_ret _ _ _ _ H) ]; clear H
  end.


Lemma plus_32_mod_8 :
  forall n, NPeano.modulo (32 + n) 8 = NPeano.modulo n 8.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
Qed.

Lemma mult_16_mod_8 :
  forall n n', NPeano.modulo (n' * 16 + n) 8 = NPeano.modulo n 8.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
  destruct (NPeano.Nat.mod_divides (n' * 16) 8); eauto.
  rewrite H0; eauto.
  eexists (2 * n'); omega.
Qed.

Lemma lt_minus_plus :
  forall n m o,
    lt n (o - m) -> lt (m + n) o.
Proof.
  intros; omega.
Qed.

Lemma lt_minus_minus :
  forall n' n m o,
    lt m o
    -> n' = n - m
    -> lt n o -> lt n' (o - m).
Proof.
  intros; omega.
Qed.

Lemma lt_8_2_16 : lt 8 (pow2 16).
Proof.
  rewrite <- Npow2_nat.
  rewrite Compare_dec.nat_compare_lt.
  rewrite <- (Nnat.Nat2N.id 8) at 1.
  rewrite <- Nnat.N2Nat.inj_compare.
  reflexivity.
Qed.

Lemma lt_minus_plus_idem :
  forall n m o,
    lt m o
    -> lt n o
    -> lt (m + (n - m)) o.
Proof.
  intros; omega.
Qed.

Lemma mult_32_mod_8 :
  forall n n', NPeano.modulo (n' * 32 + n) 8 = NPeano.modulo n 8.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
  pose proof (NPeano.Nat.mod_mul (4 * n') 8) as H'';
    rewrite <- Mult.mult_assoc, Mult.mult_comm, <- Mult.mult_assoc in H''.
  unfold mult at 2 in H''; simpl plus in H''.
  simpl rewrite H''; eauto.
Qed.

Lemma plus_16_mod_8 :
  forall n, NPeano.modulo (16 + n) 8 = NPeano.modulo n 8.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
Qed.

Lemma mult_8_mod_8 :
  forall n n', NPeano.modulo (n' * 8 + n) 8 = NPeano.modulo n 8.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
  rewrite NPeano.Nat.mod_mul; eauto.
Qed.

Lemma mult_8_mod_8': forall n' : nat, (8 * n') mod 8 = 0.
Proof.
  intros; rewrite mult_comm.
  rewrite Nat.mod_mul; omega.
Qed.

Lemma mult_32_mod_8'
  : forall n,  (n * 32) mod 8 = 0.
Proof.
  intros.
  pose proof (mult_32_mod_8 0 n);
    rewrite <- plus_n_O in H; eauto.
Qed.

Ltac solve_mod_8 :=
  intros; cbv beta; simpl mempty;
  repeat first [
           rewrite plus_32_mod_8
         | rewrite plus_16_mod_8
         | rewrite length_ByteString_ByteString_id
         | rewrite (NPeano.Nat.mod_mul _ 8 (NPeano.Nat.neq_succ_0 7))
         | rewrite mult_32_mod_8
         | rewrite mult_16_mod_8
         | rewrite mult_8_mod_8
         | rewrite mult_8_mod_8'
         | rewrite mult_32_mod_8'
         | rewrite <- plus_n_O
         | reflexivity ].

Lemma refineEquiv_ThenC_no_dep {B Env}
      {monoid : Monoid B}
  : forall (format1 : Env -> Comp (B * Env))
           {A}
           (format2 : A -> Env -> Comp (B * Env))
           {A'}
           (f : A -> A')
           (format2' format' : A' -> Env -> Comp (B * Env))
           (H : forall a env, refineEquiv (format2 a env) (format2' (f a) env))
           (H : forall a' env, format' a' env = (fun a' => format1 ThenC (format2' a')) a' env)
           (a : A)
           (env : Env),
    refineEquiv ((format1 ThenC (format2 a)) env)
                (format' (f a) env).
Proof.
  intros; unfold compose, Bind2; intros.
  setoid_rewrite H0.
  setoid_rewrite H; reflexivity.
Qed.

Lemma refineEquiv_ThenC {A B Env}
      {monoid : Monoid B}
  : forall (format1 : A -> Env -> Comp (B * Env))
           (format2 : A -> Env -> Comp (B * Env))
           {A' A''}
           (f : A -> A')
           (f' : A -> A'')
           (format1' : A' -> Env -> Comp (B * Env))
           (format2' : A'' -> Env -> Comp (B * Env))
           (format' : (A' * A'') -> Env -> Comp (B * Env))
           (H1 : forall a env,
               refineEquiv (format1 a env) (format1' (f a) env))
           (H2 : forall a env,
               refineEquiv (format2 a env) (format2' (f' a) env))
           (H' : forall aa' env,
               format' aa' env
               = (format1' (fst aa') ThenC (format2' (snd aa'))) env)
           (a : A)
           (env : Env),
    refineEquiv ((format1 a ThenC format2 a) env)
                (format' ((fun a => (f a, f' a)) a) env).
Proof.
  intros; unfold compose, Bind2; intros;
    setoid_rewrite H';
    setoid_rewrite H1; setoid_rewrite H2; reflexivity.
Qed.

Lemma refineEquiv_DoneC {A Env}
  : forall (a : A) (env : Env),
    refineEquiv (ret (ByteString_id, env))
                ((fun _ e => ret (ByteString_id, e))
                   ((fun _ => tt) a) env).
Proof.
  simpl; intros; higher_order_reflexivity.
Qed.

Ltac resolve_Checksum :=
  let a := fresh in
  let ctx := fresh in
  intros a ctx;
  match goal with
  | |- refineEquiv ((?format1 ThenC ?format2) ?ctx) ?z =>
    let format2' := (eval pattern a in format2) in
    match format2' with
    | ?format2'' a =>
      eapply (@refineEquiv_ThenC_no_dep _ _ _ format1 _ format2'');
      [ clear | higher_order_reflexivity ]
    end; cbv beta; clear
  | |- refineEquiv ((?format1 ThenC ?format2) ?ctx) ?z =>
    let format1' := (eval pattern a in format1) in
    let format2' := (eval pattern a in format2) in
    match format1' with
    | ?format1'' a =>
      match format2' with
      | ?format2'' a =>
        eapply (@refineEquiv_ThenC _ _ _ _ format1'' format2'');
        [unfold GetAttribute, GetAttributeRaw; simpl;
         try (intros; higher_order_reflexivity)
        | cbv beta; clear
        | higher_order_reflexivity]
      end
    end; cbv beta; clear
  | |- refineEquiv (ret (ByteString_id, ctx))
                   (?f (?proj a) ctx) =>
    let T := match type of a with ?A => A end in
    let T' := match type of ctx with ?A => A end in
    unify f (fun (_ : unit) (e : T') => ret (ByteString_id, e));
    unify proj (fun _ : T => tt);
    eapply (@refineEquiv_DoneC T T' a)
  end.

(*Ltac apply_IPChecksum Len_OK :=
  match goal with
    H : cache_inv_Property _ _
    |- context[
           CorrectDecoder  _ _ _
                                   (fun data c =>
                                      (_ ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn _) c) _ _] =>
    eapply compose_IPChecksum_format_correct';
    [apply H
    | repeat resolve_Checksum
    | cbv beta; unfold Domain; simpl;
      repeat calculate_length_ByteString
    | cbv beta; unfold Domain; simpl;
      repeat calculate_length_ByteString
    | solve_mod_8
    | solve_mod_8
    | apply Len_OK
    | repeat (decode_step idtac; unfold Domain; simpl)
    |
    | instantiate (1 := fun _ _ => True);
      simpl; intros; exact I
    | repeat (decode_step idtac; unfold Domain; simpl) ];
    cbv beta;
    unfold Domain; simpl
  end.

Ltac apply_IPChecksum_dep Len_OK :=
  match goal with
    H : cache_inv_Property _ _
    |- context[
           CorrectDecoder  _ _ _
                                   (fun data c =>
                                      (_ ThenChecksum _ OfSize 16 ThenCarryOn _) c) _ _] =>
    eapply compose_IPChecksum_format_correct_dep';
    [ apply H
    | repeat resolve_Checksum
    | cbv beta; unfold Domain; simpl;
      simpl mappend; unfold encode_word;
      rewrite !ByteString_enqueue_ByteString_measure,
      !length_encode_word';
      reflexivity
    | cbv beta; unfold Domain; simpl; reflexivity
    | cbv beta; unfold Domain; simpl;
      repeat calculate_length_ByteString
    | cbv beta; unfold Domain; simpl;
      repeat calculate_length_ByteString
    | cbv beta; unfold Domain; simpl;
      solve_mod_8
    | solve_mod_8
    | apply Len_OK
    | repeat decode_step idtac
    |
    | instantiate (1 := fun _ _ => True);
      simpl; intros; exact I
    |  ]
  end. *)
