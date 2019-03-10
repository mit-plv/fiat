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

Fixpoint Vector_checksum_bound n {sz} (bytes :ByteBuffer.t sz) acc : InternetChecksum.W16 :=
  match n, bytes with
  | 0, _ => acc
  | _, Vector.nil => acc
  | S 0, Vector.cons x _ _ => InternetChecksum.add_bytes_into_checksum x (wzero _) acc
  | _, Vector.cons x _ Vector.nil => InternetChecksum.add_bytes_into_checksum x (wzero _) acc
  | S (S n'), Vector.cons x _ (Vector.cons y _ t) =>
    (Vector_checksum_bound n' t (InternetChecksum.add_bytes_into_checksum x y acc))
  end.

Definition ByteBuffer_checksum_bound' n {sz} (bytes : ByteBuffer.t sz) : InternetChecksum.W16 :=
  InternetChecksum.ByteBuffer_fold_left_pair InternetChecksum.add_bytes_into_checksum n bytes (wzero _) (wzero _).

Lemma ByteBuffer_checksum_bound'_ok' :
  forall n {sz} (bytes :ByteBuffer.t sz) acc,
    Vector_checksum_bound n bytes acc =
    InternetChecksum.ByteBuffer_fold_left_pair InternetChecksum.add_bytes_into_checksum n bytes acc (wzero _).
Proof.
  fix IH 3.
  destruct bytes as [ | hd sz [ | hd' sz' tl ] ]; intros; simpl.
  - destruct n as [ | [ | ] ]; reflexivity.
  - destruct n as [ | [ | ] ]; reflexivity.
  - destruct n as [ | [ | ] ]; simpl; try reflexivity.
    rewrite IH; reflexivity.
Qed.

Lemma ByteBuffer_checksum_bound'_ok :
  forall n {sz} (bytes :ByteBuffer.t sz),
    Vector_checksum_bound n bytes (wzero _) = ByteBuffer_checksum_bound' n bytes.
Proof.
  intros; apply ByteBuffer_checksum_bound'_ok'.
Qed.

Definition IPChecksum_Valid_dec (n : nat) (b : ByteString)
  : {IPChecksum_Valid n b} + {~IPChecksum_Valid n b} := weq _ _.

Definition calculate_IPChecksum {S} {sz}
  : AlignedEncodeM (S := S) sz :=
  (fun v =>
     (let checksum := InternetChecksum.ByteBuffer_checksum_bound 20 v in
      (fun v idx s => SetByteAt (n := sz) 10 v 0 (wnot (split2 8 8 checksum)) ) >>
                                                                                (fun v idx s => SetByteAt (n := sz) 11 v 0 (wnot (split1 8 8 checksum)))) v)%AlignedEncodeM.

Definition splitLength (len: word 16) : Vector.t (word 8) 2 :=
  Vector.cons _ (split2 8 8 len) _ (Vector.cons _ (split1 8 8 len) _ (Vector.nil _)).

Definition Pseudo_Checksum_Valid
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           (n : nat) (* Number of /bits/ in checksum; needed by
                        ByteString2ListOfChar *)
           (b : ByteString)
  := onesComplement (wzero 8 :: protoCode ::
                           to_list srcAddr ++ to_list destAddr ++ to_list (splitLength udpLength)
                           ++ (ByteString2ListOfChar n b)
                    )%list
     = wones 16.

Import VectorNotations.

Definition pseudoHeader_checksum
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           {sz} (packet: ByteBuffer.t sz) :=
  InternetChecksum.ByteBuffer_checksum_bound (12 + wordToNat udpLength)
                                             (srcAddr ++ destAddr ++ [wzero 8; protoCode] ++ (splitLength udpLength) ++ packet).

Infix "^1+" := (InternetChecksum.OneC_plus) (at level 50, left associativity).

Import InternetChecksum.

Definition pseudoHeader_checksum'
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           {sz} (packet: ByteBuffer.t sz) :=
  ByteBuffer_checksum srcAddr ^1+
                               ByteBuffer_checksum destAddr ^1+
                                                             zext protoCode 8 ^1+
                                                                               udpLength ^1+
                                                                                          InternetChecksum.ByteBuffer_checksum_bound (wordToNat udpLength) packet.

Lemma OneC_plus_wzero_l :
  forall w, OneC_plus (wzero 16) w = w.
Proof. reflexivity. Qed.

Lemma OneC_plus_wzero_r :
  forall w, OneC_plus w (wzero 16) = w.
Proof.
  intros; rewrite OneC_plus_comm; reflexivity.
Qed.

Lemma Buffer_fold_left16_acc_oneC_plus :
  forall {sz} (packet: ByteBuffer.t sz) acc n,
    ByteBuffer_fold_left16 add_w16_into_checksum n packet acc =
    OneC_plus
      (ByteBuffer_fold_left16 add_w16_into_checksum n packet (wzero 16))
      acc.
Proof.
  fix IH 2.
  unfold ByteBuffer_fold_left16 in *.
  destruct packet as [ | hd sz [ | hd' sz' tl ] ]; intros; simpl.
  - destruct n as [ | [ | ] ]; reflexivity.
  - destruct n as [ | [ | ] ]; simpl; unfold add_bytes_into_checksum, add_w16_into_checksum;
      try rewrite OneC_plus_wzero_l, OneC_plus_comm; reflexivity.
  - destruct n as [ | [ | ] ]; simpl; unfold add_bytes_into_checksum, add_w16_into_checksum;
      try rewrite OneC_plus_wzero_l, OneC_plus_comm; try reflexivity.
    rewrite (IH _ tl (hd' +^+ hd ^1+ acc)).
    rewrite (IH _ tl (hd' +^+ hd)).
    rewrite OneC_plus_assoc.
    reflexivity.
Qed.

Lemma Vector_destruct_S :
  forall {A sz} (v: Vector.t A (S sz)),
  exists hd tl, v = hd :: tl.
Proof.
  repeat eexists.
  apply VectorSpec.eta.
Defined.

Lemma Vector_destruct_O :
  forall {A} (v: Vector.t A 0),
    v = [].
Proof.
  intro; apply Vector.case0; reflexivity.
Qed.

Ltac explode_vector :=
  lazymatch goal with
  | [ v: Vector.t ?A (S ?n) |- _ ] =>
    let hd := fresh "hd" in
    let tl := fresh "tl" in
    rewrite (Vector.eta v) in *;
    set (Vector.hd v: A) as hd; clearbody hd;
    set (Vector.tl v: Vector.t A n) as tl; clearbody tl;
    clear v
  | [ v: Vector.t _ 0 |- _ ] =>
    rewrite (Vector_destruct_O v) in *; clear v
  end.

Lemma pseudoHeader_checksum'_ok :
  forall (srcAddr : Vector.t (word 8) 4)
         (destAddr : Vector.t (word 8) 4)
         (udpLength : word 16)
         (protoCode : word 8)
         {sz} (packet: ByteBuffer.t sz),
    pseudoHeader_checksum srcAddr destAddr udpLength protoCode packet =
    pseudoHeader_checksum' srcAddr destAddr udpLength protoCode packet.
Proof.
  unfold pseudoHeader_checksum, pseudoHeader_checksum'.
  intros.
  repeat explode_vector.
  Opaque split1.
  Opaque split2.
  simpl in *.
  unfold ByteBuffer_checksum, InternetChecksum.ByteBuffer_checksum_bound, add_w16_into_checksum,
  add_bytes_into_checksum, ByteBuffer_fold_left16, ByteBuffer_fold_left_pair.
  fold @ByteBuffer_fold_left_pair.
  setoid_rewrite Buffer_fold_left16_acc_oneC_plus.
  rewrite combine_split.
  rewrite !OneC_plus_wzero_r, !OneC_plus_wzero_l, OneC_plus_comm.
  repeat (f_equal; [ ]).
  rewrite <- !OneC_plus_assoc.
  reflexivity.
Qed.

Definition calculate_PseudoChecksum {S} {sz}
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           (idx' : nat)
  : AlignedEncodeM (S := S) sz :=
  (fun v idx s =>
     (let checksum := pseudoHeader_checksum' srcAddr destAddr udpLength protoCode v in
      (fun v idx s => SetByteAt (n := sz) idx' v 0 (wnot (split2 8 8 checksum)) ) >>
                                                                                  (fun v idx s => SetByteAt (n := sz) (1 + idx') v 0 (wnot (split1 8 8 checksum)))) v idx s)%AlignedEncodeM.

Lemma ByteBuffer_to_list_append {sz sz'}
  : forall (v : ByteBuffer.t sz)
           (v' : ByteBuffer.t sz'),
    ByteBuffer.to_list (v ++ v')%vector
    = ((ByteBuffer.to_list v) ++ (ByteBuffer.to_list v'))%list.
Proof.
  induction v.
  - reflexivity.
  - simpl; intros.
    unfold ByteBuffer.to_list at 1; unfold to_list.
    f_equal.
    apply IHv.
Qed.

Import VectorNotations.


Lemma Pseudo_Checksum_Valid_bounded
      {A}
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : word 16)
      protoCode
      (predicate : A -> Prop)
      (format_A format_B : FormatM A ByteString)
      (len_format_A : A -> nat)
      (len_format_A_OK : forall a' b ctx ctx',
          computes_to (format_A a' ctx) (b, ctx')
          -> length_ByteString b = len_format_A a')
      (len_format_B : A -> nat)
      (len_format_B_OK : forall a' b ctx ctx',
          computes_to (format_B a' ctx) (b, ctx')
          -> length_ByteString b = len_format_B a')
      (byte_aligned_A : forall a : A, len_format_A a mod 8 = 0)
      (byte_aligned_B : forall a : A, len_format_B a mod 8 = 0)
  : forall (data : A) (x : ByteString) (x0 : CacheFormat) (x1 : ByteString) (x2 : CacheFormat)
           (ext ext' : ByteString) (env : CacheFormat) (c : word 16),
    predicate data ->
    format_A data env ∋ (x, x0) ->
    format_B data (addE x0 16) ∋ (x1, x2) ->
    Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode
                          (bin_measure (mappend x (mappend (format_checksum ByteString monoid ByteString_QueueMonoidOpt 16 c) x1)))
                          (mappend (mappend x (mappend (format_checksum ByteString monoid ByteString_QueueMonoidOpt 16 c) x1)) ext) ->
    Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode
                          (bin_measure (mappend x (mappend (format_checksum ByteString monoid ByteString_QueueMonoidOpt 16 c) x1)))
                          (mappend (mappend x (mappend (format_checksum ByteString monoid ByteString_QueueMonoidOpt 16 c) x1)) ext').
Proof.
  intros.
    unfold Pseudo_Checksum_Valid in *.
    revert H2.
    rewrite !ByteString2ListOfChar_Over; eauto.
    simpl; rewrite padding_eq_mod_8.
    rewrite !length_ByteString_enqueue_ByteString.
    rewrite Nat.add_mod by omega.
    apply len_format_A_OK in H0.
    apply len_format_B_OK in H1.
    unfold format_checksum; rewrite length_encode_word', measure_mempty.
    rewrite H0, byte_aligned_A, plus_O_n, NPeano.Nat.mod_mod, Nat.add_mod by omega.
    rewrite H1, byte_aligned_B, <- plus_n_O, NPeano.Nat.mod_mod by omega.
    reflexivity.
    simpl; rewrite padding_eq_mod_8.
    rewrite !length_ByteString_enqueue_ByteString.
    rewrite Nat.add_mod by omega.
    apply len_format_A_OK in H0.
    apply len_format_B_OK in H1.
    rewrite H0, byte_aligned_A, plus_O_n, NPeano.Nat.mod_mod, Nat.add_mod by omega.
    rewrite H1, byte_aligned_B, <- plus_n_O, NPeano.Nat.mod_mod by omega.
    unfold format_checksum; rewrite length_encode_word'; reflexivity.
Qed.

Lemma compose_PseudoChecksum_format_correct' {A}
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : word 16)
      protoCode
      (predicate : A -> Prop)
      (P : CacheDecode -> Prop)
      (P_inv : (CacheDecode -> Prop) -> Prop)
      (P_invM : (CacheDecode -> Prop) -> Prop)
      (format_A format_B : FormatM A ByteString)
      (subformat : FormatM A ByteString)
      (decode_measure : DecodeM (nat * _) _)
      (len_format_A : A -> nat)
      (len_format_A_OK : forall a' b ctx ctx',
          computes_to (format_A a' ctx) (b, ctx')
          -> length_ByteString b = len_format_A a')
      (len_format_B : A -> nat)
      (len_format_B_OK : forall a' b ctx ctx',
          computes_to (format_B a' ctx) (b, ctx')
          -> length_ByteString b = len_format_B a')
      View_Predicate
      format_measure
  : cache_inv_Property P (fun P => P_inv P /\ P_invM P) ->
    (forall a, NPeano.modulo (len_format_A a) 8 = 0)
    -> (forall a, NPeano.modulo (len_format_B a) 8 = 0)
    ->
    forall decodeA : _ -> CacheDecode -> option (A * _ * CacheDecode),
      (cache_inv_Property P P_inv ->
       CorrectDecoder monoid predicate predicate eq (format_A ++ format_unused_word 16 ++ format_B)%format decodeA P (format_A ++ format_unused_word 16 ++ format_B)%format) ->
      (cache_inv_Property P P_invM ->
          CorrectRefinedDecoder monoid predicate View_Predicate
                                (fun a n => len_format_A a + 16 + len_format_B a = n * 8)
                                (format_A ++ format_unused_word 16 ++ format_B)%format
                                subformat
                                decode_measure P
                                format_measure) ->
      (Prefix_Format _ (format_A ++ format_unused_word 16 ++ format_B) subformat)%format->
      CorrectDecoder monoid predicate predicate eq
                     (format_A ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode) OfSize 16 ThenCarryOn format_B)
                     (fun (bin : _) (env : CacheDecode) =>
                          `(n, _, _) <- decode_measure bin env;
                            if weqb (onesComplement (wzero 8 :: protoCode ::
                                                       to_list srcAddr ++ to_list destAddr ++ to_list (splitLength udpLength)
                                                       ++(ByteString2ListOfChar (n * 8) bin))%list) (wones 16) then
                              decodeA bin env
                            else None)
                     P
                     (format_A ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode) OfSize 16 ThenCarryOn format_B).
Proof.
  intros.
  rename H4 into H4'; rename H3 into H4; rename H2 into H3.
  eapply format_decode_correct_alt.
  Focus 7.
  (*7: {*)
  {eapply (composeChecksum_format_correct'
                 A _ monoid _ 16 (Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode)).
       - eapply H.
       - specialize (H4 (proj2 H)).
         split.
         2: eauto.
         eapply injection_decode_correct with (inj := fun n => mult n 8).
         4: simpl.
         eapply H4.
         + intros.
           instantiate (1 := fun a n => len_format_A a + 16 + len_format_B a = n).
           eapply H6.
         + intros; instantiate (1 := fun v => View_Predicate (Nat.div v 8)).
           cbv beta.
           rewrite Nat.div_mul; eauto.
         + intros; apply unfold_computes; intros.
           split.
           2: rewrite unfold_computes in H5; intuition.
           intros.
           rewrite unfold_computes in H5; intuition.
           instantiate (1 := fun v env t => format_measure (Nat.div v 8) env t).
           cbv beta; rewrite Nat.div_mul; eauto.
       - simpl; intros.
         destruct t1; destruct t2; simpl fst in *; simpl snd in *.
         apply unfold_computes in H7; apply unfold_computes in H6.
         erewrite len_format_A_OK; eauto.
         erewrite (len_format_B_OK _ b0); eauto.
         unfold format_checksum; rewrite length_encode_word', measure_mempty.
         rewrite <- H2; omega.
       - eauto.
       - eapply Pseudo_Checksum_Valid_bounded; eauto. }
  all: try unfold flip, pointwise_relation, impl;
    intuition eauto using EquivFormat_reflexive.
  all: try unfold flip, pointwise_relation, impl;
    intuition eauto using EquivFormat_reflexive.
    instantiate (1 := fun (n : nat) a =>
                    weq
       (onesComplement
          (wzero 8
           :: (protoCode
               :: to_list srcAddr ++
                  to_list destAddr ++ to_list (splitLength udpLength) ++ ByteString2ListOfChar n a)%list))
       (wones 16)).
  unfold Compose_Decode.
  Local Opaque Nat.div.
  destruct (decode_measure a a0) as [ [ [? ?] ? ] | ]; simpl; eauto.
  symmetry.
  find_if_inside.
  eapply weqb_true_iff in e; rewrite e; eauto.
  destruct (weqb
      (add_bytes_into_checksum (wzero 8) protoCode
         (onesComplement
            (to_list srcAddr ++
             to_list destAddr ++ split2 8 8 udpLength :: (split1 8 8 udpLength :: ByteString2ListOfChar (n * 8) a)%list)))
      WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1) eqn: ? ; eauto.
  eapply weqb_true_iff in Heqb0.
  congruence.
Qed.

Fixpoint aligned_Pseudo_checksum
         (srcAddr : ByteBuffer.t 4)
         (destAddr : ByteBuffer.t 4)
         (pktlength : word 16)
         id
         measure
         {sz}
         (v : t Core.char sz) (idx : nat)
         {struct idx}
  := match idx with
     | 0 =>
       weqb (InternetChecksum.ByteBuffer_checksum_bound (12 + measure)
                                                        ([wzero 8; id] ++ srcAddr ++ destAddr ++
                                                                       (splitLength pktlength) ++ v ))%vector
            (wones 16)
     | S idx' =>
       match v with
       | Vector.cons _ _ v' => aligned_Pseudo_checksum srcAddr destAddr pktlength id measure v' idx'
       | _ => false
       end
     end.

Lemma Vector_checksum_bound_acc'
  : forall sz'' sz sz' (sz_lt : le sz' sz'') (v : Vector.t _ sz) b1 b2 acc,
    Vector_checksum_bound sz' v (add_bytes_into_checksum b1 b2 acc) =
    add_bytes_into_checksum b1 b2 (Vector_checksum_bound sz' v acc).
Proof.
  induction sz''; intros.
  - inversion sz_lt.
    subst; reflexivity.
  - inversion sz_lt; subst.
    + clear sz_lt.
      destruct sz''; simpl.
      * destruct v; simpl; eauto.
        rewrite add_bytes_into_checksum_swap; eauto.
      * destruct v; simpl; eauto.
        destruct v; simpl; eauto.
        rewrite add_bytes_into_checksum_swap; eauto.
        rewrite !IHsz'' by omega.
        rewrite add_bytes_into_checksum_swap; eauto.
    + eauto.
Qed.

Lemma Vector_checksum_bound_acc
  : forall sz sz' (v : Vector.t _ sz) b1 b2 acc,
    Vector_checksum_bound sz' v (add_bytes_into_checksum b1 b2 acc) =
    add_bytes_into_checksum b1 b2 (Vector_checksum_bound sz' v acc).
Proof.
  intros; eapply Vector_checksum_bound_acc'.
  reflexivity.
Qed.

Lemma dequeue_byte_ByteString2ListOfChar
  : forall m sz (v : Vector.t _ sz) b,
    ByteString2ListOfChar ((S m) * 8) (build_aligned_ByteString (b :: v))
    = cons b (ByteString2ListOfChar (m * 8) (build_aligned_ByteString (v))).
Proof.
  intros; erewrite <- ByteString2ListOfChar_push_char.
  f_equal.
  pose proof (build_aligned_ByteString_append v [b]) as H; simpl in H.
  rewrite H.
  reflexivity.
Qed.

Lemma ByteString2ListOfChar_overflow
  : forall n,
    ByteString2ListOfChar ((S n) * 8) (build_aligned_ByteString [])
    = cons (wzero 8) (ByteString2ListOfChar (n * 8) (build_aligned_ByteString [])).
Proof.
  reflexivity.
Qed.

Lemma InternetChecksum_To_ByteBuffer_Checksum':
  forall (sz m : nat) (v : t Core.char sz),
    checksum (ByteString2ListOfChar (m * 8) (build_aligned_ByteString v)) = ByteBuffer_checksum_bound m v.
Proof.
  intros.
  assert ((exists m', m = 2 * m') \/ (exists m', m = S (2 * m'))).
  { induction m; eauto.
    destruct IHm; destruct_ex; subst; eauto.
    left; exists (S x); omega.
  }
  destruct H as [ [? ?] | [? ?] ]; subst.
  - rewrite (mult_comm 2).
    apply InternetChecksum_To_ByteBuffer_Checksum.
  - revert sz v.
    induction x.
    + intros; destruct v.
      * reflexivity.
      * rewrite dequeue_byte_ByteString2ListOfChar.
        reflexivity.
    + intros; destruct v.
      * replace (S (2 * S x)) with ((S (S (S (2 * x))))) by omega.
        rewrite ByteString2ListOfChar_overflow.
        rewrite ByteString2ListOfChar_overflow.
        unfold checksum; fold checksum.
        rewrite IHx.
        unfold ByteBuffer_checksum_bound, ByteBuffer_fold_left16.
        simpl.
        destruct (2 * x); eauto.
      * rewrite dequeue_byte_ByteString2ListOfChar.
        destruct v.
        replace (2 * S x * 8) with ((S (S (2 * x))) * 8) by omega.
        rewrite ByteString2ListOfChar_overflow.
        unfold checksum; fold checksum.
        rewrite IHx.
        rewrite <- !ByteBuffer_checksum_bound_ok.
        simpl.
        destruct (2 * x); eauto.
        replace (2 * S x * 8) with ((S (S (2 * x))) * 8) by omega.
        rewrite dequeue_byte_ByteString2ListOfChar.
        replace
          (checksum (h :: (h0 :: ByteString2ListOfChar (S (2 * x) * 8) (build_aligned_ByteString v))%list))
          with
            (add_bytes_into_checksum
               h h0
               (checksum (ByteString2ListOfChar (S (2 * x) * 8) (build_aligned_ByteString v))%list))
          by reflexivity.
        rewrite IHx.
        rewrite <- !ByteBuffer_checksum_bound_ok.
        replace (2 * S x) with (S (S ( 2 * x))) by omega.
        rewrite <- Vector_checksum_bound_acc; reflexivity.
Qed.

Lemma aligned_Pseudo_checksum_OK_1
      (srcAddr : ByteBuffer.t 4)
      (destAddr : ByteBuffer.t 4)
      (pktlength : word 16)
      id
      measure
      {sz}
  : forall (v : t Core.char sz),
    weqb
      (InternetChecksum.add_bytes_into_checksum (wzero 8) id
                                                (onesComplement(to_list srcAddr ++ to_list destAddr ++ split2 8 8  pktlength :: split1 8 8 pktlength :: (ByteString2ListOfChar (measure * 8) (build_aligned_ByteString v)))%list))
      WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
    = aligned_Pseudo_checksum srcAddr destAddr pktlength id measure v 0.
Proof.
  simpl; intros.
  unfold onesComplement.
  rewrite checksum_eq_Vector_checksum.
  rewrite <- ByteBuffer_checksum_bound_ok.
  unfold ByteBuffer.t in *.
  simpl.
    replace srcAddr with
      (Vector.hd srcAddr :: Vector.hd (Vector.tl srcAddr)
                 :: Vector.hd (Vector.tl (Vector.tl srcAddr))
                 :: Vector.hd (Vector.tl (Vector.tl (Vector.tl srcAddr)))
                 :: (@Vector.nil _))
    by abstract (pattern srcAddr;
              repeat (apply caseS'; let t' := fresh in intros ? t'; pattern t'); apply case0;
              reflexivity).
  replace destAddr with
      (Vector.hd destAddr :: Vector.hd (Vector.tl destAddr)
                 :: Vector.hd (Vector.tl (Vector.tl destAddr))
                 :: Vector.hd (Vector.tl (Vector.tl (Vector.tl destAddr)))
                 :: (@Vector.nil _))
    by abstract (pattern destAddr;
              repeat (apply caseS'; let t' := fresh in intros ? t'; pattern t'); apply case0;
              reflexivity).
  simpl.
  repeat rewrite Vector_checksum_bound_acc.
  rewrite <- checksum_eq_Vector_checksum.
  f_equal.
  rewrite ByteBuffer_checksum_bound_ok.
  repeat rewrite (add_bytes_into_checksum_swap _ id); f_equal.
  repeat rewrite (add_bytes_into_checksum_swap _ (Vector.hd (Vector.tl srcAddr))); f_equal.
  repeat rewrite (add_bytes_into_checksum_swap _ (Vector.hd (Vector.tl (Vector.tl (Vector.tl srcAddr))))); f_equal.
  repeat rewrite (add_bytes_into_checksum_swap _ (Vector.hd (Vector.tl destAddr))); f_equal.
  repeat rewrite (add_bytes_into_checksum_swap _ (Vector.hd (Vector.tl (Vector.tl (Vector.tl destAddr))))); f_equal.
  f_equal.
  apply InternetChecksum_To_ByteBuffer_Checksum'.
Qed.

Lemma aligned_Pseudo_checksum_OK_2
      (srcAddr : ByteBuffer.t 4)
      (destAddr : ByteBuffer.t 4)
      (pktlength : word 16)
      id
      measure
      {sz}
  : forall (v : ByteBuffer.t (S sz)) (idx : nat),
    aligned_Pseudo_checksum srcAddr destAddr pktlength id measure v (S idx) =
    aligned_Pseudo_checksum srcAddr destAddr pktlength id measure (Vector.tl v) idx.
Proof.
  intros v; pattern sz, v.
  apply Vector.caseS; reflexivity.
Qed.

Fixpoint aligned_IPchecksum
         m
         {sz}
         (v : t Core.char sz) (idx : nat)
         {struct idx}
  := match idx with
     | 0 =>
       weqb (InternetChecksum.ByteBuffer_checksum_bound m v) (wones 16)
     | S idx' =>
       match v with
       | Vector.cons _ _ v' => aligned_IPchecksum m v' idx'
       | _ => false
       end
     end.

Corollary aligned_IPChecksum_OK_1 :
  forall m sz (v : ByteBuffer.t sz),
    IPChecksum_Valid_check (m * 8) (build_aligned_ByteString v)
    = aligned_IPchecksum m v 0.
Proof.
  intros.
  unfold IPChecksum_Valid_check, aligned_IPchecksum.
  rewrite InternetChecksum_To_ByteBuffer_Checksum'.
  higher_order_reflexivity.
Qed.

Lemma aligned_IPChecksum_OK_2
      m
      {sz}
  : forall (v : ByteBuffer.t (S sz)) (idx : nat),
    aligned_IPchecksum m v (S idx) =
    aligned_IPchecksum m (Vector.tl v) idx.
Proof.
  intros v; pattern sz, v.
  apply Vector.caseS; reflexivity.
Qed.

Hint Extern 4 (weqb _ _ = _) =>
rewrite aligned_Pseudo_checksum_OK_1; higher_order_reflexivity.
Hint Extern 4 => eapply aligned_Pseudo_checksum_OK_2.

Hint Extern 4 (IPChecksum_Valid_check _ _ = _ ) =>
rewrite aligned_IPChecksum_OK_1; higher_order_reflexivity.
Hint Extern 4  => eapply aligned_IPChecksum_OK_2.

(* We admit alignment rules for encoding IP checksums. *)
Lemma CorrectAlignedEncoderForPseudoChecksumThenC
      {S}
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : word 16)
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
Admitted.

Lemma CorrectAlignedEncoderForIPChecksumThenC
      {S}
      (format_A format_B : FormatM S ByteString)
      (encode_A : forall sz, AlignedEncodeM sz)
      (encode_B : forall sz, AlignedEncodeM sz)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
  : CorrectAlignedEncoder
      (format_B ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn format_A)
      (fun sz => encode_B sz >>
                          (fun v idx s => SetCurrentByte v idx (wzero 8)) >>
                          (fun v idx s => SetCurrentByte v idx (wzero 8)) >>
                          encode_A sz >>
                          calculate_IPChecksum)% AlignedEncodeM.
Proof.
Admitted.
