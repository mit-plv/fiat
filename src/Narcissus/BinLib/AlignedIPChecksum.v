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
           (measure : nat)
           (udpLength : word 16)
           (protoCode : word 8)
           {sz} (packet: ByteBuffer.t sz) :=
  InternetChecksum.ByteBuffer_checksum_bound (12 + measure)
                                             (srcAddr ++ destAddr ++ [wzero 8; protoCode] ++ (splitLength udpLength) ++ packet).

Infix "^1+" := (InternetChecksum.OneC_plus) (at level 50, left associativity).

Import InternetChecksum.

Definition pseudoHeader_checksum'
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (measure : nat)
           (udpLength : word 16)
           (protoCode : word 8)
           {sz} (packet: ByteBuffer.t sz) :=
  ByteBuffer_checksum srcAddr ^1+
                               ByteBuffer_checksum destAddr ^1+
                                                             zext protoCode 8 ^1+
                                                                               udpLength ^1+
                                                                                          InternetChecksum.ByteBuffer_checksum_bound measure packet.

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
         (measure : nat)
         (udpLength : word 16)
         (protoCode : word 8)
         {sz} (packet: ByteBuffer.t sz),
    pseudoHeader_checksum srcAddr destAddr measure udpLength protoCode packet =
    pseudoHeader_checksum' srcAddr destAddr measure udpLength protoCode packet.
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
           (measure : nat)
           (udpLength : word 16)
           (protoCode : word 8)
           (idx' : nat)
  : AlignedEncodeM (S := S) sz :=
  (fun v idx s =>
     (let checksum := pseudoHeader_checksum' srcAddr destAddr measure udpLength protoCode v in
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
       weqb (pseudoHeader_checksum' srcAddr destAddr measure pktlength id v)
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
  rewrite <- pseudoHeader_checksum'_ok.
  rewrite checksum_eq_Vector_checksum.
  unfold pseudoHeader_checksum.
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

Lemma Vector_append_destruct {A n1 n2}
      (v : Vector.t A (n1+n2))
  : exists v1 v2, v = v1 ++ v2.
Proof.
  eauto using Vector_split_append.
Qed.

Lemma Vector_append_destruct3 {A n1 n2 n3}
      (v : Vector.t A (n1+(n2+n3)))
  : exists v1 v2 v3, v = v1 ++ v2 ++ v3.
Proof.
  destruct (Vector_append_destruct v) as [v1 [v23 ?]].
  destruct (Vector_append_destruct v23) as [v2 [v3 ?]].
  exists v1, v2, v3. subst. reflexivity.
Qed.

Lemma AlignedEncoder_some_inv'
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall sz (t : Vector.t Core.char sz) n1 (s : S) v ni ce ce',
    enc _ t n1 s ce = Some (v, ni, ce') ->
    exists b ce', enc' s ce = Some (b, ce').
Proof.
  intros. destruct (enc' s ce) eqn:?; destruct_conjs; eauto.
  eapply enc_OK in Heqo. rewrite Heqo in H. discriminate.
Qed.

Lemma AlignedEncoder_sz_destruct'
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall sz (t : Vector.t Core.char sz) n1 (s : S) v ni ce ce',
    enc _ t n1 s ce = Some (v, ni, ce') ->
    forall b ce', enc' s ce = Some (b, ce') ->
    sz = n1 + (numBytes b + (sz-(n1+numBytes b))).
Proof.
  intros.
  destruct (Nat.le_decidable (1 + sz) (numBytes b + n1)).
  edestruct enc_OK as [_ [? _]]. erewrite H2 in H; eauto. discriminate.
  rewrite length_ByteString_no_padding by eauto. omega. omega.
Qed.

Lemma AlignedEncoder_sz_destruct
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      n2
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall sz (t : Vector.t Core.char sz) n1 (s : S) v ni ce ce',
    enc _ t n1 s ce = Some (v, ni, ce') ->
    sz = n1 + ((ni-n1) + (sz-ni)) /\
    n2 = ni - n1.
Proof.
  intros. edestruct @AlignedEncoder_some_inv' as [b [? ?]]; eauto.
  assert (sz = n1 + (numBytes b + (sz-(n1+numBytes b)))) by eauto using AlignedEncoder_sz_destruct'.
  revert dependent t. revert v. rewrite H1.
  intros. destruct (Vector_append_destruct3 t) as [t1 [t2 [t3 ?]]]. subst.
  edestruct enc_OK as [? _]. edestruct H2; eauto. clear H2. destruct_conjs.
  rewrite H2 in H. injections.
  split. omega.
  erewrite enc'_sz_eq; eauto. omega.
Qed.

Lemma AlignedEncoder_some_inv
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall sz (t : Vector.t Core.char sz) n1 (s : S) v ni ce ce',
    enc _ t n1 s ce = Some (v, ni, ce') ->
    exists b , enc' s ce = Some (b, ce').
Proof.
  intros. edestruct @AlignedEncoder_some_inv' as [b [? ?]]; eauto.
  assert (sz = n1 + (numBytes b + (sz-(n1+numBytes b)))) by eauto using AlignedEncoder_sz_destruct'.
  revert dependent t. revert v. rewrite H1.
  intros. destruct (Vector_append_destruct3 t) as [t1 [t2 [t3 ?]]]. subst.
  edestruct enc_OK as [? _]. edestruct H2; eauto. clear H2. destruct_conjs.
  rewrite H2 in H. injections.
  rewrite H0. eexists. repeat f_equal.
Qed.

Lemma AlignedEncoder_inv
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n1 n2 n3
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall idx (t1 : Vector.t Core.char n1) (t2 : Vector.t Core.char n2) (t3 : Vector.t Core.char n3)
      (s : S) v ce ce',
    enc _ (t1++t2++t3) n1 s ce = Some (v, idx, ce') ->
    exists v2,
      enc n2 t2 0 s ce = Some (v2, n2, ce') /\
      v = t1 ++ v2 ++ t3 /\
      idx = n1 + n2 /\
      (forall b ce'', enc' s ce = Some (b, ce'') ->
                 b = build_aligned_ByteString v2 /\ ce'' = ce').
Proof.
  intros. edestruct @AlignedEncoder_some_inv' as [b [? Heqo]]; eauto.
  specialize (enc'_sz_eq _ _ _ _ Heqo). subst.
  edestruct enc_OK as [? _].
  edestruct H0; eauto. clear H0. destruct_conjs.
  rewrite H0 in H. injections.
  edestruct enc_OK with (idx:=0) as [? _].
  edestruct H with (m:=0) (v0:=t2) (v1:=Vector.nil Core.char) (v2:=Vector.nil Core.char); eauto.
  clear H. simpl in *. destruct_conjs.
  revert H. rewrite Vector_append_nil_r'. generalize (plus_n_O (numBytes b)).
  destruct e. simpl. intros.
  eexists; intuition eauto.
  apply build_aligned_ByteString_inj.
  rewrite !build_aligned_ByteString_append.
  rewrite <- H1. repeat f_equal.
  rewrite <- H2.
  rewrite !build_aligned_ByteString_nil.
  eauto using mempty_left.
  rewrite H3 in Heqo. injections.
  rewrite <- H2.
  rewrite !build_aligned_ByteString_nil.
  eauto using mempty_left.
  rewrite H3 in Heqo. injections. auto.
Qed.

Lemma AlignedEncoder_dist
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n1 n2 n3
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall idx (t1 : Vector.t Core.char n1) (t2 : Vector.t Core.char n2) (t3 : Vector.t Core.char n3)
      (s : S) v ce ce',
    enc _ (t1++t2) n1 s ce = Some (v, idx, ce') ->
    enc _ ((t1++t2)++t3) n1 s ce = Some (v++t3, idx, ce').
Proof.
  intros. edestruct @AlignedEncoder_some_inv' as [b [? Heqo]]; eauto.
  assert (n2 = numBytes b + (n2-numBytes b)). {
    eapply AlignedEncoder_sz_destruct' in H; eauto.
    omega.
  } revert dependent t2. revert dependent v. rewrite H0. intros.
  rename t2 into t23. rename t3 into t4.
  destruct (Vector_append_destruct t23) as [t2 [t3 ?]]. subst.
  edestruct @AlignedEncoder_inv; try apply H; eauto. intuition eauto.
  erewrite enc'_sz_eq; eauto. erewrite enc'_sz_eq; eauto. destruct_conjs.
  subst.
  match goal with
  | |- enc (?n1 + (?n2 + ?n3) + ?n4) ((?t1 ++ ?t2 ++ ?t3) ++ ?t4) ?a ?b ?c =
    Some ((?t1' ++ ?t2' ++ ?t3') ++ ?t4', ?d, ?e)=>
    assert (enc (n1 + (n2 + (n3 + n4))) (t1 ++ t2 ++ (t3 ++ t4)) a b c =
            Some ((t1' ++ t2' ++ (t3' ++ t4')), d, e))
  end.
  edestruct enc_OK as [? _]. edestruct H2; eauto. clear H2. destruct_conjs.
  rewrite H2.
  edestruct @AlignedEncoder_inv; try apply H2; eauto. intuition eauto.
  erewrite enc'_sz_eq; eauto. erewrite enc'_sz_eq; eauto. destruct_conjs.
  subst. rewrite H1 in H5. injections. eauto.
  clear H1 H H4.
  revert t1 t2 t3 t4 x0 H2. generalize (n2-numBytes b). generalize (numBytes b).
  clear. intros. rename n into n2. rename n3 into n4. rename n0 into n3.

  assert (n1 + (n2 + n3) + n4 = n1 + (n2 + (n3 + n4))) by omega.
  assert (forall {A}
            (t1 : Vector.t A n1) (t2 : Vector.t A n2) (t3 : Vector.t A n3) (t4 : Vector.t A n4),
             t1 ++ t2 ++ t3 ++ t4 = eq_rect _ (Vector.t A) ((t1 ++ t2 ++ t3) ++ t4) _ H) as L. {
    clear. intros.
    assert (n2 + n3 + n4 = n2 + (n3 + n4)) by omega.
    rewrite <- (Vector_append_assoc' _ _ _ _ H0). f_equal.
    apply Vector_append_assoc.
  }
  revert H2. rewrite !L. clear. destruct H. simpl. eauto.
Qed.

Corollary AlignedEncoder_dist0
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n2 n3
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall idx  (t2 : Vector.t Core.char n2) (t3 : Vector.t Core.char n3)
      (s : S) v ce ce',
    enc _ t2 0 s ce = Some (v, idx, ce') ->
    enc _ (t2++t3) 0 s ce = Some (v++t3, idx, ce').
Proof.
  intros. eapply AlignedEncoder_dist with (t1:=[]); eauto.
Qed.

Corollary AlignedEncoder_invl
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n1 n2 n23
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall idx (t1 : Vector.t Core.char n1) (t23 : Vector.t Core.char n23)
      (s : S) v ce ce',
    enc _ (t1++t23) n1 s ce = Some (v, idx, ce') ->
    exists v2,
      enc _ t23 0 s ce = Some (v2, n2, ce') /\
      v = t1 ++ v2 /\
      idx = n1 + n2.
Proof.
  intros.
  assert (n23 = (idx - n1 + (n1 + n23 - idx)) /\ n2 = idx - n1). {
    eapply AlignedEncoder_sz_destruct in H; eauto.
    omega.
  } destruct_conjs.
  revert dependent t23. revert dependent v. rewrite H0. intros.
  destruct (Vector_append_destruct t23) as [t2 [t3 ?]].
  subst. edestruct @AlignedEncoder_inv; try apply H; eauto.
  eexists. intuition eauto.
  eapply AlignedEncoder_dist0; eauto.
Qed.

Corollary AlignedEncoder_invr
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n2 n3
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall idx (t2 : Vector.t Core.char n2) (t3 : Vector.t Core.char n3)
      (s : S) v ce ce',
    enc _ (t2++t3) 0 s ce = Some (v, idx, ce') ->
    exists v2,
      enc _ t2 0 s ce = Some (v2, n2, ce') /\
      v = v2 ++ t3 /\
      idx = n2 /\
      (forall b ce'', enc' s ce = Some (b, ce'') ->
                 b = build_aligned_ByteString v2 /\
                 ce'' = ce').
Proof.
  intros.
  eapply AlignedEncoder_inv with (t1:=[]); eauto.
Qed.

Lemma AlignedEncoder_fixed
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n1 n2
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall sz idx (t : Vector.t Core.char sz)
      (s : S) v ce ce',
    enc _ t n1 s ce = Some (v, idx, ce') ->
    enc _ v n1 s ce = Some (v, idx, ce').
Proof.
  intros.
  pose proof H. eapply AlignedEncoder_sz_destruct in H0; eauto. destruct_conjs.
  revert dependent t. revert dependent v. rewrite H0. intros.
  edestruct (Vector_append_destruct3 t) as [t1 [t2 [t3 ?]]].
  subst. edestruct @AlignedEncoder_inv; try apply H; eauto. destruct_conjs.
  edestruct @AlignedEncoder_some_inv' as [b [? Heqo]]; eauto.
  match goal with
  | |- ?x = _ => destruct x eqn:?
  end. destruct_conjs.
  subst. edestruct @AlignedEncoder_inv; try apply Heqo0; eauto. destruct_conjs.
  subst. edestruct H4; eauto. edestruct H7; eauto. subst.
  repeat f_equal; eauto. apply build_aligned_ByteString_inj. eauto.
  specialize (enc'_sz_eq _ _ _ _ Heqo). subst. destruct enc'_sz_eq.
  edestruct enc_OK as [? _]. edestruct H2; eauto. clear H2. destruct_conjs.
  rewrite H2 in Heqo0. discriminate.
Qed.

Definition EncodeAt {S : Type} {cache : Cache}
           {sz} (idx : nat) (enc : forall {n}, @AlignedEncodeM _ S n) : @AlignedEncodeM _ S sz :=
  fun v idx' s c => Ifopt enc v idx s c as a Then Some ((fst (fst a)), idx', (snd a)) Else None.

Lemma EncodeMEquivAlignedEncodeMDep
      {S A}
      (enc1' : EncodeM S ByteString)
      (enc2' : A -> EncodeM S ByteString)
      (f' : ByteString -> A)
      (enc1 : forall sz, AlignedEncodeM sz)
      (enc2 : A -> forall sz, AlignedEncodeM sz)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> A)
      (l : nat)
      (enc1_OK : EncodeMEquivAlignedEncodeM enc1' enc1)
      (enc2_OK : forall a, EncodeMEquivAlignedEncodeM (enc2' a) (enc2 a))
      (enc1'_aligned : forall s ce t ce', enc1' s ce = Some (t, ce') -> padding t = 0)
      (enc2'_aligned : forall a s ce t ce', enc2' a s ce = Some (t, ce') -> padding t = 0)
      (enc1_sz_eq : forall s ce t ce',
          enc1' s ce = Some (t, ce') ->
          numBytes t = l)
      (enc2_sz_eq : forall a s ce t ce',
          enc2' a s ce = Some (t, ce') -> numBytes t = l)
      (f_OK : forall (b : ByteString)
                idx (v1 : Vector.t Core.char idx)
                m (v2 : Vector.t Core.char m)
                (v : Vector.t Core.char (idx + ((numBytes b) + m))),
          ByteString_enqueue_ByteString (build_aligned_ByteString v1)
                                        (ByteString_enqueue_ByteString b (build_aligned_ByteString v2))
          = build_aligned_ByteString v ->
          f' b = f (numBytes b) v idx)
  : EncodeMEquivAlignedEncodeM
      (fun s ce =>
         `(p, ce) <- enc1' s ce;
           enc2' (f' p) s ce)
      (fun sz => enc1 sz >>
                   (fun v idx s => let a := f l v (idx-l) in
                                EncodeAt (idx-l) (enc2 a) v idx s))%AlignedEncodeM.
Proof.
  repeat split; intros; simpl in *. {
    destruct enc1' eqn:?; [| discriminate]; destruct_conjs; simpl in *.
    specialize (enc1_sz_eq _ _ _ _ Heqe).
    specialize (enc2_sz_eq _ _ _ _ _ H).
    specialize (enc1'_aligned _ _ _ _ Heqe).
    assert (numBytes b = numBytes t) as L1 by (subst; eauto).

    edestruct enc1_OK as [? _]. specialize (H1 _ _ Heqe).
    revert H1. rewrite L1. intros.
    edestruct (H1 enc1'_aligned v1 v _ v2); eauto. clear H1. destruct_conjs.

    assert (exists v, v1 ++ v ++ v2 = x) as L2. {
      symmetry in H2. destruct (build_aligned_ByteString_split' _ _ _ H2).
      symmetry in H3. destruct (build_aligned_ByteString_split _ _ _ H3).
      replace (idx + (numBytes t + m) - idx - m) with (numBytes t) in * by omega.
      eexists. apply build_aligned_ByteString_inj. rewrite !build_aligned_ByteString_append.
      rewrite H2. rewrite H4. repeat f_equal.
    } destruct L2 as [v' L2].

    edestruct enc2_OK as [? _]. specialize (H3 _ _ H).
    edestruct H3; eauto. clear H3. destruct_conjs.
    rewrite L2 in H3.

    eexists. split; eauto. unfold AppendAlignedEncodeM.
    rewrite H1. simpl. unfold EncodeAt.
    replace (idx + numBytes t - l) with idx by omega.
    match goal with
    | H : enc2 ?a _ _ _ _ _ = _ |- context[enc2 ?a' _ _ _ _ _] =>
      replace a' with a
    end.
    rewrite H3. simpl. reflexivity.
    destruct L1. rewrite <- enc1_sz_eq. eauto.
  } {
    destruct enc1' eqn:?; [| discriminate]; destruct_conjs; simpl in *.
    edestruct enc1_OK as [_ [? _]]. eapply H1 in Heqe.
    unfold AppendAlignedEncodeM. rewrite Heqe. reflexivity.
    assert (numBytes b = numBytes t) as L1. {
      erewrite enc1_sz_eq; eauto.
      erewrite enc2_sz_eq; eauto.
    }
    rewrite length_ByteString_no_padding in *; eauto. omega.
  } {
    destruct enc1' eqn:?; [| discriminate]; destruct_conjs; simpl in *.
    exfalso. eauto.
  } {
    destruct enc1' eqn:?; destruct_conjs; simpl in *; unfold AppendAlignedEncodeM. {
      destruct (Nat.le_decidable (1 + numBytes') (numBytes b + idx)).
      edestruct enc1_OK as [_ [? _]]. erewrite H1; eauto.
      rewrite length_ByteString_no_padding by eauto. omega.
      assert (exists m, numBytes' = idx + (numBytes b + m)). {
        exists (numBytes' - (idx + numBytes b)). omega.
      } destruct H1 as [m ?]. subst.
      edestruct (enc1_OK env s idx) as [? _]; eauto.
      edestruct H1; eauto. destruct_conjs.
      match goal with
      | H : enc1 _ ?v' _ _ _ = _ |- _ => replace v with v'
      end. rewrite H2. simpl. unfold EncodeAt.
      edestruct enc2_OK as [_ [_ [_ ?]]]. rewrite H4; eauto.
      specialize (enc1_sz_eq _ _ _ _ Heqe).
      replace (idx + numBytes b - l) with idx by omega.
      rewrite <- enc1_sz_eq. erewrite <- f_OK; eauto.
      repeat (rewrite Vector_split_append; f_equal).
    } {
      edestruct (enc1_OK env s idx) as [_ [_ [_ ?]]]; eauto. eapply H0 in Heqe; eauto.
      rewrite Heqe. reflexivity.
    }
  }
Qed.

Lemma sequence_Encoding_padding_0
      {cache : Cache} {S : Type}
      enc1 enc2
      (enc1_aligned : forall s ce t ce', enc1 s ce = Some (t, ce') -> padding t = 0)
      (enc2_aligned : forall s ce t ce', enc2 s ce = Some (t, ce') -> padding t = 0)
  : forall s ce b ce',
    @sequence_Encode ByteString cache _ S enc1 enc2 s ce = Some (b, ce') -> padding b = 0.
Proof.
  unfold sequence_Encode. intros.
  destruct enc1 eqn:?; destruct_conjs; [| discriminate]; simpl in *.
  destruct enc2 eqn:?; destruct_conjs; [| discriminate]; simpl in *.
  injections. apply enc1_aligned in Heqo. apply enc2_aligned in Heqo0.
  rewrite ByteString_enqueue_ByteString_padding_eq. rewrite Heqo. rewrite Heqo0.
  reflexivity.
Qed.

Lemma sequence_Encoding_size
      {cache : Cache} {S : Type}
      enc1 enc2 n1 n2
      (enc1_sz : forall s ce t ce', enc1 s ce = Some (t, ce') -> length_ByteString t = n1)
      (enc2_sz : forall s ce t ce', enc2 s ce = Some (t, ce') -> length_ByteString t = n2)
  : forall s ce b ce',
    @sequence_Encode ByteString cache _ S enc1 enc2 s ce = Some (b, ce') -> length_ByteString b = n1 + n2.
Proof.
  unfold sequence_Encode. intros.
  destruct enc1 eqn:?; destruct_conjs; [| discriminate]; simpl in *.
  destruct enc2 eqn:?; destruct_conjs; [| discriminate]; simpl in *.
  injections. apply enc1_sz in Heqo. apply enc2_sz in Heqo0.
  rewrite length_ByteString_enqueue_ByteString. omega.
Qed.

Lemma EncodeMEquivAlignedEncodeMForChecksum
      {S A}
      (enc1' enc2' enc3' : EncodeM S ByteString)
      (encA' : A -> EncodeM S ByteString)
      (f' : ByteString -> A)
      (enc1 enc2 enc3 : forall sz, AlignedEncodeM sz)
      (encA : A -> forall sz, AlignedEncodeM sz)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> A)
      n1 n2 n3
      (enc1_OK : EncodeMEquivAlignedEncodeM enc1' enc1)
      (enc2_OK : EncodeMEquivAlignedEncodeM enc2' enc2)
      (enc3_OK : EncodeMEquivAlignedEncodeM enc3' enc3)
      (encA_OK : forall a, EncodeMEquivAlignedEncodeM (encA' a) (encA a))
      (enc1'_aligned : forall s ce t ce', enc1' s ce = Some (t, ce') -> padding t = 0)
      (enc2'_aligned : forall s ce t ce', enc2' s ce = Some (t, ce') -> padding t = 0)
      (enc3'_aligned : forall s ce t ce', enc3' s ce = Some (t, ce') -> padding t = 0)
      (encA'_aligned : forall a s ce t ce', encA' a s ce = Some (t, ce') -> padding t = 0)
      (enc1_sz_eq : forall s ce t ce',
          enc1' s ce = Some (t, ce') -> numBytes t = n1)
      (enc2_sz_eq : forall s ce t ce',
          enc2' s ce = Some (t, ce') -> numBytes t = n2)
      (enc3_sz_eq : forall s ce t ce',
          enc3' s ce = Some (t, ce') -> numBytes t = n3)
      (encA_sz_eq : forall a s ce t ce',
          encA' a s ce = Some (t, ce') -> numBytes t = n2)
      (f_OK : forall (b : ByteString)
                idx (v1 : Vector.t Core.char idx)
                m (v2 : Vector.t Core.char m)
                (v : Vector.t Core.char (idx + ((numBytes b) + m))),
          ByteString_enqueue_ByteString (build_aligned_ByteString v1)
                                        (ByteString_enqueue_ByteString b (build_aligned_ByteString v2))
          = build_aligned_ByteString v ->
          f' b = f (numBytes b) v idx)
  : EncodeMEquivAlignedEncodeM
      (fun s ce =>
         `(p, ce) <- sequence_Encode enc1' (sequence_Encode enc2' enc3') s ce;
           (fun a => (sequence_Encode enc1' (sequence_Encode (encA' a) enc3'))) (f' p) s ce)
      (fun sz => (enc1 sz >> enc2 sz >> enc3 sz) >>
                   (fun v idx s => let a := f (n1+n2+n3) v (idx-(n1+n2+n3)) in
                                EncodeAt (idx-(n1+n2+n3))
                                         ((fun a sz => enc1 sz >> encA a sz >> enc3 sz) a)
                                         v idx s))%AlignedEncodeM.
Proof.
  apply EncodeMEquivAlignedEncodeMDep; eauto; intros;
    repeat (apply Append_EncodeMEquivAlignedEncodeM; eauto).
  - eapply sequence_Encoding_padding_0 in H; eauto. intros.
    eapply sequence_Encoding_padding_0 in H0; eauto.
  - eapply sequence_Encoding_padding_0 in H; eauto. intros.
    eapply sequence_Encoding_padding_0 in H0; eauto.
  - pose proof H. eapply sequence_Encoding_size in H0.
    2 : {
      intros. rewrite length_ByteString_no_padding; eauto.
    }
    2 : {
      intros. eapply sequence_Encoding_size in H1; eauto.
      intros. rewrite length_ByteString_no_padding; eauto.
      intros. rewrite length_ByteString_no_padding; eauto.
    }
    rewrite length_ByteString_no_padding in H0; eauto. omega.
    eapply sequence_Encoding_padding_0 in H; eauto. intros.
    eapply sequence_Encoding_padding_0 in H1; eauto.
  - pose proof H. eapply sequence_Encoding_size in H0.
    2 : {
      intros. rewrite length_ByteString_no_padding; eauto.
    }
    2 : {
      intros. eapply sequence_Encoding_size in H1; eauto.
      intros. rewrite length_ByteString_no_padding; eauto.
      intros. rewrite length_ByteString_no_padding; eauto.
    }
    rewrite length_ByteString_no_padding in H0; eauto. omega.
    eapply sequence_Encoding_padding_0 in H; eauto. intros.
    eapply sequence_Encoding_padding_0 in H1; eauto.
Qed.

Lemma CorrectAlignedEncoderForChecksum
      {S}
      checksum_sz (checksum_valid : nat -> ByteString -> Prop)
      (format_A format_B : FormatM S ByteString)
      (encode_A : forall sz, AlignedEncodeM sz)
      (encode_B : forall sz, AlignedEncodeM sz)
      (encode_C' : forall sz, AlignedEncodeM sz)
      (encode_C : word checksum_sz -> forall sz, AlignedEncodeM sz)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> word checksum_sz)
      n1 n2 n3

      (enc2' : EncodeM S ByteString)
      (f' : ByteString -> word checksum_sz)
      (enc2_OK : EncodeMEquivAlignedEncodeM enc2' encode_C')
      (encA_OK : forall a, EncodeMEquivAlignedEncodeM
                        ((fun a _ ce => Some (format_checksum _ _ _ _ a, ce)) a) (encode_C a))
      (enc2'_aligned : forall s ce t ce', enc2' s ce = Some (t, ce') -> padding t = 0)
      (format_B_sz_eq : forall s ce t ce',
          format_B s ce ∋ (t, ce') -> numBytes t = n1)
      (enc2_sz_eq : forall s ce t ce',
          enc2' s ce = Some (t, ce') -> numBytes t = n2)
      (format_A_sz_eq : forall s ce t ce',
          format_A s ce ∋ (t, ce') -> numBytes t = n3)
      (f_OK : forall (b : ByteString)
                idx (v1 : Vector.t Core.char idx)
                m (v2 : Vector.t Core.char m)
                (v : Vector.t Core.char (idx + ((numBytes b) + m))),
          ByteString_enqueue_ByteString (build_aligned_ByteString v1)
                                        (ByteString_enqueue_ByteString b (build_aligned_ByteString v2))
          = build_aligned_ByteString v ->
          f' b = f (numBytes b) v idx)
      (checksum_sz_OK : checksum_sz mod 8 = 0)
      (checksum_sz_OK' : checksum_sz = 8 * n2)
      (* TODO: no f': f' bs = f  |bs| (bs) 0 *)
      (checksum_OK : forall s ce b' ce',
          enc2' s ce = Some (b', ce') ->
          forall b1 b3 ext,
            let a := f' (mappend b1 (mappend b' b3)) in
            let b2 := format_checksum _ _ _ checksum_sz a in
            checksum_valid
              (bin_measure (mappend b1 (mappend b2 b3)))
              (mappend (mappend b1 (mappend b2 b3)) ext))
      (checksum_OK' : forall s ce,
          enc2' s ce = None ->
          forall b1 b2 b3 ext,
            ~checksum_valid
              (bin_measure (mappend b1 (mappend b2 b3)))
              (mappend (mappend b1 (mappend b2 b3)) ext))
  : CorrectAlignedEncoder
      (format_B ThenChecksum checksum_valid OfSize checksum_sz ThenCarryOn format_A)
      (fun sz => encode_B sz >> encode_C' sz >> encode_A sz >>
                       (fun v idx s => let a := f (n1+n2+n3) v (idx-(n1+n2+n3)) in
                                    EncodeAt (idx-(n2+n3))
                                             (fun sz => encode_C a sz)
                                             v idx s))%AlignedEncodeM.
Proof.
  destruct encoder_A_OK as [enc3' [HA1 [HA2 HA3]]].
  destruct encoder_B_OK as [enc1' [HB1 [HB2 HB3]]].
  exists (fun s ce =>
       `(p, ce) <- sequence_Encode enc1' (sequence_Encode enc2' enc3') s ce;
       (fun a => (sequence_Encode enc1' (sequence_Encode
                                        ((fun a _ ce => Some (format_checksum _ _ _ _ a, ce)) a)
                                        enc3'))) (f' p) s ce).
  split; [| split]; intros.
  - unfold composeChecksum, sequence_Encode. split; intros; simpl in *.
    + intros [? ?]. intros.
      computes_to_inv. injections.
      destruct enc1' eqn:Henc1; [| discriminate]; destruct_conjs; simpl in *.
      destruct enc2' eqn:Henc2; [| discriminate]; destruct_conjs; simpl in *.
      destruct enc3' eqn:Henc3; [| discriminate]; destruct_conjs; simpl in *.
      destruct env, c, c1. rewrite Henc1 in H. simpl in *.
      destruct c0. rewrite Henc3 in H. simpl in *. injections.
      repeat computes_to_econstructor; eauto.
      edestruct HB1. apply H in Henc1. apply Henc1.
      repeat computes_to_econstructor; eauto. simpl.
      edestruct HA1. apply H in Henc3. apply Henc3.
      repeat computes_to_econstructor; eauto.
      simpl. apply eq_ret_compute. repeat f_equal.
    + intro. unfold Bind2 in H0.
      computes_to_inv. destruct_conjs. injections. simpl in *.
      destruct env, u0. destruct enc1' eqn:Henc1; destruct_conjs; simpl in *.
      destruct c. destruct enc2' eqn:Henc2; destruct_conjs; simpl in *.
      destruct c. destruct enc3' eqn:Henc3; destruct_conjs; simpl in *.
      destruct c. rewrite Henc1 in H. simpl in *.
      rewrite Henc3 in H. simpl in *. discriminate.
      edestruct HA1. intuition eauto. intuition eauto.
      edestruct HB1. intuition eauto.
  - destruct sequence_Encode; [| discriminate]; destruct_conjs; simpl in *.
    eapply sequence_Encoding_padding_0; try apply H; eauto.
    intros.
    eapply sequence_Encoding_padding_0; try apply H0; eauto.
    intros. simpl in *. injections.
    unfold format_checksum. rewrite encode_word'_padding. eauto.
  - eapply EncodeMEquivAlignedEncodeM_morphism; cycle 1.
    apply EncodeMEquivAlignedEncodeMForChecksum
      with (encA' := (fun a _ ce => Some (format_checksum _ _ _ _ a, ce))); eauto.
    + intros. injections.
      unfold format_checksum. rewrite encode_word'_padding. eauto.
    + intros. eapply format_B_sz_eq. eapply HB1; eauto.
    + intros. eapply format_A_sz_eq. eapply HA1; eauto.
    + intros. injections. unfold format_checksum.
      match goal with
      | |- ?a = ?b => assert (8*a = 8*b)
      end.
      rewrite <- length_ByteString_no_padding.
      rewrite length_encode_word'. rewrite measure_mempty. omega.
      rewrite encode_word'_padding. eauto. omega.
    + intros. simpl. unfold AppendAlignedEncodeM.
      destruct encode_B eqn:?; destruct_conjs; simpl in *; eauto.
      destruct encode_C' eqn:?; destruct_conjs; simpl in *; eauto.
      destruct encode_A eqn:?; destruct_conjs; simpl in *; eauto.
      unfold EncodeAt.
      destruct (encode_B sz t1 _ _ _) eqn:?; destruct_conjs; simpl in *; eauto.
      assert (t1 = t2). {
        destruct (enc1' w c2) eqn:?; destruct_conjs; simpl in *; eauto.
        2 : {
          edestruct HB3 as [_ [_ [_ ?]]]. eapply H in Heqo0. rewrite Heqo in Heqo0.
          easy.
        }
        assert (exists m, sz = (n4-(n1+n2+n3)) + (n1 + m)). {
          exists (sz + n2 + n3 - n4).
          assert (n1+n2+n3 <= n4)%nat. {
            admit.
          }
          assert (n4 <= sz)%nat. {
            admit.
          }
          omega.
        } destruct H as [m ?].

        assert (numBytes b = n1) as L1. {
          eapply format_B_sz_eq. eapply HB1; eauto.
        }
        subst.

        edestruct HB3 as [? _]. edestruct H; eauto. clear H. destruct_conjs.
        match goal with
        | H1 : encode_B _ ?a _ _ _ = _,
               H2 : encode_B _ ?a' _ _ _ = _ |- _ => assert (a' = a) as Lv
        end.
        repeat (rewrite Vector_split_append; f_equal).
        rewrite <- Lv in Heqo. rewrite Heqo in H.
        injections.
        apply build_aligned_ByteString_inj.
        rewrite <- Lv. rewrite <- H0.
        rewrite !build_aligned_ByteString_append.
        repeat f_equal. rewrite <- Lv.
        rewrite Vector_append_split_snd.
        rewrite Vector_append_split_fst.
      }

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
                          calculate_PseudoChecksum srcAddr destAddr (wordToNat udpLength) udpLength protoCode (NPeano.div idx 8))% AlignedEncodeM.
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
