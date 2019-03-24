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

Lemma Vector_append_inj {n1 n2}
      (v1 v1' : Vector.t Core.char n1) (v2 v2' : Vector.t Core.char n2)
  : v1 ++ v2 = v1' ++ v2' -> v1 = v1' /\ v2 = v2'.
Proof.
  intros.
  apply (f_equal build_aligned_ByteString) in H.
  rewrite !build_aligned_ByteString_append in H.
  split; apply build_aligned_ByteString_inj.
  eapply ByteString_enqueue_ByteString_inj; eauto.
  eapply ByteString_enqueue_ByteString_inj'; eauto.
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
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
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
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      n2
      (enc'_sz_eq : forall s ce t ce',
          enc' s ce = Some (t, ce') -> numBytes t = n2)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
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
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
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

Lemma AlignedEncoder_inv'
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n1 n3
  : forall s ce b ce'',
    enc' s ce = Some (b, ce'') ->
    forall (t1 : Vector.t Core.char n1) (t2 : Vector.t Core.char (numBytes b))
      (t3 : Vector.t Core.char n3) v idx ce',
      enc _ (t1++t2++t3) n1 s ce = Some (v, idx, ce') ->
      exists v2,
        enc _ t2 0 s ce = Some (v2, numBytes b, ce') /\
        v = t1 ++ v2 ++ t3 /\
        idx = n1 + numBytes b /\
        b = build_aligned_ByteString v2 /\
        ce'' = ce'.
Proof.
  intros.
  edestruct enc_OK as [? _].
  edestruct H1; eauto. clear H1. destruct_conjs.
  rewrite H1 in H0. injections.
  edestruct enc_OK with (idx:=0) as [? _].
  edestruct H0 with (m:=0) (v0:=t2) (v1:=Vector.nil Core.char) (v2:=Vector.nil Core.char); eauto.
  clear H0. simpl in *. destruct_conjs.
  revert H0. rewrite Vector_append_nil_r'. generalize (plus_n_O (numBytes b)).
  destruct e. simpl. intros.
  assert (b = build_aligned_ByteString x) as L. {
    rewrite <- H3.
    rewrite !build_aligned_ByteString_nil.
    eauto using mempty_left.
  }
  eexists; intuition eauto.
  apply build_aligned_ByteString_inj.
  rewrite !build_aligned_ByteString_append.
  rewrite <- H2. repeat f_equal. eauto.
Qed.

Lemma AlignedEncoder_inv
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n
  : forall (t : Vector.t Core.char n) n1 s ce v idx ce',
      enc _ t n1 s ce = Some (v, idx, ce') ->
      exists n2 n3 (t1 : Vector.t Core.char n1)
        (t2 : Vector.t Core.char n2) (t3 : Vector.t Core.char n3) v2
        (pf : n1 + (n2 + n3) = n),
        enc _ t2 0 s ce = Some (v2, n2, ce') /\
        idx = n1 + n2 /\
        t = eq_rect _ _ (t1 ++ t2 ++ t3) _ pf /\
        v = eq_rect _ _ (t1 ++ v2 ++ t3) _ pf /\
        enc' s ce = Some (build_aligned_ByteString v2, ce').
Proof.
  intros. edestruct @AlignedEncoder_some_inv' as [b [? Heqo]]; eauto.
  pose proof Heqo as Hsz. eapply AlignedEncoder_sz_destruct' in Hsz; eauto.
  revert dependent t. revert dependent v. rewrite Hsz. intros.
  destruct (Vector_append_destruct3 t) as [t1 [t2 [t3 ?]]]. subst.
  edestruct @AlignedEncoder_inv'; eauto. destruct_conjs. subst.
  repeat eexists; eauto;
    try (rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; apply Nat.eq_dec).
  congruence.
  Grab Existential Variables.
  omega.
Qed.

Lemma AlignedEncoder_extr
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n n'
  : forall (t : Vector.t Core.char n) (t' : Vector.t Core.char n')
      n1 s v ce idx ce',
    enc _ t n1 s ce = Some (v, idx, ce') ->
    enc _ (t++t') n1 s ce = Some (v++t', idx, ce').
Proof.
  intros. edestruct @AlignedEncoder_inv as [n2 [n3 [t1 [t2 [t3 [v2 ?]]]]]]; eauto.
  destruct_conjs.
  subst. simpl in *.
  match goal with
  | |- enc (?n1 + (?n2 + ?n3) + ?n4) ((?t1 ++ ?t2 ++ ?t3) ++ ?t4) ?a ?b ?c =
    Some ((?t1' ++ ?t2' ++ ?t3') ++ ?t4', ?d, ?e)=>
    assert (enc (n1 + (n2 + (n3 + n4))) (t1 ++ t2 ++ (t3 ++ t4)) a b c =
            Some ((t1' ++ t2' ++ (t3' ++ t4')), d, e))
  end.
  assert (n2 = numBytes (build_aligned_ByteString v2)) as L by eauto.
  edestruct enc_OK as [? _]. edestruct H0 with (v:=eq_rect _ _ t2 _ L); eauto. clear H0. destruct_conjs.
  destruct L. simpl in *. rewrite H0.
  repeat f_equal. apply build_aligned_ByteString_inj.
  rewrite <- H2. rewrite !build_aligned_ByteString_append. reflexivity.

  rename n' into n4. revert H0. clear. intros.
  assert (n1 + (n2 + n3) + n4 = n1 + (n2 + (n3 + n4))) by omega.
  assert (forall {A}
            (t1 : Vector.t A n1) (t2 : Vector.t A n2) (t3 : Vector.t A n3) (t4 : Vector.t A n4),
             t1 ++ t2 ++ t3 ++ t4 = eq_rect _ (Vector.t A) ((t1 ++ t2 ++ t3) ++ t4) _ H) as L. {
    clear. intros.
    assert (n2 + n3 + n4 = n2 + (n3 + n4)) by omega.
    rewrite <- (Vector_append_assoc' _ _ _ _ H0). f_equal.
    apply Vector_append_assoc.
  }
  revert H0. rewrite !L. clear. destruct H. simpl. eauto.
Qed.

Corollary AlignedEncoder_inv2
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n
  : forall (t : Vector.t Core.char n) n1 s ce v idx ce',
      enc _ t n1 s ce = Some (v, idx, ce') ->
      exists n2 n3 (t1 : Vector.t Core.char n1) (t23 : Vector.t Core.char (n2+n3)) v23
        (pf : n1 + (n2+n3) = n),
        enc _ t23 0 s ce = Some (v23, n2, ce') /\
        idx = n1 + n2 /\
        t = eq_rect _ _ (t1 ++ t23) _ pf /\
        v = eq_rect _ _ (t1 ++ v23) _ pf.
Proof.
  intros. edestruct @AlignedEncoder_inv; eauto. destruct_conjs.
  repeat eexists; eauto. eauto using AlignedEncoder_extr.
Qed.

Corollary AlignedEncoder_inv0
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n
  : forall (t : Vector.t Core.char n) s ce v ce',
    enc _ t 0 s ce = Some (v, n, ce') ->
    enc' s ce = Some (build_aligned_ByteString v, ce').
Proof.
  intros. edestruct @AlignedEncoder_inv as [n2 [n3 [t1 [t2 [t3 [v2 ?]]]]]]; eauto.
  destruct_conjs. subst. simpl in *.
  rewrite H5. repeat f_equal.
  assert (n3 = 0) by omega. subst. clear.
  apply Vector.case0 with (v:=t1). simpl.
  apply Vector.case0 with (v:=t3).
  rewrite Vector_append_nil_r'. generalize (plus_n_O n2). destruct e.
  reflexivity.
Qed.

Lemma AlignedEncoder_none_inv
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
  : forall s ce b ce'
      sz (t : Vector.t Core.char sz) n1,
    enc' s ce = Some (b, ce') ->
    enc _ t n1 s ce = None ->
    (sz < n1 + numBytes b)%nat.
Proof.
  intros.
  destruct (Nat.le_decidable (1 + sz) (numBytes b + n1)). omega.
  assert (sz = n1 + (numBytes b + (sz - (n1+numBytes b)))) by omega.
  revert dependent t. rewrite H2. intros. destruct (Vector_append_destruct3 t) as [t1 [t2 [t3 ?]]].
  subst.
  edestruct enc_OK as [? _]. edestruct H3; eauto. clear H3. destruct_conjs.
  rewrite H3 in H0. discriminate.
Qed.

Lemma AlignedEncoder_extl
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
  : forall n (t : Vector.t Core.char n) n1 s ce v ce',
    enc _ t 0 s ce = Some (v, n1, ce') ->
    forall idx (t1 : Vector.t Core.char idx),
    enc _ (t1++t) idx s ce = Some (t1++v, idx+n1, ce').
Proof.
  intros.
  match goal with
  | |- ?a = _ => destruct a eqn:?
  end. destruct_conjs.
  edestruct @AlignedEncoder_inv2 as [n2 [n3 [t2 [t23 [v23 ?]]]]]; try apply Heqo; eauto.
  destruct_conjs. assert (n2 + n3 = n) as L by omega. destruct L.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in H3 by (apply Nat.eq_dec).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in H4 by (apply Nat.eq_dec).
  subst.
  apply Vector_append_inj in H3. destruct_conjs. subst.
  edestruct @AlignedEncoder_some_inv; try apply H; eauto.
  edestruct @AlignedEncoder_some_inv; try apply H1; eauto.
  substss. injections. eauto.
  exfalso.
  edestruct @AlignedEncoder_some_inv; try apply H; eauto.
  eapply AlignedEncoder_none_inv in Heqo; eauto.
  eapply AlignedEncoder_sz_destruct' in H; eauto.
  omega.
Qed.

Lemma AlignedEncoder_fixed
      {S} {cache : Cache}
      (enc' : EncodeM S ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
      (enc'_aligned : forall s ce t ce', enc' s ce = Some (t, ce') -> padding t = 0)
      n n1
  : forall (t : Vector.t Core.char n)
      s ce v idx ce',
    enc _ t n1 s ce = Some (v, idx, ce') ->
    enc _ v n1 s ce = Some (v, idx, ce').
Proof.
  intros. edestruct @AlignedEncoder_inv as [n2 [n3 [t1 [t2 [t3 [v2 ?]]]]]]; eauto.
  destruct_conjs.
  subst. simpl in *.
  assert (n2 = numBytes (build_aligned_ByteString v2)) as L by eauto.
  match goal with
  | |- ?x = _ => destruct x eqn:?
  end. destruct_conjs.
  edestruct @AlignedEncoder_inv'; try apply Heqo; eauto. destruct_conjs.
  subst. repeat f_equal. eauto using build_aligned_ByteString_inj.
  exfalso. eapply AlignedEncoder_none_inv in Heqo; eauto.
  omega.
Qed.

Lemma AlignedEncoder_append_inv
      {S} {cache : Cache}
      (enc1' : EncodeM S ByteString)
      (enc1 : forall sz, AlignedEncodeM sz)
      (enc1_OK : EncodeMEquivAlignedEncodeM enc1' enc1)
      (enc1'_aligned : forall s ce t ce', enc1' s ce = Some (t, ce') -> padding t = 0)
      (enc2' : EncodeM S ByteString)
      (enc2 : forall sz, AlignedEncodeM sz)
      (enc2_OK : EncodeMEquivAlignedEncodeM enc2' enc2)
      (enc2'_aligned : forall s ce t ce', enc2' s ce = Some (t, ce') -> padding t = 0)
      n
  : forall (t : Vector.t Core.char n) s ce v idx ce',
    (enc1 n >> enc2 n)%AlignedEncodeM t 0 s ce = Some (v, idx, ce') ->
    exists n1 n2 n3 (t1 : Vector.t Core.char n1) (t23 : Vector.t Core.char (n2+n3)) v1 v23 ce''
      (pf : n1 + (n2+n3) = n),
      enc1 _ t1 0 s ce = Some (v1, n1, ce'') /\
      enc2 _ t23 0 s ce'' = Some (v23, n2, ce') /\
      idx = n1 + n2 /\
      t = eq_rect _ _ (t1 ++ t23) _ pf /\
      v = eq_rect _ _ (v1 ++ v23) _ pf.
Proof.
  unfold AppendAlignedEncodeM. intros.
  destruct enc1 eqn:?; [| discriminate]; destruct_conjs; simpl in *.
  destruct enc2 eqn:?; [| discriminate]; destruct_conjs; simpl in *.
  injections. rename n0 into n1. rename t0 into v0.
  edestruct @AlignedEncoder_inv as [n1' [n23 [tnil [t1 [t23 [v1 ?]]]]]]; try apply enc1_OK; eauto.
  destruct_conjs. subst. simpl in *.
  revert dependent tnil. intros tnil.
  apply Vector.case0 with (v:=tnil). clear tnil. simpl. intros. rename n1' into n1.
  edestruct @AlignedEncoder_inv2 as [n2 [n3 [v1' [t23' [v23 ?]]]]]; try apply enc2_OK; eauto.
  destruct_conjs. assert (n2 + n3 = n23) by omega. destruct H6.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in H3 by (apply Nat.eq_dec).
  rewrite <- Eqdep_dec.eq_rect_eq_dec in H5 by (apply Nat.eq_dec).
  subst. apply Vector_append_inj in H3. destruct_conjs. subst.
  repeat eexists; eauto.
  instantiate (1:=eq_refl). all : eauto.
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

Lemma sequence_Encoding_inv
      {cache : Cache} {S : Type}
      enc1 enc2
  : forall s ce b ce',
    @sequence_Encode ByteString cache _ S enc1 enc2 s ce = Some (b, ce') ->
    exists b1 b2 ce1,
      enc1 s ce = Some (b1, ce1) /\
      enc2 s ce1 = Some (b2, ce') /\
      b = mappend b1 b2.
Proof.
  unfold sequence_Encode. intros.
  destruct enc1 eqn:?; destruct_conjs; [| discriminate]; simpl in *.
  destruct enc2 eqn:?; destruct_conjs; [| discriminate]; simpl in *.
  injections. eauto 10.
Qed.

Definition EncodeAgain {S : Type} {cache : Cache}
           {n}
           (a : @AlignedEncodeM _ S n)
           (b : nat -> @AlignedEncodeM _ S n)
  : @AlignedEncodeM _ S n :=
  fun v idx s c => (Ifopt a v idx s c  as a' Then
                    (Ifopt b (snd (fst a')) (fst (fst a')) idx s c as b' Then
                       Some (fst (fst b'), snd (fst a'), snd b')
                       Else None)
                    Else None).

Lemma EncodeMEquivAlignedEncodeMDep
      {S A}
      (enc1' : EncodeM S ByteString)
      (enc2' : A -> EncodeM S ByteString)
      (f' : ByteString -> A)
      (enc1 : forall sz, AlignedEncodeM sz)
      (enc2 : A -> forall sz, AlignedEncodeM sz)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> A)
      (enc1_OK : EncodeMEquivAlignedEncodeM enc1' enc1)
      (enc2_OK : forall a, EncodeMEquivAlignedEncodeM (enc2' a) (enc2 a))
      (enc1'_aligned : forall s ce t ce', enc1' s ce = Some (t, ce') -> padding t = 0)
      (enc2'_aligned : forall a s ce t ce', enc2' a s ce = Some (t, ce') -> padding t = 0)
      (enc'_sz_eq : forall s a ce t1 ce1 t2 ce2,
          enc1' s ce = Some (t1, ce1) ->
          enc2' a s ce = Some (t2, ce2) ->
          bin_measure t1 = bin_measure t2)
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
         `(p, _) <- enc1' s ce;
           enc2' (f' p) s ce)
      (fun sz => EncodeAgain (enc1 sz)
                          (fun idx' v idx s =>
                             enc2 (f (idx'-idx) v idx) sz v idx s))%AlignedEncodeM.
Proof.
  repeat split; intros; simpl in *. {
    destruct enc1' eqn:?; [| discriminate]; destruct_conjs; simpl in *.
    assert (numBytes b = numBytes t) as L1. {
      assert (bin_measure b = bin_measure t) by eauto.
      rewrite !length_ByteString_no_padding in H1 by eauto.
      omega.
    }

    edestruct enc1_OK as [? _]. specialize (H1 _ _ Heqe).
    revert H1. rewrite L1. intros.
    edestruct (H1 (enc1'_aligned _ _ _ _ Heqe) v1 v _ v2); eauto. clear H1. destruct_conjs.

    assert (exists v, v1 ++ v ++ v2 = x) as L2. {
      destruct L1.
      edestruct @AlignedEncoder_inv'; eauto; eauto. destruct_conjs.
      eauto.
    } destruct L2 as [v' L2].

    edestruct enc2_OK as [? _]. specialize (H3 _ _ H).
    edestruct H3; eauto. clear H3. destruct_conjs.
    rewrite L2 in H3.

    eexists. split; eauto. unfold EncodeAgain.
    rewrite H1. simpl.
    match goal with
    | H : enc2 ?a _ _ _ _ _ = _ |- context[enc2 ?a' _ _ _ _ _] =>
      replace a' with a
    end.
    rewrite H3. simpl. reflexivity.
    destruct L1. replace (idx + numBytes b - idx) with (numBytes b) by omega. eauto.
  } {
    destruct enc1' eqn:?; [| discriminate]; destruct_conjs; simpl in *.
    edestruct enc1_OK as [_ [? _]]. eapply H1 in Heqe.
    unfold EncodeAgain. rewrite Heqe. reflexivity.
    assert (bin_measure b = bin_measure t) as L1 by eauto. simpl in *.
    congruence.
  } {
    destruct enc1' eqn:?; [| discriminate]; destruct_conjs; simpl in *.
    exfalso. eauto.
  } {
    destruct enc1' eqn:?; destruct_conjs; simpl in *; unfold EncodeAgain. {
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
      end. rewrite H2. simpl.
      edestruct enc2_OK as [_ [_ [_ ?]]]. rewrite H4; eauto.
      simpl. rewrite <- H. f_equal.
      replace (idx + numBytes b - idx) with (numBytes b) by omega. symmetry.
      eauto.
      repeat (rewrite Vector_split_append; f_equal).
    } {
      edestruct (enc1_OK env s idx) as [_ [_ [_ ?]]]; eauto. eapply H0 in Heqe; eauto.
      rewrite Heqe. reflexivity.
    }
  }
Qed.

Ltac destruct_unit :=
  repeat match goal with
         | v : () |- _ => destruct v
         end.

Ltac solve_seq_padding :=
  repeat (intros; match goal with
                  | H : sequence_Encode ?e1 ?e2 _ _ = Some (?t, _) |- padding ?t = 0 =>
                    eapply sequence_Encoding_padding_0 in H; eauto
                  end).

Lemma EncodeMEquivAlignedEncodeMForChecksum
      {S A}
      (enc1' enc2' enc3' : EncodeM S ByteString)
      (encA' : A -> EncodeM S ByteString)
      (f' : ByteString -> A)
      (enc1 enc2 enc3 : forall sz, AlignedEncodeM sz)
      (encA : A -> forall sz, AlignedEncodeM sz)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> A)
      (enc1_OK : EncodeMEquivAlignedEncodeM enc1' enc1)
      (enc2_OK : EncodeMEquivAlignedEncodeM enc2' enc2)
      (enc3_OK : EncodeMEquivAlignedEncodeM enc3' enc3)
      (encA_OK : forall a, EncodeMEquivAlignedEncodeM (encA' a) (encA a))
      (enc1'_aligned : forall s ce t ce', enc1' s ce = Some (t, ce') -> padding t = 0)
      (enc2'_aligned : forall s ce t ce', enc2' s ce = Some (t, ce') -> padding t = 0)
      (enc3'_aligned : forall s ce t ce', enc3' s ce = Some (t, ce') -> padding t = 0)
      (encA'_aligned : forall a s ce t ce', encA' a s ce = Some (t, ce') -> padding t = 0)
      (enc'_sz_eq : forall s a ce t1 ce1 t2 ce2,
          enc2' s ce = Some (t1, ce1) ->
          encA' a s ce = Some (t2, ce2) ->
          bin_measure t1 = bin_measure t2)
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
         `(p, _) <- sequence_Encode enc1' (sequence_Encode enc2' enc3') s ce;
           (fun a => (sequence_Encode enc1' (sequence_Encode (encA' a) enc3'))) (f' p) s ce)
      (fun sz => EncodeAgain (enc1 sz >> enc2 sz >> enc3 sz)
                          (fun idx' v idx s =>
                             (fun a sz => enc1 sz >> encA a sz >> enc3 sz)
                               (f (idx'-idx) v idx) sz v idx s))%AlignedEncodeM.
Proof.
  apply EncodeMEquivAlignedEncodeMDep; eauto; intros;
    repeat (apply Append_EncodeMEquivAlignedEncodeM; eauto);
    solve_seq_padding.
  apply sequence_Encoding_inv in H.
  apply sequence_Encoding_inv in H0. destruct_conjs.
  apply sequence_Encoding_inv in H9.
  apply sequence_Encoding_inv in H4. destruct_conjs.
  subst. rewrite !mappend_measure.
  simpl in *. destruct_unit.
  substss. injections. eauto.
Qed.

Definition f_bit_aligned_free {A} (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> A)
  : ByteString -> A :=
  fun bs => f (numBytes bs) (byteString bs) 0.

Lemma CorrectAlignedEncoderForChecksum
      {S}
      checksum_sz (checksum_valid : nat -> ByteString -> Prop)
      (format_A format_B : FormatM S ByteString)
      (encode_A encode_B : forall sz, AlignedEncodeM sz)
      (encode_C' : forall sz, AlignedEncodeM sz)
      (encode_C : word checksum_sz -> forall sz, AlignedEncodeM sz)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> word checksum_sz)
      (f_OK : forall idx n m (t : Vector.t Core.char n)
                (v1 : Vector.t Core.char idx) (v2 : Vector.t Core.char m),
         f n t 0 = f n (v1 ++ t ++ v2) idx)
      (enc2' : EncodeM S ByteString)
      (enc2_OK : EncodeMEquivAlignedEncodeM enc2' encode_C')
      (encode_C_OK : forall a, EncodeMEquivAlignedEncodeM
                            ((fun a _ ce => Some (format_checksum _ _ _ _ a, ce)) a) (encode_C a))
      (enc2'_aligned : forall s ce t ce', enc2' s ce = Some (t, ce') -> padding t = 0)
      n1
      (format_B_sz_eq : forall s ce t ce',
          format_B s ce ∋ (t, ce') -> numBytes t = n1)
      (checksum_sz_OK : checksum_sz mod 8 = 0)
      (checksum_sz_OK' : forall s ce t ce', enc2' s ce = Some (t, ce') ->
                                       checksum_sz = bin_measure t)
      (checksum_OK : forall s ce b' ce',
          enc2' s ce = Some (b', ce') ->
          forall b1 b3 ext,
            let a := (f_bit_aligned_free f) (mappend b1 (mappend b' b3)) in
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
      (fun sz => EncodeAgain (encode_B sz >> encode_C' sz >> encode_A sz)
                          (fun idx' v idx s =>
                             encode_C (f (idx'-idx) v idx) sz v (idx+n1) s))%AlignedEncodeM.
Proof.
  destruct encoder_A_OK as [enc3' [HA1 [HA2 HA3]]].
  destruct encoder_B_OK as [enc1' [HB1 [HB2 HB3]]].
  exists (fun s ce =>
       `(p, _) <- sequence_Encode enc1' (sequence_Encode enc2' enc3') s ce;
       (fun a => (sequence_Encode enc1' (sequence_Encode
                                        ((fun a _ ce => Some (format_checksum _ _ _ _ a, ce)) a)
                                        enc3'))) ((f_bit_aligned_free f) p) s ce).
  split; [| split]; intros.
  - unfold composeChecksum, sequence_Encode. split; intros; simpl in *.
    + intros [? ?]. intros.
      computes_to_inv. injections.
      destruct enc1' eqn:Henc1; [| discriminate]; destruct_conjs; simpl in *.
      destruct enc2' eqn:Henc2; [| discriminate]; destruct_conjs; simpl in *.
      destruct enc3' eqn:Henc3; [| discriminate]; destruct_conjs; simpl in *.
      destruct_unit.
      rewrite Henc3 in H. simpl in *. injections.
      repeat computes_to_econstructor; eauto.
      edestruct HB1. apply H in Henc1. apply Henc1.
      repeat computes_to_econstructor; eauto. simpl.
      edestruct HA1. apply H in Henc3. apply Henc3.
      repeat computes_to_econstructor; eauto.
      simpl. apply eq_ret_compute. repeat f_equal.
    + intro. unfold Bind2 in H0.
      computes_to_inv. destruct_conjs. injections. simpl in *. destruct_unit.
      destruct enc1' eqn:Henc1; destruct_conjs; simpl in *; destruct_unit.
      destruct enc2' eqn:Henc2; destruct_conjs; simpl in *; destruct_unit.
      destruct enc3' eqn:Henc3; destruct_conjs; simpl in *; destruct_unit.
      discriminate.
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
    + intros. injections. unfold format_checksum.
      rewrite length_encode_word'. rewrite measure_mempty.
      apply checksum_sz_OK' in H. omega.
    + unfold f_bit_aligned_free. instantiate (1:=f). intros.
      assert (padding b = 0) as L1. {
        apply (f_equal padding) in H. simpl in H.
        rewrite padding_ByteString_enqueue_aligned_ByteString in H; eauto.
        rewrite ByteString_enqueue_ByteString_padding_eq in H. simpl padding in H.
        rewrite (Nat.mod_add _ 0 8) in H; eauto.
        rewrite Nat.mod_small in H; eauto.
        destruct b. simpl in *. auto.
      }
      assert (b = build_aligned_ByteString (byteString b)) as L2. {
        revert L1. clear. intros.
        destruct b. simpl. unfold build_aligned_ByteString. simpl in *.
        subst. f_equal. eauto using shatter_word_0.
        apply Core.le_uniqueness_proof.
      }
      revert L2 H. revert v.
      generalize (byteString b). generalize (numBytes b). intros. rewrite L2 in H.
      rewrite <- !build_aligned_ByteString_append in H.
      apply build_aligned_ByteString_inj in H. subst.
      eauto.
    + intros. unfold EncodeAgain.
      set (fun sz => encode_C' sz >> encode_A sz)%AlignedEncodeM as enc'.
      set (fun sz => encode_B sz >> enc' sz)%AlignedEncodeM as enc.
      match goal with
      | |- context[Ifopt ?b _ _ _ _ as _ Then _ Else _] => replace b with (enc sz) by reflexivity
      end.
      destruct enc eqn:?; eauto.
      destruct_conjs. simpl. unfold AppendAlignedEncodeM.

      edestruct @AlignedEncoder_inv2 as [n2 [n3 [t1 [t23 [v23 ?]]]]]; try apply Heqa.
      apply Append_EncodeMEquivAlignedEncodeM. 2 : eauto. eauto.
      apply Append_EncodeMEquivAlignedEncodeM. 2 : eauto. eauto. eauto.
      solve_seq_padding.
      destruct_conjs. subst. simpl in *.

      edestruct @AlignedEncoder_append_inv with (enc1:=encode_B)
        as [nB [nC [nC3 [tB [tC3 [vB [vC3 [?ce ?]]]]]]]].
      5 : apply H0.
      3 : apply Append_EncodeMEquivAlignedEncodeM. all : eauto.
      solve_seq_padding. destruct_conjs.
      subst. simpl in *. destruct H. simpl in *.

      assert (encode_B (idx + (nB + (nC + nC3))) (t1 ++ vB ++ vC3) idx w c =
              Some (t1 ++ vB ++ vC3, idx+nB, ce)). {
        assert (idx + nB + (nC + nC3) = idx + (nB + (nC + nC3))) as L by omega.
        rewrite Vector_append_assoc with (H:=L). destruct L. simpl.
        epose proof AlignedEncoder_extr as H'. eapply H'; eauto. clear H'.
        eapply @AlignedEncoder_fixed; eauto.
        eapply AlignedEncoder_extl; eauto.
      } rewrite H. simpl.

      assert (nB = n1). {
        erewrite <- format_B_sz_eq; eauto.
        epose proof AlignedEncoder_inv0 as L. eapply L in H1; eauto. clear L.
        instantiate (1:=build_aligned_ByteString vB). reflexivity.
        eapply HB1; eauto. eauto using AlignedEncoder_inv0.
      } subst n1.
      destruct_unit. destruct encode_C eqn:?; eauto. destruct_conjs. simpl in *.

      edestruct @AlignedEncoder_append_inv with (enc1:=encode_C')
        as [nC' [nA [nA3 [tC [tA3 [vC [vA3 [?ce ?]]]]]]]]; try apply H2; eauto.
      destruct_conjs.
      subst. simpl in *. destruct H3. simpl in *. rename nC' into nC.

      match goal with
      | H : encode_C ?a _ _ _ _ _ = _ |- _ =>
        edestruct @AlignedEncoder_inv with (enc:=(encode_C a))
          as [nC' [n3' [t1C [tC' [tC3 [vC' ?]]]]]]
      end; eauto.
      intros. simpl in *. injections.
      unfold format_checksum. rewrite encode_word'_padding. eauto.
      destruct_conjs.

      assert (nC = nC'). {
        injections.
        assert (checksum_sz = 8 * nC').
        eapply (f_equal bin_measure) in H12. simpl in *.
        unfold format_checksum in H12.
        rewrite length_encode_word' in H12. rewrite measure_mempty in H12.
        unfold length_ByteString in H12. simpl in H12. omega.
        assert (checksum_sz = 8 * nC).
        epose proof AlignedEncoder_inv0 as L. eapply L in H4; eauto. clear L.
        apply checksum_sz_OK' in H4.
        unfold length_ByteString in H4. simpl in H4. omega.
        omega.
      } subst nC'.

      assert (n3' = nA + nA3) as L by omega. subst n3'.
      assert (encode_A (idx + (nB + (nC + (nA + nA3)))) t n w c =
              Some (t, n+nA, c)). {
        rewrite (Vector_append_assoc _ _ _ H3) in H8.
        clear Heqa0. destruct H3. simpl in *.
        subst. apply Vector_append_inj in H8. destruct_conjs.
        apply Vector_append_inj in H7. destruct_conjs. subst.
        assert (idx + nB + nC + (nA + nA3) = idx + nB + (nC + (nA + nA3))) as L by omega.
        rewrite (Vector_append_assoc _ _ _ L). destruct L. simpl.
        epose proof AlignedEncoder_extl as L. eapply L; eauto. clear L.
        destruct_unit.
        eapply @AlignedEncoder_fixed; eauto.
      } rewrite H11. simpl. reflexivity.
      Grab Existential Variables.
      eauto.
Qed.

Definition encode_word_16_const
           {S : Type}
  : word (2*8) -> forall sz, AlignedEncodeM (S:=S) sz :=
  fun w sz v idx _ ce => SetCurrentBytes v idx w ce.

Definition encode_word_16_0 {S : Type} := @encode_word_16_const S (wzero 16).

Lemma AlignedEncoder_const
      {S A} {cache : Cache}
      (enc' : EncodeM A ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall a, EncodeMEquivAlignedEncodeM (S:=S)
           (fun _ ce => enc' a ce)
           (fun sz v n _ ce => enc sz v n a ce).
Proof.
  intros.
  Admitted.

Lemma CorrectAlignedEncoderForChecksum'
      {S}
      (checksum_valid : nat -> ByteString -> Prop)
      (format_A format_B : FormatM S ByteString)
      (encode_A encode_B : forall sz, AlignedEncodeM sz)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> word 16)
      (f_OK : forall idx n m (t : Vector.t Core.char n)
                (v1 : Vector.t Core.char idx) (v2 : Vector.t Core.char m),
         f n t 0 = f n (v1 ++ t ++ v2) idx)
      n1
      (format_B_sz_eq : forall s ce t ce',
          format_B s ce ∋ (t, ce') -> numBytes t = n1)
      (checksum_OK :
         forall b1 b3 ext,
           let a := (f_bit_aligned_free f)
                      (mappend b1 (mappend (format_checksum _ _ _ _ (wzero 16)) b3)) in
           let b2 := format_checksum _ _ _ 16 a in
           checksum_valid
             (bin_measure (mappend b1 (mappend b2 b3)))
             (mappend (mappend b1 (mappend b2 b3)) ext))
  : CorrectAlignedEncoder
      (format_B ThenChecksum checksum_valid OfSize 16 ThenCarryOn format_A)
      (fun sz => EncodeAgain (encode_B sz >> encode_word_16_0 sz >> encode_A sz)
                          (fun idx' v idx s =>
                             encode_word_16_const (f (idx'-idx) v idx) sz v (idx+n1) s))%AlignedEncodeM.
Proof.
  destruct CorrectAlignedEncoderForFormatNChar
    with (sz:=2) as [enc' [Hc1 [Hc2 Hc3]]]; eauto.
  eapply CorrectAlignedEncoderForChecksum; intros; eauto. {
    eapply AlignedEncoder_const in Hc3. apply Hc3.
  } {
    admit.
  } {
    admit.
  } {
    admit.
  } {
    admit.
  } {
    admit.
  }
Qed.

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
