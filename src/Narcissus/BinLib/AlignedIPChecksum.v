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
          format_B s ce ∋ (t, ce') -> bin_measure t = n1)
      (checksum_sz_OK : checksum_sz mod 8 = 0)
      (checksum_sz_OK' : forall s ce t ce', enc2' s ce = Some (t, ce') ->
                                       checksum_sz = bin_measure t)
      (checksum_OK : forall s ce b' ce',
          enc2' s ce = Some (b', ce') ->
          forall b1 b3 ext,
            (exists s ce ce', format_B s ce ∋ (b1, ce')) ->
            (exists s ce ce', format_A s ce ∋ (b3, ce')) ->
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
                             encode_C (f (idx'-idx) v idx) sz v (idx+n1/8) s))%AlignedEncodeM.
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
      intros. eapply checksum_OK; eauto.
      repeat eexists. simpl. apply HB1 in Henc1. eauto.
      repeat eexists. simpl. apply HA1 in Henc3. eauto.
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

      assert (nB = n1/8). {
        erewrite <- format_B_sz_eq; eauto.
        epose proof AlignedEncoder_inv0 as L. eapply L in H1; eauto. clear L.
        instantiate (1:=build_aligned_ByteString vB).
        rewrite length_ByteString_no_padding; eauto.
        rewrite Nat.mul_comm.
        rewrite Nat.div_mul by auto.
        reflexivity.
        eapply HB1; eauto. eauto using AlignedEncoder_inv0.
      } destruct H3.
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

Definition encode_word_const
           {S : Type}
           {n}
  : word (n*8) -> forall sz, AlignedEncodeM (S:=S) sz :=
  fun w sz v idx _ ce => SetCurrentBytes v idx w ce.

Definition encode_word_16_const {S : Type} := @encode_word_const S 2.

Definition encode_word_16_0 {S : Type} := @encode_word_16_const S (wzero 16).

Lemma format_word_is_encode_word {T}
      {cache : Cache} {cacheAddNat : CacheAdd cache nat}
      {monoid : Monoid T} {monoidUnit : QueueMonoidOpt monoid bool}
      {n} (enc : EncodeM (word n) T)
  : (forall s env,
        (forall t env', enc s env = Some (t, env')
                   -> refine (format_word s env) (ret (t, env')))
        /\ (enc s env = None ->
           forall benv', ~ computes_to (format_word s env) benv')) ->
    forall s env, enc s env = Some (encode_word' _ s mempty, addE env n).
Proof.
  intros. destruct enc eqn:?; destruct_conjs.
  - apply H in Heqe.
    eapply Return_inv in Heqe; eauto. congruence.
  - exfalso. eapply H; eauto.
    computes_to_econstructor; eauto.
Qed.

Lemma EncodeMEquivAlignedEncodeM_const
      {S A} {cache : Cache}
      (enc' : EncodeM A ByteString)
      (enc : forall sz, AlignedEncodeM sz)
      (enc_OK : EncodeMEquivAlignedEncodeM enc' enc)
  : forall a, EncodeMEquivAlignedEncodeM (S:=S)
           (fun _ ce => enc' a ce)
           (fun sz v n _ ce => enc sz v n a ce).
Proof.
  intros. repeat split; simpl; intros;
            edestruct enc_OK as [? [? [? ?]]]; eauto.
Qed.

Lemma EncodeMEquivAlignedEncodeM_word_const
      {S}
      {n}
  : forall (w : word (n*8)),
    EncodeMEquivAlignedEncodeM
      (fun (_ : S) env => Some (encode_word' _ w mempty, addE env (n*8)))
      (encode_word_const w).
Proof.
  intros.
  destruct CorrectAlignedEncoderForFormatNChar with (sz:=n); eauto. destruct_conjs.
  eapply EncodeMEquivAlignedEncodeM_const in H1.
  match goal with
  | H : EncodeMEquivAlignedEncodeM ?a _ |- EncodeMEquivAlignedEncodeM ?b _ =>
    replace b with a
  end. eauto.
  extensionality s. extensionality ce.
  eauto using format_word_is_encode_word.
Qed.

Definition AlignedEncoderForChecksum
      {S}
      n1
      (encode_B encode_A : forall sz, AlignedEncodeM sz)
      (f : nat -> forall {sz}, Vector.t (word 8) sz -> nat -> word 16)
  := (fun sz => EncodeAgain (encode_B sz >> encode_word_16_0 sz >> encode_A sz)
                         (fun idx' v idx (s : S) =>
                            encode_word_16_const (f (idx'-idx) v idx) sz v (idx+n1/8) s))%AlignedEncodeM.

Local Opaque encode_word'.
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
          format_B s ce ∋ (t, ce') -> bin_measure t = n1)
      (checksum_OK :
         forall b1 b3 ext,
            (exists s ce ce', format_B s ce ∋ (b1, ce')) ->
            (exists s ce ce', format_A s ce ∋ (b3, ce')) ->
           let a := (f_bit_aligned_free f)
                      (mappend b1 (mappend (format_checksum _ _ _ _ (wzero 16)) b3)) in
           let b2 := format_checksum _ _ _ 16 a in
           checksum_valid
             (bin_measure (mappend b1 (mappend b2 b3)))
             (mappend (mappend b1 (mappend b2 b3)) ext))
  : CorrectAlignedEncoder
      (format_B ThenChecksum checksum_valid OfSize 16 ThenCarryOn format_A)
      (AlignedEncoderForChecksum n1 encode_B encode_A f).
Proof.
  unfold AlignedEncoderForChecksum.
  eapply CorrectAlignedEncoderForChecksum; intros;
    eauto using (EncodeMEquivAlignedEncodeM_word_const (n:=2));
    simpl in H; match goal with
                | H : Some (?a, _) = Some (?b, _) |- _ => replace b with a in * by congruence
                | H : Some _ = None |- _ => discriminate H
                end.
  - apply encode_word'_padding.
  - rewrite length_encode_word'. reflexivity.
  - unfold format_checksum in *. eauto.
Qed.

Lemma ByteBuffer_checksum_bound_tail
      {sz}
  : forall (v : ByteBuffer.t sz) (idx : nat) (v' : ByteBuffer.t idx),
    InternetChecksum.ByteBuffer_checksum_bound sz (v++v') =
    InternetChecksum.ByteBuffer_checksum_bound sz v.
Proof.
  simpl. intros.
  rewrite <- !InternetChecksum_To_ByteBuffer_Checksum'.
  f_equal. rewrite build_aligned_ByteString_append.
  replace (sz * 8) with (bin_measure (build_aligned_ByteString v)).
  rewrite ByteString2ListOfChar_Over; eauto.
  simpl. unfold length_ByteString. simpl. omega.
Qed.

Lemma padding_append_0
      b1 b2
  : padding b1 = 0 -> padding b2 = 0 -> padding (mappend b1 b2) = 0.
Proof.
  intros.
  rewrite padding_ByteString_enqueue_aligned_ByteString; eauto.
Qed.

Lemma refine_ret_ret_eq
      {A} (a b : A)
  : refine (ret a) (ret b) -> a = b.
Proof.
  eauto using Return_inv.
Qed.

Lemma checksum_app_0
  : forall l, checksum (wzero 8 :: wzero 8 :: l)%list = checksum l.
Proof.
  intros. replace (wzero 8 :: (wzero 8 :: l))%list with ([wzero 8; wzero 8] ++ l)%list by reflexivity.
  rewrite checksum_split; simpl; eauto.
  exists 1. reflexivity.
Qed.

Lemma ByteString2ListOfChar_format_checksum
      (w : word 16)
  : let b := format_checksum _ _ _ _ w in
    ByteString2ListOfChar (bin_measure b) b = [hi8 w; lo8 w]%list.
Proof.
  simpl.
  assert (refine (format_word w ()) (ret (build_aligned_ByteString ([hi8 w; lo8 w]), ()))). {
    etransitivity.
    2 : {
      pose proof AlignedFormat2Char.
      apply H; eauto. higher_order_reflexivity.
    }
    autorewrite with monad laws.
    higher_order_reflexivity.
  }
  unfold format_word, format_checksum in *. simpl in *.
  apply refine_ret_ret_eq in H. injections. rewrite H0.
  rewrite ByteString2ListOfChar_eq'; eauto.
  Grab Existential Variables.
  simpl. exact ().
Qed.

Local Arguments Nat.modulo : simpl never.
Lemma ByteString_mod_16_padding
  : forall b, bin_measure b mod 16 = 0 -> padding b = 0.
Proof.
  intros.
  rewrite padding_eq_mod_8. simpl in *.
  apply Nat.mod_divides; eauto.
  apply Nat.mod_divides in H; eauto.
  destruct H as [x ?]. rewrite H. clear.
  exists (2*x). omega.
Qed.

Fixpoint calculate_aligned_IPchecksum'
         m
         {sz}
         (v : t Core.char sz) (idx : nat)
         {struct idx}
  := match idx with
     | 0 =>
       InternetChecksum.ByteBuffer_checksum_bound m v
     | S idx' =>
       match v with
       | Vector.cons _ _ v' => calculate_aligned_IPchecksum' m v' idx'
       | _ => wzero _
       end
     end.

Lemma calculate_aligned_IPchecksum_front
      m
      {sz}
  : forall (v : ByteBuffer.t sz) (idx : nat) (v' : ByteBuffer.t idx),
    calculate_aligned_IPchecksum' m (v'++v) idx =
    calculate_aligned_IPchecksum' m v 0.
Proof.
  induction v'; eauto.
Qed.

Lemma calculate_aligned_IPchecksum_tail
      {sz}
  : forall (v : ByteBuffer.t sz) (idx : nat) (v' : ByteBuffer.t idx),
    calculate_aligned_IPchecksum' sz (v++v') 0 =
    calculate_aligned_IPchecksum' sz v 0.
Proof.
  intros. simpl.
  rewrite ByteBuffer_checksum_bound_tail. reflexivity.
Qed.

Definition calculate_aligned_IPchecksum
         m
         {sz}
         (v : t Core.char sz) (idx : nat)
  := wnot (calculate_aligned_IPchecksum' m v idx).

Lemma CorrectAlignedEncoderForIPChecksumThenC
      {S}
      (format_A format_B : FormatM S ByteString)
      (encode_A : forall sz, AlignedEncodeM sz)
      (encode_B : forall sz, AlignedEncodeM sz)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
      n1
      (format_B_sz_OK' : forall (s : S) (b : ByteString) (env env' : CacheFormat),
          format_B s env ∋ (b, env') -> bin_measure b = n1)
      (format_B_sz_OK : n1 mod 16 = 0)
      (len_format_A : S -> nat)
      (format_A_sz_OK' : forall (s : S) (b : ByteString) (env env' : CacheFormat),
          format_A s env ∋ (b, env') -> bin_measure b = len_format_A s)
      (format_A_sz_OK : forall (s : S), len_format_A s mod 8 = 0)
  : CorrectAlignedEncoder
      (format_B ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn format_A)
      (AlignedEncoderForChecksum n1 encode_B encode_A calculate_aligned_IPchecksum).
Proof.
  eapply CorrectAlignedEncoderForChecksum';
    unfold calculate_aligned_IPchecksum; eauto; intros.
  - rewrite calculate_aligned_IPchecksum_front.
    rewrite calculate_aligned_IPchecksum_tail. reflexivity.
  - destruct_conjs.
    assert (bin_measure b1 mod 16 = 0) as L1 by (erewrite format_B_sz_OK'; eauto).
    assert (padding b3 = 0) as L2 by (rewrite padding_eq_mod_8; erewrite format_A_sz_OK'; eauto).
    unfold f_bit_aligned_free, IPChecksum_Valid, onesComplement. simpl in *.
    rewrite <- InternetChecksum_To_ByteBuffer_Checksum'.
    rewrite ByteString2ListOfChar_Over.
    rewrite !build_aligned_ByteString_byteString_idem.
    match goal with
    | |- context [ByteString2ListOfChar (numBytes ?a * 8) ?a] =>
      replace (numBytes a * 8) with (bin_measure a)
    end.
    2 : rewrite length_ByteString_no_padding; try omega.
    rewrite !ByteString2ListOfChar_append.
    rewrite !ByteString2ListOfChar_format_checksum.

    assert (forall n, n mod 16 = 0 ->
                 forall b, exists x, |ByteString2ListOfChar n b| = 2 * x) as L. {
      clear. intros.
      apply Nat.mod_divides in H; eauto. destruct H as [x ?].
      replace (16 * x) with (8 * (2*x)) in * by omega.
      subst.
      rewrite ByteString2ListOfChar_len. eauto.
    }
    destruct L with (n:=bin_measure b1) (b:=b1) as [x1 ?]; eauto.
    clear L.
    set (ByteString2ListOfChar (bin_measure b1) b1) as l1 in *.
    set (ByteString2ListOfChar (bin_measure b3) b3) as l3 in *.

    unfold hi8, lo8.
    rewrite split1_wzero, split2_wzero.
    match goal with
    | |- context [wnot (checksum ?a)] =>
      assert (checksum a = checksum (l1 ++ l3))%list as L
    end. {
      rewrite !checksum_split; eauto. exists 1. reflexivity.
    } rewrite L. clear L.
    rewrite checksum_split; eauto.
    rewrite checksum_split; eauto.
    match goal with
    | |- context [?a ^1+ (?b ^1+ ?c)] =>
        assert (a ^1+ (b ^1+ c) = b ^1+ a ^1+ c) as L
    end. {
      rewrite <- !OneC_plus_assoc.
      rewrite OneC_plus_comm.
      rewrite <- !OneC_plus_assoc.
      f_equal.
      rewrite OneC_plus_comm.
      reflexivity.
    } rewrite L. clear L.
    rewrite <- !checksum_split; eauto.
    apply checksum_correct.
    simpl. exists (1+x1). unfold Core.char in *. rewrite H7. omega.
    simpl. exists 1. omega.
    simpl. exists 1. omega.
    all : destruct_conjs; simpl.
    all : repeat match goal with
                 | |- padding (ByteString_enqueue_ByteString _ _) = _ =>
                   rewrite !padding_ByteString_enqueue_aligned_ByteString
                 | |- padding (format_checksum _ _ _ _ _) = _ =>
                   unfold format_checksum; rewrite encode_word'_padding
                 | _ => eauto using ByteString_mod_16_padding
                 end.
Qed.


Definition calculate_aligned_Pseudochecksum'
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           (m : nat)
           {sz} (v : ByteBuffer.t sz) (idx : nat) :=
  ByteBuffer_checksum srcAddr ^1+
  ByteBuffer_checksum destAddr ^1+
  zext protoCode 8 ^1+
  udpLength ^1+
  calculate_aligned_IPchecksum' m v idx.

Definition calculate_aligned_Pseudochecksum''
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           (m : nat)
           {sz} (v : ByteBuffer.t sz) :=
  calculate_aligned_IPchecksum' (12 + m)
                                ([wzero 8; protoCode] ++ srcAddr ++ destAddr ++
                                         (splitLength udpLength) ++ v) 0.

Lemma calculate_aligned_Pseudochecksum_equiv :
  forall (srcAddr : Vector.t (word 8) 4)
    (destAddr : Vector.t (word 8) 4)
    (udpLength : word 16)
    (protoCode : word 8)
    (m : nat)
    {sz} (v : ByteBuffer.t sz),
    calculate_aligned_Pseudochecksum' srcAddr destAddr udpLength protoCode m v 0 =
    calculate_aligned_Pseudochecksum'' srcAddr destAddr udpLength protoCode m v.
Proof.
  unfold calculate_aligned_Pseudochecksum', calculate_aligned_Pseudochecksum''.
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
  match goal with
  | |- _ = ?a ^1+ ?b =>
    assert (a ^1+ b = b ^1+ a) by (apply OneC_plus_comm)
  end.
  simpl in *. rewrite H.
  rewrite <- !OneC_plus_assoc.
  reflexivity.
Qed.

Lemma calculate_aligned_Pseudochecksum_front
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : word 16)
      (protoCode : word 8)
      m
      {sz}
  : forall (v : ByteBuffer.t sz) (idx : nat) (v' : ByteBuffer.t idx),
    calculate_aligned_Pseudochecksum' srcAddr destAddr udpLength protoCode m (v'++v) idx =
    calculate_aligned_Pseudochecksum' srcAddr destAddr udpLength protoCode m v 0.
Proof.
  intros. unfold calculate_aligned_Pseudochecksum'.
  f_equal. apply calculate_aligned_IPchecksum_front.
Qed.

Lemma calculate_aligned_Pseudochecksum_tail
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : word 16)
      (protoCode : word 8)
      {sz}
  : forall (v : ByteBuffer.t sz) (idx : nat) (v' : ByteBuffer.t idx),
    calculate_aligned_Pseudochecksum' srcAddr destAddr udpLength protoCode sz (v++v') 0 =
    calculate_aligned_Pseudochecksum' srcAddr destAddr udpLength protoCode sz v 0.
Proof.
  intros. unfold calculate_aligned_Pseudochecksum'.
  f_equal. apply calculate_aligned_IPchecksum_tail.
Qed.

Definition calculate_aligned_Pseudochecksum
           (srcAddr : Vector.t (word 8) 4)
           (destAddr : Vector.t (word 8) 4)
           (udpLength : word 16)
           (protoCode : word 8)
           (m : nat)
           {sz} (v : ByteBuffer.t sz) (idx : nat) :=
  wnot (calculate_aligned_Pseudochecksum' srcAddr destAddr udpLength protoCode m v idx).

Lemma CorrectAlignedEncoderForPseudoChecksumThenC
      {S}
      (srcAddr : Vector.t (word 8) 4)
      (destAddr : Vector.t (word 8) 4)
      (udpLength : word 16)
      (protoCode : word 8)
      (format_A format_B : FormatM S ByteString)
      (encode_A : forall sz, AlignedEncodeM sz)
      (encode_B : forall sz, AlignedEncodeM sz)
      (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
      (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
      n1
      (format_B_sz_OK' : forall (s : S) (b : ByteString) (env env' : CacheFormat),
          format_B s env ∋ (b, env') -> bin_measure b = n1)
      (format_B_sz_OK : n1 mod 16 = 0)
      (len_format_A : S -> nat)
      (format_A_sz_OK' : forall (s : S) (b : ByteString) (env env' : CacheFormat),
          format_A s env ∋ (b, env') -> bin_measure b = len_format_A s)
      (format_A_sz_OK : forall (s : S), len_format_A s mod 8 = 0)
  : CorrectAlignedEncoder
      (format_B ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength protoCode) OfSize 16
                ThenCarryOn format_A)
      (AlignedEncoderForChecksum n1 encode_B encode_A
                                 (calculate_aligned_Pseudochecksum srcAddr destAddr udpLength protoCode)).
Proof.
  apply CorrectAlignedEncoderForChecksum';
    unfold calculate_aligned_Pseudochecksum; eauto with nocore; intros.
  - rewrite calculate_aligned_Pseudochecksum_front.
    rewrite calculate_aligned_Pseudochecksum_tail. reflexivity.
  - destruct_conjs.
    assert (bin_measure b1 mod 16 = 0) as L1 by (erewrite format_B_sz_OK'; eauto).
    assert (padding b3 = 0) as L2 by (rewrite padding_eq_mod_8; erewrite format_A_sz_OK'; eauto).
    unfold f_bit_aligned_free, Pseudo_Checksum_Valid, onesComplement.
    rewrite calculate_aligned_Pseudochecksum_equiv.
    unfold calculate_aligned_Pseudochecksum''.
    unfold calculate_aligned_IPchecksum'.
    rewrite <- InternetChecksum_To_ByteBuffer_Checksum'.
    rewrite ByteString2ListOfChar_Over.
    rewrite !build_aligned_ByteString_append.
    rewrite !build_aligned_ByteString_byteString_idem.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- context [numBytes ?a * 8] =>
      replace (numBytes a * 8) with (bin_measure a)
    end.
    2 : rewrite length_ByteString_no_padding; try omega.

    match goal with
    | |- context [wnot (checksum (ByteString2ListOfChar ?a ?b))] =>
      assert (a = bin_measure b) as L
    end. {
      rewrite !@mappend_measure.
      rewrite !Nat.add_assoc.
      reflexivity.
    } rewrite L. clear L.
    rewrite !ByteString2ListOfChar_append.
    rewrite !ByteString2ListOfChar_format_checksum.

    assert (forall n, n mod 16 = 0 ->
                 forall b, exists x, |ByteString2ListOfChar n b| = 2 * x) as L. {
      clear. intros.
      apply Nat.mod_divides in H; eauto. destruct H as [x ?].
      replace (16 * x) with (8 * (2*x)) in * by omega.
      subst.
      rewrite ByteString2ListOfChar_len. eauto.
    }
    destruct L with (n:=bin_measure b1) (b:=b1) as [x1 ?]; eauto.
    clear L.
    set (ByteString2ListOfChar (bin_measure b1) b1) as l1 in *.
    set (ByteString2ListOfChar (bin_measure b3) b3) as l3 in *.

    rewrite !ByteString2ListOfChar_eq'.
    simpl Core.byteString. unfold ByteBuffer.to_list.

    unfold hi8, lo8.
    rewrite split1_wzero, split2_wzero.
    match goal with
    | |- checksum (?a :: ?b :: ?l)%list = _ =>
      replace (a :: b :: l)%list with (to_list (a :: [b])%vector ++ l)%list by reflexivity
    end.
    rewrite !app_assoc.
    unfold Core.char in *.
    match goal with
    | |- context [(?a ++ l1)%list] => set (a ++ l1)%list as l1'
    end.
    assert (exists x, | l1' | = 2 * x) as L'. {
      subst l1'. simpl.
      rewrite !app_length. rewrite <- !ByteBuffer.to_list_length. rewrite H7.
      exists (6+x1). omega.
    } destruct L' as [x L'].
    rewrite <- !app_assoc.
    match goal with
    | |- context [wnot (checksum ?a)] =>
      assert (checksum a = checksum (l1' ++ l3))%list as L
    end. {
      rewrite !checksum_split; eauto.
      exists 1. reflexivity.
    } rewrite L. clear L.
    rewrite checksum_split; eauto.
    rewrite checksum_split; eauto.
    match goal with
    | |- context [?a ^1+ (?b ^1+ ?c)] =>
        assert (a ^1+ (b ^1+ c) = b ^1+ a ^1+ c) as L
    end. {
      rewrite <- !OneC_plus_assoc.
      rewrite OneC_plus_comm.
      rewrite <- !OneC_plus_assoc.
      f_equal.
      rewrite OneC_plus_comm.
      reflexivity.
    } rewrite L. clear L.
    rewrite <- !checksum_split; eauto.
    apply checksum_correct.
    rewrite !app_length. rewrite L'. simpl. exists (1+x). omega.
    simpl. exists 1. omega.
    simpl. exists 1. omega.

    all : destruct_conjs; simpl.
    all : repeat match goal with
                 | |- padding (ByteString_enqueue_ByteString _ _) = _ =>
                   rewrite !padding_ByteString_enqueue_aligned_ByteString
                 | |- padding (format_checksum _ _ _ _ _) = _ =>
                   unfold format_checksum; rewrite encode_word'_padding
                 | _ => eauto using ByteString_mod_16_padding
                 end.
Qed.