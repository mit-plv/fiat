Require Import
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
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeCheckSum
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.Option
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.InternetChecksum.

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

Fixpoint transformer_dequeue_word {B}
         {transformer : Transformer B}
         {transformer_opt : QueueTransformerOpt transformer bool}
         (sz : nat)
         (b : B)
  : (word sz * B) :=
  match sz with
  | 0 => (WO, b)
  | S sz' =>
    match dequeue_opt b with
    | Some (v, b') =>
      let (w', b'') := transformer_dequeue_word sz' b' in
      (append_bit v w', b'')
    | _ => (wzero (S sz'), b)
    end
  end.

Lemma transformer_dequeue_enqueue_word
  : forall (w : word (0 + 1 * 8)) (ext : ByteString) OK,
    transformer_dequeue_word _ (ByteString_enqueue_ByteString (word_into_ByteString OK w) ext) = (w, ext).
Proof.
  simpl; intros; shatter_word w.
  unfold word_into_ByteString; simpl.
  do 8 match goal with
         |- context [ByteString_dequeue (ByteString_enqueue_ByteString ?z _)] =>
         let H := fresh in
         destruct (ByteString_dequeue z) as [ [? ?] | ] eqn:H;
           unfold ByteString_dequeue in H; simpl in H;
             [ erewrite ByteString_dequeue_transform_opt; try eassumption;
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
  rewrite <- ByteString_enqueue_ByteString_id_left.
  unfold ByteString_id; repeat f_equal.
  apply le_uniqueness_proof.
Qed.

Fixpoint ByteString2ListOfChar (n : nat)
         (b : ByteString) : list char :=
  match n with
  | 0 => nil
  | S (S (S (S (S (S (S (S n'))))))) =>
    let (c, b') := transformer_dequeue_word 8 b in
    cons c (ByteString2ListOfChar n' b')
  | S n' =>
    let (c, b') := transformer_dequeue_word 8 b in
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
  Local Opaque transformer_dequeue_word.
  intros.
  simpl.
  replace {| padding := 0; front := WO; paddingOK := PaddingOK; byteString := [c] |} with (word_into_ByteString ByteString_id_subproof (c : word (0 + 1 * 8))).
  rewrite transformer_dequeue_enqueue_word.
  reflexivity.
  unfold char in c; shatter_word c.
  unfold word_into_ByteString; simpl.
  f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma ByteString2ListOfChar_eq
  : forall (b ext : ByteString),
    padding b = 0 ->
    ByteString2ListOfChar (bin_measure b) (transform b ext) =
    byteString b.
Proof.
  simpl; intros.
  destruct b; simpl in *; subst.
  unfold length_ByteString; simpl padding; rewrite plus_O_n.
  simpl Core.byteString.
  revert front paddingOK; induction byteString; intros.
  - reflexivity.
  - simpl Core.byteString; simpl length.
    rewrite Mult.mult_succ_r, NPeano.Nat.add_comm.
    rewrite Mult.mult_comm.
    do 8 rewrite plus_Sn_m.
    rewrite plus_O_n.
    symmetry.
    rewrite <- (IHbyteString WO paddingOK) at 1.
    replace (ByteString_enqueue_ByteString {| padding := 0; front := front; paddingOK := paddingOK; byteString := a :: byteString |} ext)
    with
    (ByteString_enqueue_ByteString {| padding := 0; front := front; paddingOK := paddingOK; byteString := [a] |} (ByteString_enqueue_ByteString {| padding := 0; front := front; paddingOK := paddingOK; byteString := byteString |} ext) ).
    pose proof ByteString2ListOfChar_push_char as H'.
    simpl plus in H'.
    shatter_word front.
    rewrite H'.
    f_equal.
    f_equal.
    omega.
    rewrite ByteString_enqueue_ByteString_assoc.
    f_equal.
    shatter_word front.
    erewrite <- massage_queue_into_ByteString; reflexivity.
Qed.

Corollary ByteString2ListOfChar_eq'
  : forall (b : ByteString),
    padding b = 0 ->
    ByteString2ListOfChar (bin_measure b) b =
    byteString b.
Proof.
  intros.
  erewrite <- ByteString2ListOfChar_eq with (ext := transform_id); auto.
Qed.

Definition transformer : Transformer ByteString :=
  ByteStringQueueTransformer.

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
    rewrite length_ByteString_enqueue.
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
  let b'' := if Peano_dec.eq_nat_dec (padding b) 0 then transform_id
             else encode_word (wzero (8 - (padding b))) in
  transform b''
            (encode_word (wnot (onesComplement
                                  (ByteString2ListOfChar (bin_measure (transform b b')) (transform b b'))))).

Lemma length_ByteString_IPChecksum
  : forall b b',
    padding b = 0
    -> length_ByteString (IPChecksum b b') = 16.
Proof.
  unfold IPChecksum; simpl; intros.
  erewrite ByteString_enqueue_ByteString_measure.
  rewrite H; find_if_inside; try congruence.
  rewrite length_encode_word.
  rewrite length_ByteString_id; reflexivity.
Qed.

(*Lemma encode_word_S :
  forall n w, encode_word (sz := S n) w =
              transform (encode_word (WS (whd w) WO))
                        (encode_word (wtl w)).
Proof.
  intros; rewrite (shatter_word w); simpl.
  induction n; simpl;
    rewrite (shatter_word (wtl w)).
  reflexivity.
  simpl.
  rewrite IHn.
  unfold encode_word; simpl.
  rewrite ByteString_enqueue_ByteString_assoc,
  <- !ByteString_enqueue_ByteString_enqueue_ByteString.


  unfold ByteString_enqueue_ByteString at 1; simpl.
Qed.

Lemma encode_word_WO :
  forall w, encode_word' 0 w = transform_id.
Proof.
  intros; rewrite (shatter_word w); simpl; reflexivity.
Qed. *)

(*Lemma encode_char :
  forall n w, encode_word (sz := 8 + n) w =
            transform {| front := WO;
               paddingOK := Lt.lt_0_Sn _;
               byteString := WS (whd w)
                             (WS (whd (wtl w))
                             (WS (whd (wtl (wtl w)))
                             (WS (whd (wtl (wtl (wtl w))))
                             (WS (whd (wtl (wtl (wtl (wtl w)))))
                             (WS (whd (wtl (wtl (wtl (wtl (wtl w))))))
                             (WS (whd (wtl (wtl (wtl (wtl (wtl (wtl w)))))))
                             (WS (whd (wtl (wtl (wtl (wtl (wtl (wtl (wtl w)))))))) WO))))))) :: nil |} (encode_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))).
Proof.
  simpl; intros.
  rewrite (encode_word_S (7 + n)).
  rewrite (encode_word_S (6 + n)).
  rewrite (encode_word_S (5 + n)).
  rewrite (encode_word_S (4 + n)).
  rewrite (encode_word_S (3 + n)).
  rewrite (encode_word_S (2 + n)).
  rewrite (encode_word_S (1 + n)).
  rewrite (encode_word_S (n)).
  rewrite !transform_assoc.
  simpl; f_equal.
  unfold ByteString_push, ByteString_id; simpl.
  simpl.
  unfold ByteString_transformer at 7. simpl.
  unfold ByteString_transformer at 6. simpl.
  unfold ByteString_transformer at 5. simpl.
  unfold ByteString_transformer at 4. simpl.
  unfold ByteString_transformer at 3. simpl.
  unfold ByteString_transformer at 2. simpl.
  unfold ByteString_transformer at 1. simpl.
  unfold ByteString_transformer. simpl.
  unfold ByteString_push at 7; simpl.
  unfold ByteString_push at 6; simpl.
  unfold ByteString_push at 5; simpl.
  unfold ByteString_push at 4; simpl.
  unfold ByteString_push at 3; simpl.
  unfold ByteString_push at 2; simpl.
  unfold ByteString_push at 1; simpl.
  unfold ByteString_push; simpl.
  f_equal; apply le_uniqueness_proof.
Qed.

Lemma ByteString_push_WO :
  forall bs,
    ByteString_push_word WO bs = bs.
Proof.
  reflexivity.
Qed. *)

(*Lemma encode_word_hi_lo :
  forall w : word 16, encode_word w =
            {| front := WO;
               paddingOK := Lt.lt_0_Sn _;
               byteString := [lo8 w; hi8 w] |}.
Proof.
Defined.
  intros; rewrite (encode_char 8).
  intros; rewrite (encode_char 0).
  simpl.
  unfold ByteString_enqueue_ByteString.
  simpl.
  rewrite !ByteString_push_char_id_right.
  rewrite encode_word_WO.
  simpl.
  f_equal.
  apply le_uniqueness_proof.
  simpl.
  unfold hi8, lo8.
  unfold split2.
  unfold split1, plus.
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w)))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w)))))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w)))))))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w)))))))))))))))).
  f_equal.
  rewrite (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))))))))))).
  f_equal.
  rewrite encode_word_WO; reflexivity.
  rewrite encode_word_WO; reflexivity.
Qed. *)

Lemma length_ByteString_into_list_measure :
  forall b,
| ByteString_into_list b | = bin_measure b.
Proof.
  simpl.
  intros; rewrite <- length_list_into_ByteString; f_equal.
  rewrite <- ByteString_into_list_eq; reflexivity.
Qed.

Lemma encode_word'_padding :
  forall sz (w : word sz),
    padding (encode_word' _ w transform_id) = NPeano.modulo sz 8.
Proof.
  intros; rewrite (ByteString_into_list_eq _).
  rewrite padding_list_into_ByteString.
  f_equal.
  rewrite length_ByteString_into_list_measure.
  simpl.
  rewrite length_encode_word'; simpl; rewrite length_ByteString_id.
  omega.
Qed.

(*Lemma even_IPChecksum
  : forall w : word 16, (|byteString (encode_word w) |) = 2.
Proof.
  intros; pose proof (length_encode_word' 16 w) as H'''; simpl in H'''.
  unfold length_ByteString in H'''.
  setoid_rewrite encode_word'_padding in H'''; simpl in H'''.
  omega.
Qed. *)

(*Lemma onesComplement_onesComplement :
  forall b,
    (exists n, length b = 2 * n)
    -> onesComplement (b ++ (byteString (encode_word' 16 (wnot (onesComplement b))))) = wones 16.
Proof.
  intros; rewrite onesComplement_commute; eauto.
  unfold onesComplement; intros.
  rewrite encode_word_hi_lo.
  apply checksum_correct.
  rewrite even_IPChecksum; exists 1; reflexivity.
Qed. *)

Definition IPChecksum_Valid (n : nat) (b : ByteString) : Prop :=
  onesComplement (ByteString2ListOfChar n b) = wones 16.

Definition IPChecksum_Valid_dec (n : nat) (b : ByteString)
  : {IPChecksum_Valid n b} + {~IPChecksum_Valid n b} := weq _ _.

Definition decode_IPChecksum
  : ByteString -> CacheDecode -> option (() * ByteString * CacheDecode) :=
  decode_unused_word 16.

(*Lemma ByteString_transformer_eq_app :
  forall (b b' : ByteString),
    padding b = 0
    -> padding b' = 0
    -> ByteString_enqueue_ByteString b b' =
       {| front := WO;
          paddingOK := Lt.lt_0_Sn _;
          byteString := byteString b ++ byteString b' |}.
Proof.
Defined. *)

Lemma ByteString2ListOfChar_Over :
  forall (b ext : ByteString),
    padding b = 0
    -> ByteString2ListOfChar (bin_measure b)
                             (transform b ext) =
       ByteString2ListOfChar (bin_measure b) b.
Proof.
  intros; rewrite ByteString2ListOfChar_eq; eauto.
  intros; rewrite ByteString2ListOfChar_eq'; eauto.
Qed.

Lemma padding_eq_length
  : forall b,
    padding b = (bin_measure b) - (8 * length (byteString b)).
Proof.
  destruct b; simpl.
  unfold length_ByteString; simpl.
  omega.
Qed.

Lemma length_list_into_ByteString
  : forall l, length_ByteString (list_into_ByteString l) = length l.
Proof.
  induction l.
  - reflexivity.
  - simpl; rewrite length_ByteString_push; eauto.
Qed.

(*Lemma add_padding_OK
  : forall b,
    padding (transform b
                       (if Peano_dec.eq_nat_dec (padding b) 0 then transform_id
                       else encode_word (wzero (8 - (padding b))))) = 0.
Proof.
Defined. *)
(*  intros; rewrite transform_padding_eq.
  find_if_inside; subst; simpl.
  - rewrite e; simpl; eauto.
  - pose proof (paddingOK b).
    destruct (padding b); simpl; eauto.
    repeat match goal with
           | [ |- context[match ?n0 with 0 => _ | _ => _ end] ]
             => is_var n0; destruct n0; simpl; eauto; [ ]
           end.
    omega.
Qed. *)

(* Lemma IPChecksum_OK : *)
(*   forall (b ext : ByteString), *)
(*     IPChecksum_Valid (bin_measure (transform b (IPChecksum b))) *)
(*                      (transform (transform b (IPChecksum b)) ext). *)
(* Proof. *)
(*   simpl; intros. *)
(*   unfold IPChecksum, IPChecksum_Valid. *)
(*   pose proof transform_assoc as H'; simpl in H'; rewrite H'. *)
(*   rewrite ByteString_transformer_eq_app. *)
(*   rewrite ByteString2ListOfChar_Over. *)
(*   rewrite !ByteString2ListOfChar_eq'; simpl. *)
(*   apply onesComplement_onesComplement. *)
(*   eapply add_padding_OK. *)
(*   reflexivity. *)
(*   reflexivity. *)
(*   eapply add_padding_OK. *)
(*   rewrite encode_word'_padding; reflexivity. *)
(* Qed. *)

(*Lemma padding_transform_commute
  : forall b b',
    padding (transform b b') = padding (transform b' b).
Proof.
Defined. *)
(*  intros; rewrite !transform_padding_eq.
  rewrite Plus.plus_comm; eauto.
Qed. *)

Definition IPv4_Packet_encoded_measure (ipv4_b : ByteString)
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

Lemma transformer_dequeue_word_inj
  : forall sz w w' p,
    WordOpt.transformer_dequeue_word sz w = Some p
    -> WordOpt.transformer_dequeue_word sz w' = Some p
    -> w = w'.
Proof.
  induction sz; simpl; intros.
  - injections; eauto.
  - destruct (ByteString_dequeue w) as [ [? ?] | ] eqn : ? ;
      destruct (ByteString_dequeue w') as [ [? ?] | ] eqn : ?;
                                                              try discriminate.
    simpl in *.
    destruct (WordOpt.transformer_dequeue_word sz b0) as [ [? ?] | ] eqn : ? ;
      destruct (WordOpt.transformer_dequeue_word sz b2) as [ [? ?] | ]  eqn : ? ;
      try discriminate.
    destruct p as [? ?].
    injection H; injection H0; intros; subst.
    eapply ByteString_dequeue_opt_inj; eauto.
    apply SW_word_inj in H4; simpl in *; injections.
    apply SW_word_inj' in H1; subst.
    replace b0 with b2; eauto.
Qed.

(*Lemma decode_IPChecksum_pf'
  : forall (u : ()) (b b' : ByteString),
    () -> forall ctxD ctxD' : (), True -> decode_IPChecksum b ctxD = Some (u, b', ctxD') -> True /\ (exists b'' : ByteString, b = ByteString_transformer b'' b').
Proof.
  unfold IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
  intros; destruct (WordOpt.transformer_pop_word 16 b) eqn : ? ;
    simpl in H1; try discriminate.
  intuition.
  destruct p; simpl in H1.
  injections.
  eexists (encode_word' 16 w).
  eapply transformer_pop_word_inj; eauto.
  pose proof transformer_pop_encode_word' as H'; simpl in H';
    eapply H'.
Qed.

Lemma decode_IPChecksum_pf
  : forall (b b' ext : ByteString) (ctx ctx' ctxD : ()),
    padding b = 0 ->
    decode_IPChecksum (ByteString_transformer (ByteString_transformer (IPChecksum b b') b') ext) ctxD = Some ((), ByteString_transformer b' ext, ctxD).
Proof.
  intros; pose proof transform_assoc as H'; simpl in H'; rewrite <- H'; clear H'.
  unfold IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
  find_if_inside.
  rewrite transform_id_left.
  pose proof transformer_pop_encode_word' as H'; simpl in H'; rewrite H'; simpl; eauto.
  congruence.
Qed. *)

Definition IPChecksum_ByteAligned (b : ByteString) :=
  padding b = 0 /\ exists n, length (byteString b) = 2 * n.

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
  omega.
Qed.

Lemma IPChecksum_ByteAligned_length_ByteString
  : forall b,
    IPChecksum_ByteAligned b
    -> NPeano.modulo (length_ByteString b) 16 = 0.
Proof.
  destruct b; unfold length_ByteString.
  unfold Core.padding, Core.byteString.
  intros; destruct H; simpl in H.
  rewrite H, plus_O_n.
  destruct_ex.
  simpl Core.byteString in H0.
  rewrite H0.
  rewrite Mult.mult_assoc.
  unfold mult at 2.
  simpl plus.
  rewrite Mult.mult_comm, NPeano.Nat.mod_mul; eauto.
Qed.

(*Lemma IPchecksum_Valid_OK' :
  forall (b b' ext : ByteString),
    IPChecksum_ByteAligned b  (* Should be able to elide this assumption. *)
    -> IPChecksum_ByteAligned b'
    -> IPChecksum_Valid
         (bin_measure (transform (transform b (IPChecksum b b')) b'))
         (transform (transform (transform b (IPChecksum b b')) b') ext).
Proof.
  simpl; intros.
  destruct H0; destruct H.
  unfold IPChecksum, IPChecksum_Valid.
  pose proof transform_assoc as H'; simpl in H'; rewrite H'.
  rewrite ByteString2ListOfChar_Over with (ext := ext); try eassumption.
  rewrite !ByteString_transformer_eq_app; try eassumption.
  pose proof ByteString2ListOfChar_eq' as H''; simpl in H''.
  rewrite H''.
  unfold byteString at 1.
  unfold byteString at 1.
  unfold byteString at 1.
  rewrite onesComplement_commute; eauto.
  rewrite app_assoc.
  rewrite H''.
  unfold byteString at 5.
  rewrite onesComplement_commute with (b := byteString b); eauto.
  rewrite H; find_if_inside; try congruence.
  simpl; rewrite app_nil_r.
  apply onesComplement_onesComplement.
  destruct_ex; eexists (x + x0); rewrite app_length; rewrite H1, H2; omega.
  reflexivity.
  rewrite H; find_if_inside; try congruence.
  rewrite !app_length.
  simpl; destruct_ex; exists (x0 + 1).
  rewrite H2, even_IPChecksum; omega.
  reflexivity.
  find_if_inside.
  reflexivity.
  congruence.
  rewrite H; find_if_inside; try congruence.
  pose proof transform_id_right as H''; simpl in H''; rewrite H''; eauto.
  rewrite encode_word'_padding; reflexivity.
  rewrite H; find_if_inside; try congruence.
  pose proof transform_id_right as H''; simpl in H''; rewrite H''; eauto.
  rewrite transform_padding_eq; rewrite H.
  rewrite encode_word'_padding; reflexivity.
  rewrite H; find_if_inside; try congruence.
  pose proof transform_id_right as H''; simpl in H''; rewrite H''; eauto.
  rewrite transform_padding_eq.
  rewrite transform_padding_eq; rewrite H.
  rewrite encode_word'_padding.
  rewrite H0; reflexivity.
Qed. *)

Lemma normalize_encoder_term {A}
  : forall (encoder encoder' : A -> CacheEncode -> Comp (_ * CacheEncode))
           (a : A)
           (ctx ctx' : CacheEncode)
           (b : ByteString),
    encoder a ctx ↝ (b, ctx')
    -> (forall a ctx, refineEquiv (encoder a ctx) (encoder' a ctx))
    -> encoder' a ctx ↝ (b, ctx').
Proof.
  intros; eapply H0; eauto.
Qed.

Lemma length_ByteString_compose :
  forall encode1 encode2 b (ctx ctx' : CacheEncode) n n',
    computes_to (compose _ encode1 encode2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (encode1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (encode2 ctx) (b, ctx')
                           -> length_ByteString b = n')
    -> length_ByteString b = n + n'.
Proof.
  unfold compose, Bind2; intros; computes_to_inv; injections.
  destruct v; destruct v0.
  rewrite ByteString_enqueue_ByteString_measure; erewrite H0, H1; eauto.
Qed.

Lemma length_ByteString_composeChecksum :
  forall sz checksum_Valid encode1 encode2 b (ctx ctx' : CacheEncode) n n' ,
    computes_to (composeChecksum _ _ _ sz checksum_Valid encode1 encode2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (encode1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (encode2 ctx) (b, ctx')
                           -> length_ByteString b = n')
    -> length_ByteString b = n + n' + sz.
Proof.
  unfold composeChecksum, Bind2; intros; computes_to_inv; injections.
  destruct v; destruct v0.
  rewrite !ByteString_enqueue_ByteString_measure; simpl.
  unfold encode_checksum.
  erewrite length_encode_word'; simpl; rewrite length_ByteString_id.
  erewrite H0, H1; eauto; omega.
Qed.

Lemma length_ByteString_composeIf :
  forall encode1 encode2 b (ctx ctx' : CacheEncode) n P,
    computes_to (composeIf _ _ _ P encode1 encode2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (encode1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (encode2 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> length_ByteString b = n.
Proof.
  unfold composeIf, Bind2; intros; computes_to_inv; injections.
  destruct v; simpl in *; eauto.
Qed.

Transparent pow2.
Arguments pow2 : simpl never.

(*Lemma computes_to_composeChecksum_decode_unused_word
  : forall sz checksum (w : word sz) ctx ctx'' rest rest' b,
    computes_to ((((encode_word_Spec w) ThenC rest')
                    ThenChecksum checksum OfSize sz ThenCarryOn rest) ctx) (b, ctx'')
    -> exists b' b'' ctx' ctx''' ,
      computes_to (rest' ctx') (b', ctx''')
      /\ computes_to (rest ctx''') (b'', ctx'')
      /\ forall ext, decode_unused_word' sz (transform b ext) = Some ((), transform (transform b' (transform (checksum sz (transform (encode_word' _ w) b') b'') b'')) ext).
Proof.
  unfold composeChecksum, compose, Bind2, encode_word_Spec; intros; computes_to_inv; injections.
  destruct v0; destruct v2; simpl in *; do 4 eexists;
    repeat split; eauto.
  unfold decode_unused_word'.
  intros.
  rewrite <- !ByteString_transform_assoc.
  pose proof transformer_pop_encode_word' as H''; simpl in H'';
    intros; rewrite H''; reflexivity.
Qed. *)

Lemma computes_to_compose_decode_word
  : forall sz (w : word sz) (ctx ctx'' : CacheEncode)
           (rest : CacheEncode -> Comp (ByteString * CacheEncode))
           (b : ByteString),
    computes_to (((encode_word_Spec w) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_word' sz (transform b ext) = Some (w, transform b' ext).
Proof.
  unfold composeChecksum, compose, Bind2, encode_word_Spec; intros; computes_to_inv; injections.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  intros; rewrite <- transformer_dequeue_word_eq_decode_word'.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof transformer_dequeue_encode_word' as H''; simpl in H'';
    intros; rewrite H''; reflexivity.
Qed.

Lemma computes_to_compose_decode_unused_word
  : forall sz (w : word sz) (ctx ctx'' : CacheEncode)
           (rest : CacheEncode -> Comp (ByteString * CacheEncode))
           (b : ByteString),
    computes_to (((encode_word_Spec w) ThenC rest) ctx) (b, ctx'')
    -> exists b' ctx',
      computes_to (rest ctx') (b', ctx'')
      /\ forall ext,
        decode_unused_word' sz (transform b ext) = Some ((), transform b' ext).
Proof.
  unfold composeChecksum, compose, Bind2, encode_word_Spec; intros; computes_to_inv; injections.
  destruct v0; simpl in *; do 2 eexists;
    repeat split; eauto.
  unfold decode_unused_word'; intros.
  rewrite <- !ByteString_enqueue_ByteString_assoc.
  pose proof transformer_dequeue_encode_word' as H''; simpl in H'';
    intros; rewrite H''; reflexivity.
Qed.

Arguments mult : simpl never.
Arguments decode_word' : simpl never.

Lemma length_ByteString_ret :
  forall b' b (ctx ctx' : CacheEncode),
    computes_to (ret (b', ctx)) (b, ctx')
    -> length_ByteString b = length_ByteString b'.
Proof.
  intros; computes_to_inv; injections; reflexivity.
Qed.

Lemma length_ByteString_unused_word
  : forall sz (b : ByteString) (ctx ctx' : CacheEncode),
    encode_unused_word_Spec sz ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold encode_unused_word_Spec, encode_unused_word_Spec'; simpl.
  intros; computes_to_inv; injections.
  rewrite length_encode_word'; simpl.
  rewrite length_ByteString_id.
  omega.
Qed.

Lemma length_ByteString_word
  : forall sz (w : word sz) (b : ByteString) (ctx ctx' : CacheEncode),
    encode_word_Spec w ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold encode_word_Spec; simpl.
  intros; computes_to_inv; injections.
  rewrite length_encode_word'.
  simpl; rewrite length_ByteString_id; omega.
Qed.

Lemma length_ByteString_bool
  : forall (b' : bool) (b : ByteString) (ctx ctx' : CacheEncode),
    encode_bool_Spec b' ctx ↝ (b, ctx')
    -> length_ByteString b = 1.
Proof.
  unfold encode_bool_Spec; simpl.
  intros; computes_to_inv; injections.
  eapply length_ByteString_enqueue.
Qed.

Lemma length_ByteString_encode_list {A}
  : forall encode_A l (b : ByteString) (ctx ctx' : CacheEncode) n,
    (forall (a : A) (b : ByteString) (ctx ctx' : CacheEncode),
        computes_to (encode_A a ctx) (b, ctx')
        -> length_ByteString b = n)
    -> encode_list_Spec encode_A l ctx ↝ (b, ctx')
    -> length_ByteString b = (length l) * n.
Proof.
  induction l; simpl; intros; computes_to_inv.
  - injections; reflexivity.
  - unfold Bind2 in H0; computes_to_inv; injections.
    destruct v; destruct v0; simpl in *.
    erewrite ByteString_enqueue_ByteString_measure.
    erewrite H; eauto.
    rewrite Mult.mult_succ_l.
    erewrite <- IHl; eauto with arith.
Qed.

Lemma ByteString_enqueue_padding_eq
  : forall a b,
    padding (ByteString_enqueue a b) =
    NPeano.modulo (S (padding b)) 8.
Proof.
  intros; rewrite !padding_eq_mod_8, length_ByteString_enqueue.
  rewrite (NPeano.Nat.add_mod_idemp_r 1 _ 8); auto.
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
    rewrite length_ByteString_enqueue.
    f_equal; simpl; omega.
Qed.

Lemma ByteString_enqueue_ByteString_padding_eq
  : forall b b',
    padding (ByteString_enqueue_ByteString b b') = NPeano.modulo (padding b + padding b') 8.
Proof.
  intros.
  rewrite (ByteString_into_queue_eq b),
  (ByteString_into_queue_eq b').
  rewrite ByteString_enqueue_ByteString_into_list.
  rewrite queue_into_ByteString_app.
  generalize (queue_into_ByteString (ByteString_into_queue b)).
  induction (ByteString_into_queue b'); intros; simpl fold_left.
  - change (padding (queue_into_ByteString nil)) with 0.
    rewrite <- plus_n_O.
    rewrite (ByteString_into_list_eq b0).
    rewrite padding_list_into_ByteString.
    rewrite NPeano.Nat.mod_mod; auto.
  - rewrite IHl.
    rewrite ByteString_enqueue_padding_eq.
    rewrite !queue_into_ByteString_padding_eq.
    simpl length.
    rewrite <- NPeano.Nat.add_mod; auto.
    rewrite NPeano.Nat.add_mod_idemp_r; auto.
    f_equal; omega.
Qed.

Definition length_ByteString_ByteString_id
  : length_ByteString ByteString_id = 0 := eq_refl.

Lemma length_ByteString_encode_option {A}
  : forall encode_Some encode_None a_opt
           (b : ByteString) (ctx ctx' : CacheEncode) n,
    (forall (a : A) (b : ByteString) (ctx ctx' : CacheEncode),
        computes_to (encode_Some a ctx) (b, ctx')
        -> length_ByteString b = n)
    -> (forall (b : ByteString) (ctx ctx' : CacheEncode),
           computes_to (encode_None () ctx) (b, ctx')
           -> length_ByteString b = n)
    -> encode_option_Spec encode_Some encode_None a_opt ctx ↝ (b, ctx')
    -> length_ByteString b = n.
Proof.
  destruct a_opt; simpl; intros; computes_to_inv.
  - eapply H; eauto.
  - eauto.
Qed.

(*Lemma IPChecksum_unique
  : forall x x3 x1 ext u ctx ctx',
    IPChecksum_ByteAligned x
    -> IPChecksum_ByteAligned x1
    -> IPChecksum_Valid (length_ByteString (ByteString_transformer x (ByteString_transformer x3 x1)))
                     (ByteString_transformer x (ByteString_transformer x3 (ByteString_transformer x1 ext)))
    -> decode_IPChecksum (ByteString_transformer x3 (ByteString_transformer x1 ext)) ctx = Some (u, (ByteString_transformer x1 ext), ctx')
    -> x3 = IPChecksum x x1.
Proof.
Defined. *)

Lemma compose_IPChecksum_encode_correct
  : forall (A : Type)
           (B := ByteString)
           (trans : Transformer B := transformer)
           (trans_opt : QueueTransformerOpt trans bool :=
              ByteString_QueueTransformerOpt)
           (calculate_checksum := IPChecksum)
           (checksum_Valid := IPChecksum_Valid)
           (checksum_Valid_dec := IPChecksum_Valid_dec)
           (A' : Type)
           (P : CacheDecode -> Prop)
           (P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop)
           (decodeChecksum := decode_IPChecksum),
    cache_inv_Property P
                       (fun P0 : CacheDecode -> Prop =>
                          P_inv1 P0 /\
                          P_inv2 P0 /\
                          (forall (b : B) (ctx : CacheDecode) (u : ()) (b' : B) (ctx' : CacheDecode),
                              decodeChecksum b ctx = Some (u, b', ctx') -> P0 ctx -> P0 ctx')) ->
    forall (project : A -> A') (predicate : A -> Prop)
           (predicate' : A' -> Prop) (predicate_rest' : A -> B -> Prop)
           (predicate_rest : A' -> B -> Prop)
           (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
           (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
           (encoded_A_measure : B -> nat)
           (len_encode1 : A -> nat)
           (len_encode2 : A -> nat),
      (forall a' b ctx ctx',
          computes_to (encode1 (project a') ctx) (b, ctx')
          -> length_ByteString b = len_encode1 a')
      -> (forall a b ctx ctx',
             computes_to (encode2 a ctx) (b, ctx')
             -> length_ByteString b = len_encode2 a)
      -> (forall a, NPeano.modulo (len_encode1 a) 8 = 0)
      -> (forall a, NPeano.modulo (len_encode2 a) 8 = 0)
      -> (forall (a : A) (ctx ctx' ctx'' : CacheEncode) c (b b'' ext : B),
             encode1 (project a) ctx ↝ (b, ctx') ->
             encode2 a ctx' ↝ (b'', ctx'') ->
             predicate a ->
             len_encode1 a + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform (encode_checksum _ _ _ 16 c) b'')) ext)) ->
      forall decode1 : B -> CacheDecode -> option (A' * B * CacheDecode),
        (cache_inv_Property P P_inv1 ->
         encode_decode_correct_f _ transformer predicate' predicate_rest encode1 decode1 P) ->
        (forall data : A, predicate data -> predicate' (project data)) ->
        (forall (a' : A') (b : ByteString) (a : A) (ce ce' ce'' : CacheEncode)
                (b' b'' : ByteString) c,
            encode1 a' ce ↝ (b', ce') ->
            project a = a' ->
            predicate a ->
            encode2 a ce' ↝ (b'', ce'') ->
            predicate_rest' a b ->
            {c0 : word 16 |
             forall ext : ByteString,
               IPChecksum_Valid (bin_measure (transform b' (transform (encode_checksum _ _ _ _ c0) b'')))
                                (transform (transform b' (transform (encode_checksum _ _ _ _ c0) b'')) ext)} ↝ c ->
            predicate_rest a' (transform (transform (encode_checksum _ _ _ _ c) b'') b)) ->
        forall decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode),
          (forall proj : A',
              predicate' proj ->
              cache_inv_Property P P_inv2 ->
              encode_decode_correct_f _ transformer
                                      (fun data : A => predicate data /\ project data = proj) predicate_rest' encode2
                                      (decode2 proj) P) ->
          encode_decode_correct_f _ transformer predicate predicate_rest'
                                  (fun data : A =>
                                     encode1 (project data) ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn encode2 data)
                                  (fun (bin : B) (env : CacheDecode) =>
                                     if checksum_Valid_dec (encoded_A_measure bin) bin
                                     then
                                       `(proj, rest, env') <- decode1 bin env;
                                         `(_, rest', env'0) <- decodeChecksum rest env';
                                         decode2 proj rest' env'0
                                     else None) P.
Proof.
  intros; eapply composeChecksum_encode_correct.
  - eassumption.
  - intros; rewrite !transform_measure.
    simpl; rewrite (H0 _ _ _ _ H9).
    simpl; rewrite (H1 _ _ _ _ H10).
    erewrite <- H4; eauto; try omega.
    unfold encode_checksum.
    rewrite length_encode_word'.
    simpl; omega.
  - eassumption.
  - eassumption.
  - eassumption.
  - intros; unfold decodeChecksum, IPChecksum, decode_IPChecksum,
            decode_unused_word, decode_unused_word'.
    rewrite <- !transform_assoc.
    unfold B in *.
    unfold encode_checksum.
    rewrite transformer_dequeue_encode_word'; simpl; eauto.
  - unfold decodeChecksum, IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
    intros; destruct (WordOpt.transformer_dequeue_word 16 b) eqn : ? ;
      try discriminate; intuition.
    destruct p.
    injections.
    eexists w.
    simpl.
    unfold encode_checksum.
    erewrite (transformer_dequeue_word_inj _ b);
      [ | eauto
        | pose proof transformer_dequeue_encode_word' as H'; simpl in H';
          eapply H'].
    reflexivity.
  - eassumption.
  - intros.
    unfold IPChecksum_Valid in *.
    simpl.
    rewrite ByteString2ListOfChar_Over.
    * rewrite ByteString2ListOfChar_Over in H12.
      eauto.
      simpl.
      apply H0 in H10.
      pose proof (H2 data).
      rewrite <- H10 in H13.
      rewrite !ByteString_enqueue_ByteString_padding_eq.
      rewrite padding_eq_mod_8, H13.
      pose proof (H3 data).
      unfold encode_checksum.
      rewrite encode_word'_padding.
      rewrite <- (H1 _ _ _ _ H11) in H14.
      rewrite padding_eq_mod_8, H14.
      reflexivity.
    * rewrite !ByteString_enqueue_ByteString_padding_eq.
      apply H0 in H10.
      pose proof (H2 data).
      rewrite <- H10 in H13.
      rewrite padding_eq_mod_8, H13.
      pose proof (H3 data).
      unfold encode_checksum.
      rewrite encode_word'_padding.
      rewrite <- (H1 _ _ _ _ H11) in H14.
      rewrite padding_eq_mod_8, H14.
      reflexivity.
Qed.

(* A (hopefully) more convenient IP_Checksum lemma *)
Lemma compose_IPChecksum_encode_correct'
  : forall (A : Type)
           (B := ByteString)
           (trans : Transformer B := transformer)
           (trans_opt : QueueTransformerOpt trans bool :=
              ByteString_QueueTransformerOpt)
           (calculate_checksum := IPChecksum)
           (checksum_Valid := IPChecksum_Valid)
           (checksum_Valid_dec := IPChecksum_Valid_dec)
           (A' : Type)
           (P : CacheDecode -> Prop)
           (P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop)
           (decodeChecksum := decode_IPChecksum),
    cache_inv_Property P
                       (fun P0 : CacheDecode -> Prop =>
                          P_inv1 P0 /\
                          P_inv2 P0 /\
                          (forall (b : B) (ctx : CacheDecode) (u : ()) (b' : B) (ctx' : CacheDecode),
                              decodeChecksum b ctx = Some (u, b', ctx') -> P0 ctx -> P0 ctx')) ->
    forall (project : A -> A') (predicate : A -> Prop)
           (predicate' : A' -> Prop) (predicate_rest' : A -> B -> Prop)
           (predicate_rest : A' -> B -> Prop)
           (encode1 : A -> CacheEncode -> Comp (B * CacheEncode))
           (encode1' : A' -> CacheEncode -> Comp (B * CacheEncode))
           (refine_encode1 : forall a ctx,
               refineEquiv (encode1 a ctx) (encode1' (project a) ctx))
           (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
           (encoded_A_measure : B -> nat)
           (len_encode1 : A -> nat)
           (len_encode2 : A -> nat),
      (forall a' b ctx ctx',
          computes_to (encode1 a' ctx) (b, ctx')
          -> length_ByteString b = len_encode1 a')
      -> (forall a b ctx ctx',
             computes_to (encode2 a ctx) (b, ctx')
             -> length_ByteString b = len_encode2 a)
      -> (forall a, NPeano.modulo (len_encode1 a) 8 = 0)
      -> (forall a, NPeano.modulo (len_encode2 a) 8 = 0)
      -> (forall (a : A) (ctx ctx' ctx'' : CacheEncode) c (b b'' ext : B),
             encode1 a ctx ↝ (b, ctx') ->
             encode2 a ctx' ↝ (b'', ctx'') ->
             predicate a ->
             len_encode1 a + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform (encode_checksum _ _ _ 16 c) b'')) ext)) ->
      forall decode1 : B -> CacheDecode -> option (A' * B * CacheDecode),
        (cache_inv_Property P P_inv1 ->
         encode_decode_correct_f _ transformer predicate' predicate_rest encode1' decode1 P) ->
        (forall data : A, predicate data -> predicate' (project data)) ->
        (forall (a' : A') (b : ByteString) (a : A) (ce ce' ce'' : CacheEncode)
                (b' b'' : ByteString) c,
            encode1' a' ce ↝ (b', ce') ->
            project a = a' ->
            predicate a ->
            encode2 a ce' ↝ (b'', ce'') ->
            predicate_rest' a b ->
            {c0 : word 16 |
             forall ext : ByteString,
               IPChecksum_Valid (bin_measure (transform b' (transform (encode_checksum _ _ _ _ c0) b'')))
                                (transform (transform b' (transform (encode_checksum _ _ _ _ c0) b'')) ext)} ↝ c ->
            predicate_rest a' (transform (transform (encode_checksum _ _ _ _ c) b'') b)) ->
        forall decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode),
          (forall proj : A',
              predicate' proj ->
              cache_inv_Property P P_inv2 ->
              encode_decode_correct_f _ transformer
                                      (fun data : A => predicate data /\ project data = proj) predicate_rest' encode2
                                      (decode2 proj) P) ->
          encode_decode_correct_f _ transformer predicate predicate_rest'
                                  (fun data : A =>
                                     encode1 data ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn encode2 data)
                                  (fun (bin : B) (env : CacheDecode) =>
                                     if checksum_Valid_dec (encoded_A_measure bin) bin
                                     then
                                       `(proj, rest, env') <- decode1 bin env;
                                         `(_, rest', env'0) <- decodeChecksum rest env';
                                         decode2 proj rest' env'0
                                     else None) P.
Proof.
  intros.
  assert (forall a' b ctx ctx',
             computes_to (encode1' (project a') ctx) (b, ctx')
             -> length_ByteString b = len_encode1 a') as H0'
      by (intros; eapply H0; eauto; apply refine_encode1; eauto).
  destruct (fun H4 => @compose_IPChecksum_encode_correct
                A A' P P_inv1 P_inv2 H project predicate
                predicate' predicate_rest' predicate_rest encode1'
                encode2 encoded_A_measure len_encode1
                len_encode2 H0' H1 H2 H3 H4 decode1 H5
                H6 H7 decode2 H8); [ | ].
  intros; eapply H4; eauto.
  apply refine_encode1; eauto.
  unfold encode_decode_correct_f; intuition.
  - eapply H9; eauto.
    unfold composeChecksum in *.
    unfold Bind2 in *; computes_to_inv; computes_to_econstructor.
    apply refine_encode1; eauto.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    rewrite <- H15'''; computes_to_econstructor.
  - eapply H10; eauto.
  - destruct (H10 _ _ _ _ _ _ H11 H13 H14); destruct_ex;
      eexists _, _; intuition eauto.
    unfold composeChecksum in *.
    unfold Bind2 in *; computes_to_inv; computes_to_econstructor.
    apply refine_encode1; eauto.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    instantiate (1 := x0); rewrite <- H17''';
      computes_to_econstructor.
Qed.

(*Lemma IPchecksum_Valid_OK_dep' :
  forall (b b' ext : ByteString),
    IPChecksum_ByteAligned b  (* Should be able to elide this assumption. *)
    -> IPChecksum_ByteAligned b'
    -> IPChecksum_Valid
         (bin_measure (transform (transform b (IPChecksum b b')) b'))
         (transform (transform (transform b (IPChecksum b b')) b') ext).
Proof.
  simpl; intros.
  destruct H0; destruct H.
  unfold IPChecksum, IPChecksum_Valid.
  pose proof transform_assoc as H'; simpl in H'; rewrite H'.
  rewrite ByteString2ListOfChar_Over with (ext := ext); try eassumption.
  rewrite !ByteString_transformer_eq_app; try eassumption.
  pose proof ByteString2ListOfChar_eq' as H''; simpl in H''.
  rewrite H''.
  unfold byteString at 1.
  unfold byteString at 1.
  unfold byteString at 1.
  rewrite onesComplement_commute; eauto.
  rewrite app_assoc.
  rewrite H''.
  unfold byteString at 5.
  rewrite onesComplement_commute with (b := byteString b); eauto.
  rewrite H; find_if_inside; try congruence.
  simpl; rewrite app_nil_r.
  apply onesComplement_onesComplement.
  destruct_ex; eexists (x + x0); rewrite app_length; rewrite H1, H2; omega.
  reflexivity.
  rewrite H; find_if_inside; try congruence.
  rewrite !app_length.
  simpl; destruct_ex; exists (x0 + 1).
  rewrite H2, even_IPChecksum; omega.
  reflexivity.
  find_if_inside.
  reflexivity.
  congruence.
  rewrite H; find_if_inside; try congruence.
  pose proof transform_id_right as H''; simpl in H''; rewrite H''; eauto.
  rewrite encode_word'_padding; reflexivity.
  rewrite H; find_if_inside; try congruence.
  pose proof transform_id_right as H''; simpl in H''; rewrite H''; eauto.
  rewrite transform_padding_eq; rewrite H.
  rewrite encode_word'_padding; reflexivity.
  rewrite H; find_if_inside; try congruence.
  pose proof transform_id_right as H''; simpl in H''; rewrite H''; eauto.
  rewrite transform_padding_eq.
  rewrite transform_padding_eq; rewrite H.
  rewrite encode_word'_padding.
  rewrite H0; reflexivity.
Qed. *)

Lemma compose_IPChecksum_encode_correct_dep
  : forall (A : Type)
           (B := ByteString)
           (trans : Transformer B := transformer)
           (trans_opt : QueueTransformerOpt trans bool :=
              ByteString_QueueTransformerOpt)
           (bextra : B)
           (bextra_len : nat)
           (checksum_Valid := fun n b' => IPChecksum_Valid (bextra_len + n) (transform bextra b'))
           (checksum_Valid_dec := fun n b' => IPChecksum_Valid_dec (bextra_len + n) (transform bextra b'))
           (A' : Type)
           (P : CacheDecode -> Prop)
           (P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop)
           (decodeChecksum := decode_IPChecksum),
    cache_inv_Property P
                       (fun P0 : CacheDecode -> Prop =>
                          P_inv1 P0 /\
                          P_inv2 P0 /\
                          (forall (b : B) (ctx : CacheDecode) (u : ()) (b' : B) (ctx' : CacheDecode),
                              decodeChecksum b ctx = Some (u, b', ctx') -> P0 ctx -> P0 ctx')) ->
    forall (project : A -> A') (predicate : A -> Prop)
           (predicate' : A' -> Prop) (predicate_rest' : A -> B -> Prop)
           (predicate_rest : A' -> B -> Prop)
           (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
           (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
           (encoded_A_measure : B -> nat)
           (len_encode1 : A -> nat)
           (len_encode2 : A -> nat)
           (bextra_len_eq : length_ByteString bextra = bextra_len)
           (bextra_ByteAligned : NPeano.modulo bextra_len 8 = 0),
      (forall a' b ctx ctx',
          computes_to (encode1 (project a') ctx) (b, ctx')
          -> length_ByteString b = len_encode1 a')
      -> (forall a b ctx ctx',
             computes_to (encode2 a ctx) (b, ctx')
             -> length_ByteString b = len_encode2 a)
      -> (forall a, NPeano.modulo (len_encode1 a) 8 = 0)
      -> (forall a, NPeano.modulo (len_encode2 a) 8 = 0)
      -> (forall (a : A) (ctx ctx' ctx'' : CacheEncode) c (b b'' ext : B),
             encode1 (project a) ctx ↝ (b, ctx') ->
             encode2 a ctx' ↝ (b'', ctx'') ->
             predicate a ->
             len_encode1 a + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform (encode_checksum _ _ _ 16 c) b'')) ext)) ->
      forall decode1 : B -> CacheDecode -> option (A' * B * CacheDecode),
        (cache_inv_Property P P_inv1 ->
         encode_decode_correct_f _ transformer predicate' predicate_rest encode1 decode1 P) ->
        (forall data : A, predicate data -> predicate' (project data)) ->
        (forall (a' : A') (b : ByteString) (a : A) (ce ce' ce'' : CacheEncode)
                (b' b'' : ByteString) c,
            encode1 a' ce ↝ (b', ce') ->
            project a = a' ->
            predicate a ->
            encode2 a ce' ↝ (b'', ce'') ->
            predicate_rest' a b ->
            {c0 : word 16 |
             forall ext : ByteString,
               checksum_Valid (bin_measure (transform b' (transform (encode_checksum _ _ _ _ c0) b'')))
                              (transform (transform b' (transform (encode_checksum _ _ _ _ c0) b'')) ext)} ↝ c ->
            predicate_rest a' (transform (transform (encode_checksum _ _ _ _ c) b'') b)) ->
        forall decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode),
          (forall proj : A',
              predicate' proj ->
              cache_inv_Property P P_inv2 ->
              encode_decode_correct_f _ transformer
                                      (fun data : A => predicate data /\ project data = proj) predicate_rest' encode2
                                      (decode2 proj) P) ->
          encode_decode_correct_f _ transformer predicate predicate_rest'
                                  (fun data : A =>
                                     encode1 (project data) ThenChecksum checksum_Valid OfSize 16 ThenCarryOn encode2 data)
                                  (fun (bin : B) (env : CacheDecode) =>
                                     if checksum_Valid_dec (encoded_A_measure bin) bin
                                     then
                                       `(proj, rest, env') <- decode1 bin env;
                                         `(_, rest', env'0) <- decodeChecksum rest env';
                                         decode2 proj rest' env'0
                                     else None) P.
Proof.
  intros.
  eapply (@composeChecksum_encode_correct
            A B trans _ 16 checksum_Valid
            checksum_Valid_dec).
  - eassumption.
  - intros; rewrite !transform_measure.
    simpl; rewrite (H0 _ _ _ _ H9).
    simpl; rewrite (H1 _ _ _ _ H10).
    erewrite <- H4.
    2: eassumption.
    unfold encode_checksum.
    rewrite length_encode_word'.
    simpl; omega.
    eassumption.
    eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
  - intros; unfold decodeChecksum, IPChecksum, decode_IPChecksum,
            decode_unused_word, decode_unused_word'.
    rewrite <- !transform_assoc.
    unfold B in *.
    unfold encode_checksum.
    rewrite transformer_dequeue_encode_word'; simpl; eauto.
  - unfold decodeChecksum, IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
    unfold B in *.
    intros; destruct (WordOpt.transformer_dequeue_word 16 b) eqn : ? ;
      try discriminate; intuition.
    destruct p.
    simpl in H10.
    injection H10; intros.
    unfold encode_checksum.
    eexists w.
    erewrite (transformer_dequeue_word_inj _ b);
      [ | eapply Heqo
        | pose proof (@transformer_dequeue_encode_word' _ transformer _) as H';
          simpl in H'; eapply H' ].
    rewrite H12; reflexivity.
  - eassumption.
  - intros.
    unfold checksum_Valid, IPChecksum_Valid in *.
    rewrite <- bextra_len_eq in *.
    simpl bin_measure in *; simpl transform in *.
    rewrite <- transform_ByteString_measure in *.
    replace
      (length_ByteString
         (ByteString_append bextra
                            (ByteString_enqueue_ByteString x (ByteString_enqueue_ByteString (encode_checksum B trans trans_opt 16 c) x1))))
    with
    (length_ByteString
       (ByteString_enqueue_ByteString bextra
                                      (ByteString_enqueue_ByteString x (ByteString_enqueue_ByteString (encode_checksum B trans trans_opt 16 c) x1)))) in *.
    rewrite !ByteString_enqueue_ByteString_assoc in *.
    rewrite ByteString2ListOfChar_Over.
    rewrite ByteString2ListOfChar_Over in H12.
    eauto.
    rewrite !ByteString_enqueue_ByteString_padding_eq.
    apply H0 in H10.
    pose proof (H2 data).
    rewrite <- H10 in H13.
    unfold encode_checksum.
    rewrite encode_word'_padding.
    rewrite !padding_eq_mod_8.
    pose proof (H3 data).
    rewrite <- (H1 _ _ _ _ H11) in H14.
    rewrite H13, H14, bextra_ByteAligned.
    reflexivity.
    rewrite !ByteString_enqueue_ByteString_padding_eq.
    apply H0 in H10.
    pose proof (H2 data).
    rewrite <- H10 in H13.
    unfold encode_checksum.
    rewrite encode_word'_padding.
    rewrite !padding_eq_mod_8.
    pose proof (H3 data).
    rewrite <- (H1 _ _ _ _ H11) in H14.
    rewrite H13, H14, bextra_ByteAligned.
    reflexivity.
    rewrite !ByteString_enqueue_ByteString_measure.
    unfold ByteString_append.
    rewrite length_ByteString_push_word.
    rewrite length_ByteString_append.
    unfold length_ByteString at 1.
    rewrite !ByteString_enqueue_ByteString_measure.
    omega.
Qed.

Lemma compose_IPChecksum_encode_correct_dep'
  : forall (A : Type)
           (B := ByteString)
           (trans : Transformer B := transformer)
           (trans_opt : QueueTransformerOpt trans bool :=
              ByteString_QueueTransformerOpt)
           (bextra : B)
           (bextra_len : nat)
           (checksum_Valid := fun n b' => IPChecksum_Valid (bextra_len + n) (transform bextra b'))
           (checksum_Valid_dec := fun n b' => IPChecksum_Valid_dec (bextra_len + n) (transform bextra b'))
           (A' : Type)
           (P : CacheDecode -> Prop)
           (P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop)
           (decodeChecksum := decode_IPChecksum),
    cache_inv_Property P
                       (fun P0 : CacheDecode -> Prop =>
                          P_inv1 P0 /\
                          P_inv2 P0 /\
                          (forall (b : B) (ctx : CacheDecode) (u : ()) (b' : B) (ctx' : CacheDecode),
                              decodeChecksum b ctx = Some (u, b', ctx') -> P0 ctx -> P0 ctx')) ->
    forall (project : A -> A') (predicate : A -> Prop)
           (predicate' : A' -> Prop) (predicate_rest' : A -> B -> Prop)
           (predicate_rest : A' -> B -> Prop)
           (encode1 : A -> CacheEncode -> Comp (B * CacheEncode))
           (encode1' : A' -> CacheEncode -> Comp (B * CacheEncode))
           (refine_encode1 : forall a ctx,
               refineEquiv (encode1 a ctx) (encode1' (project a) ctx))
           (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
           (encoded_A_measure : B -> nat)
           (len_encode1 : A -> nat)
           (len_encode2 : A -> nat)
           (bextra_len_eq : length_ByteString bextra = bextra_len)
           (bextra_ByteAligned : NPeano.modulo bextra_len 8 = 0),
      (forall a' b ctx ctx',
          computes_to (encode1 a' ctx) (b, ctx')
          -> length_ByteString b = len_encode1 a')
      -> (forall a b ctx ctx',
             computes_to (encode2 a ctx) (b, ctx')
             -> length_ByteString b = len_encode2 a)
      -> (forall a, NPeano.modulo (len_encode1 a) 8 = 0)
      -> (forall a, NPeano.modulo (len_encode2 a) 8 = 0)
      -> (forall (a : A) (ctx ctx' ctx'' : CacheEncode) c (b b'' ext : B),
             encode1 a ctx ↝ (b, ctx') ->
             encode2 a ctx' ↝ (b'', ctx'') ->
             predicate a ->
             len_encode1 a + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform (encode_checksum _ _ _ 16 c) b'')) ext)) ->
      forall decode1 : B -> CacheDecode -> option (A' * B * CacheDecode),
        (cache_inv_Property P P_inv1 ->
         encode_decode_correct_f _ transformer predicate' predicate_rest encode1' decode1 P) ->
        (forall data : A, predicate data -> predicate' (project data)) ->
        (forall (a' : A') (b : ByteString) (a : A) (ce ce' ce'' : CacheEncode)
                (b' b'' : ByteString) c,
            encode1' a' ce ↝ (b', ce') ->
            project a = a' ->
            predicate a ->
            encode2 a ce' ↝ (b'', ce'') ->
            predicate_rest' a b ->
            {c0 : word 16 |
             forall ext : ByteString,
               checksum_Valid (bin_measure (transform b' (transform (encode_checksum _ _ _ _ c0) b'')))
                              (transform (transform b' (transform (encode_checksum _ _ _ _ c0) b'')) ext)} ↝ c ->
            predicate_rest a' (transform (transform (encode_checksum _ _ _ _ c) b'') b)) ->
        forall decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode),
          (forall proj : A',
              predicate' proj ->
              cache_inv_Property P P_inv2 ->
              encode_decode_correct_f _ transformer
                                      (fun data : A => predicate data /\ project data = proj) predicate_rest' encode2
                                      (decode2 proj) P) ->
          encode_decode_correct_f _ transformer predicate predicate_rest'
                                  (fun data : A =>
                                     encode1 data ThenChecksum checksum_Valid OfSize 16 ThenCarryOn encode2 data)
                                  (fun (bin : B) (env : CacheDecode) =>
                                     if checksum_Valid_dec (encoded_A_measure bin) bin
                                     then
                                       `(proj, rest, env') <- decode1 bin env;
                                         `(_, rest', env'0) <- decodeChecksum rest env';
                                         decode2 proj rest' env'0
                                     else None) P.
Proof.
  intros.
  assert (forall (a : A) (ctx ctx' ctx'' : CacheEncode) (c : word 16) (b b'' ext : B),
             encode1' (project a) ctx ↝ (b, ctx') ->
             encode2 a ctx' ↝ (b'', ctx'') ->
             predicate a ->
             len_encode1 a + len_encode2 a + 16 =
             encoded_A_measure (transform (transform b (transform (encode_checksum B trans trans_opt 16 c) b'')) ext)) as H4'
      by (intros; eapply H4; eauto; eapply refine_encode1; eauto).
    assert (forall a' b ctx ctx',
             computes_to (encode1' (project a') ctx) (b, ctx')
             -> length_ByteString b = len_encode1 a') as H0'
      by (intros; eapply H0; eauto; apply refine_encode1; eauto).
  generalize refine_encode1
             (@compose_IPChecksum_encode_correct_dep
                A bextra bextra_len A' P P_inv1 P_inv2 H project predicate
                predicate' predicate_rest' predicate_rest encode1'
                encode2 encoded_A_measure len_encode1
                len_encode2 bextra_len_eq bextra_ByteAligned
                H0' H1 H2 H3 H4' decode1 H5
                H6 H7 decode2 H8); clear;
    unfold encode_decode_correct_f; intuition.
  - eapply H0; eauto.
    unfold composeChecksum in *.
    unfold Bind2 in *; computes_to_inv; computes_to_econstructor.
    apply refine_encode1; eauto.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    rewrite <- H4'''; computes_to_econstructor.
  - eapply H1; eauto.
  - destruct (H1 _ _ _ _ _ _ H H2 H3); destruct_ex;
      eexists _, _; intuition eauto.
    unfold composeChecksum in *.
    unfold Bind2 in *; computes_to_inv; computes_to_econstructor.
    apply refine_encode1; eauto.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    instantiate (1 := x0); rewrite <- H6''';
      computes_to_econstructor.
Qed.

Ltac calculate_length_ByteString :=
  intros;
  match goal with
  | H : computes_to _ _ |- _ =>
    first [ eapply (length_ByteString_composeChecksum _ _ _ _ _ _ _ _ _ H);
            try (simpl transform_id; rewrite length_ByteString_ByteString_id)
          | eapply (length_ByteString_composeIf _ _ _ _ _ _ _ H);
            try (simpl transform_id; rewrite length_ByteString_ByteString_id)
          | eapply (length_ByteString_compose _ _ _ _ _ _ _ H);
            try (simpl transform_id; rewrite length_ByteString_ByteString_id)
          | eapply (fun H' H'' => length_ByteString_encode_option _ _ _ _ _ _ _ H' H'' H)
          | eapply (length_ByteString_unused_word _ _ _ _ H)
          | eapply (length_ByteString_bool _ _ _ _ H)
          | eapply (length_ByteString_word _ _ _ _ _ H)
          | eapply (fun H' => length_ByteString_encode_list _ _ _ _ _ _ H' H)
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



Ltac solve_mod_8 :=
  intros; cbv beta; simpl transform_id;
  repeat first [
           rewrite plus_32_mod_8
         | rewrite plus_16_mod_8
         | rewrite length_ByteString_ByteString_id
         | rewrite (NPeano.Nat.mod_mul _ 8 (NPeano.Nat.neq_succ_0 7))
         | rewrite mult_32_mod_8
         | rewrite mult_16_mod_8
         | rewrite mult_8_mod_8
         | rewrite <- plus_n_O
         | reflexivity ].

Lemma refineEquiv_ThenC_no_dep {B Env}
      {transformer : Transformer B}
  : forall (encode1 : Env -> Comp (B * Env))
           {A}
           (encode2 : A -> Env -> Comp (B * Env))
           {A'}
           (f : A -> A')
           (encode2' encode' : A' -> Env -> Comp (B * Env))
           (H : forall a env, refineEquiv (encode2 a env) (encode2' (f a) env))
           (H : forall a' env, encode' a' env = (fun a' => encode1 ThenC (encode2' a')) a' env)
           (a : A)
           (env : Env),

    refineEquiv ((encode1 ThenC (encode2 a)) env)
                (encode' (f a) env).
Proof.
  intros; unfold compose, Bind2; intros.
  setoid_rewrite H0.
  setoid_rewrite H; reflexivity.
Qed.

Lemma refineEquiv_ThenC {A B Env}
      {transformer : Transformer B}
  : forall (encode1 : A -> Env -> Comp (B * Env))
           (encode2 : A -> Env -> Comp (B * Env))
           {A' A''}
           (f : A -> A')
           (f' : A -> A'')
           (encode1' : A' -> Env -> Comp (B * Env))
           (encode2' : A'' -> Env -> Comp (B * Env))
           (encode' : (A' * A'') -> Env -> Comp (B * Env))
           (H1 : forall a env,
               refineEquiv (encode1 a env) (encode1' (f a) env))
           (H2 : forall a env,
               refineEquiv (encode2 a env) (encode2' (f' a) env))
           (H' : forall aa' env,
               encode' aa' env
               = (encode1' (fst aa') ThenC (encode2' (snd aa'))) env)
           (a : A)
           (env : Env),
    refineEquiv ((encode1 a ThenC encode2 a) env)
                (encode' ((fun a => (f a, f' a)) a) env).
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
  | |- refineEquiv ((?encode1 ThenC ?encode2) ?ctx) ?z =>
    let encode2' := (eval pattern a in encode2) in
    match encode2' with
    | ?encode2'' a =>
      eapply (@refineEquiv_ThenC_no_dep _ _ _ encode1 _ encode2'');
      [ clear | higher_order_reflexivity ]
    end; cbv beta; clear
  | |- refineEquiv ((?encode1 ThenC ?encode2) ?ctx) ?z =>
    let encode1' := (eval pattern a in encode1) in
    let encode2' := (eval pattern a in encode2) in
    match encode1' with
    | ?encode1'' a =>
      match encode2' with
      | ?encode2'' a =>
        eapply (@refineEquiv_ThenC _ _ _ _ encode1'' encode2'');
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

Ltac apply_IPChecksum Len_OK :=
  match goal with
    H : cache_inv_Property _ _
    |- context[
           encode_decode_correct_f _ _ _ _
                                   (fun data c =>
                                      (_ ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn _) c) _ _] =>
    eapply compose_IPChecksum_encode_correct';
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
           encode_decode_correct_f _ _ _ _
                                   (fun data c =>
                                      (_ ThenChecksum _ OfSize 16 ThenCarryOn _) c) _ _] =>
    eapply compose_IPChecksum_encode_correct_dep';
    [ apply H
    | repeat resolve_Checksum
    | cbv beta; unfold Domain; simpl;
      simpl transform; unfold encode_word;
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
  end.
