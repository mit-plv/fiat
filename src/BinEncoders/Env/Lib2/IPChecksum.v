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
        Fiat.BinEncoders.Env.Automation.SolverOpt
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

Fixpoint transformer_pop_word {B}
         {transformer : Transformer B}
         {transformer_opt : TransformerUnitOpt transformer bool}
         (sz : nat)
         (b : B)
  : (word sz * B) :=
  match sz with
  | 0 => (WO, b)
  | S sz' =>
    match transform_pop_opt b with
    | Some (v, b') =>
      let (w', b'') := transformer_pop_word sz' b' in
      (WS v w', b'')
    | _ => (wzero (S sz'), b)
    end
  end.

Lemma transformer_pop_push_word
      (sz' : nat)
    : forall (w : word sz') (ext : ByteString),
      transformer_pop_word sz' (ByteString_push_word w ext) = (w, ext).
  Proof.
    induction sz'; simpl; intros.
    - rewrite (shatter_word w); eauto.
    - rewrite (shatter_word w); simpl.
      rewrite ByteString_transform_push_pop_opt.
      rewrite IHsz'; eauto.
  Qed.

Fixpoint ByteString2ListOfChar (n : nat)
           (b : ByteString) : list char :=
  match n with
  | 0 => nil
  | S (S (S (S (S (S (S (S n'))))))) =>
    let (c, b') := transformer_pop_word 8 b in
    cons c (ByteString2ListOfChar n' b')
  | S n' =>
    let (c, b') := transformer_pop_word 8 b in
    cons c (ByteString2ListOfChar n' b')
  end.

Lemma ByteString2ListOfChar_push_char
  : forall n c b,
    ByteString2ListOfChar
      (8 + n)
      (ByteString_push_char c b) = (c :: ByteString2ListOfChar n b)%list.
Proof.
  Local Opaque transformer_pop_word.
  simpl.
  unfold ByteString_push_char.
  pose proof transformer_pop_push_word as H'; simpl in H';
    intros.
  rewrite H'; f_equal.
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
    unfold ByteString_transformer.
    unfold Core.front, Core.byteString.
    rewrite (shatter_word front).
    simpl ByteString_push_word.
    simpl fold_right.
    cbv beta.
    rewrite (ByteString2ListOfChar_push_char ((|byteString |) * 8) a).
    f_equal.
    rewrite Mult.mult_comm; reflexivity.
Qed.

Corollary ByteString2ListOfChar_eq'
  : forall (b : ByteString),
    padding b = 0 ->
    ByteString2ListOfChar (bin_measure b) b =
    byteString b.
Proof.
  intros.
  erewrite <- ByteString2ListOfChar_eq with (ext := transform_id); auto.
  rewrite transform_id_right; eauto.
Qed.

Definition IPChecksum (b b' : ByteString) : ByteString :=
  let b'' := if Peano_dec.eq_nat_dec (padding b) 0 then transform_id
                    else encode_word' _ (wzero (8 - (padding b))) in
  transform b''
    (encode_word' _ (wnot (onesComplement
                             (ByteString2ListOfChar (bin_measure (transform b b')) (transform b b'))))).

Definition transformer : Transformer ByteString := ByteStringTransformer.

Lemma onesComplement_commute :
  forall b b',
    (exists n, length b = 2 * n)
    -> (exists n, length b' = 2 * n)
    -> onesComplement (b ++ b') = onesComplement (b' ++ b).
Proof.
  intros; unfold onesComplement.
  eapply checksum_app; eauto.
Qed.

Lemma length_encode_word' sz :
  forall (w : word sz), bin_measure (encode_word' sz w) = sz.
Proof.
  induction sz; intros;
    rewrite (shatter_word w); simpl.
  - pose proof (transform_measure transform_id transform_id) as H';
      rewrite transform_id_left in H'.
    simpl bin_measure in H'; simpl transform_id in H'; omega.
  - pose proof measure_push as H'; simpl in H'.
    rewrite H', IHsz; omega.
Qed.

Lemma length_ByteString_IPChecksum
  : forall b b',
    padding b = 0
    -> length_ByteString (IPChecksum b b') = 16.
Proof.
  unfold IPChecksum; simpl; intros.
  erewrite transform_ByteString_measure.
  rewrite H; find_if_inside; try congruence.
  rewrite length_encode_word'; reflexivity.
Qed.

Transparent transformer_pop_word.

Lemma encode_word_S :
  forall n w, encode_word' (S n ) w =
              transform (encode_word' _ (WS (whd w) WO))
                        (encode_word' _ (wtl w)).
Proof.
  intros; rewrite (shatter_word w); simpl.
  induction n; simpl;
    rewrite (shatter_word (wtl w)).
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma encode_word_WO :
  forall w, encode_word' 0 w = transform_id.
Proof.
  intros; rewrite (shatter_word w); simpl; reflexivity.
Qed.

Lemma encode_char :
  forall n w, encode_word' (8 + n) w =
            transform {| front := WO;
               paddingOK := Lt.lt_0_Sn _;
               byteString := WS (whd w)
                             (WS (whd (wtl w))
                             (WS (whd (wtl (wtl w)))
                             (WS (whd (wtl (wtl (wtl w))))
                             (WS (whd (wtl (wtl (wtl (wtl w)))))
                             (WS (whd (wtl (wtl (wtl (wtl (wtl w))))))
                             (WS (whd (wtl (wtl (wtl (wtl (wtl (wtl w)))))))
                             (WS (whd (wtl (wtl (wtl (wtl (wtl (wtl (wtl w)))))))) WO))))))) :: nil |} (encode_word' _ (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl w))))))))).
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
Qed.

Lemma encode_word_hi_lo :
  forall w, encode_word' 16 w =
            {| front := WO;
               paddingOK := Lt.lt_0_Sn _;
               byteString := [lo8 w; hi8 w] |}.
Proof.
  intros; rewrite (encode_char 8).
  intros; rewrite (encode_char 0).
  simpl.
  unfold ByteString_transformer.
  rewrite !ByteString_push_char_id_right.
  rewrite encode_word_WO.
  simpl.
  f_equal.
  apply le_uniqueness_proof.
  simpl.
  unfold hi8, lo8.
  unfold split2.
  unfold split1.
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
Qed.

Lemma padding_list_into_ByteString :
  forall l,
    padding (list_into_ByteString l) = NPeano.modulo (length l) 8.
Proof.
  induction l.
  simpl; eauto.
  simpl length.
  destruct (Peano_dec.eq_nat_dec (NPeano.modulo (length l) 8) 7).
  - rewrite NatModulo_S_Full.
    simpl.
    unfold ByteString_push.
    destruct (Peano_dec.eq_nat_dec (padding (list_into_ByteString l)) 7).
    simpl; eauto.
    elimtype False.
    rewrite IHl in n; congruence.
    eauto.
  - rewrite NatModulo_S_Not_Full; eauto.
    unfold NPeano.Nat.modulo; rewrite <- IHl.
    simpl.
    unfold ByteString_push.
    rewrite <- IHl in n.
    destruct (Peano_dec.eq_nat_dec (padding (list_into_ByteString l)) 7);
      simpl; eauto.
    congruence.
Qed.

Lemma encode_word'_padding :
  forall sz (w : word sz),
    padding (encode_word' sz w) = NPeano.modulo sz 8.
Proof.
  intros; rewrite (ByteString_into_list_eq _).
  rewrite padding_list_into_ByteString.
  f_equal.
  induction w; simpl; eauto.
  unfold ByteString_push.
  symmetry; rewrite <- IHw at 1; clear IHw.
  unfold ByteString_into_list.
  destruct (Peano_dec.eq_nat_dec (padding (encode_word' n w)) 7);
    simpl; rewrite app_length; eauto.
  assert (|wordToList (front (encode_word' n w)) | = 7).
  destruct (encode_word' n w); simpl in *.
  subst; reflexivity.
  rewrite H.
  reflexivity.
Qed.

Lemma even_IPChecksum
  : forall w, (|byteString (encode_word' 16 w) |) = 2.
Proof.
  intros; pose proof (length_encode_word' 16 w) as H'''; simpl in H'''.
  unfold length_ByteString in H'''.
  setoid_rewrite encode_word'_padding in H'''; simpl in H'''.
  omega.
Qed.

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

Lemma ByteString_transformer_eq_app :
  forall (b b' : ByteString),
    padding b = 0
    -> padding b' = 0
    -> ByteString_transformer b b' =
       {| front := WO;
          paddingOK := Lt.lt_0_Sn _;
          byteString := byteString b ++ byteString b' |}.
Proof.
  destruct b; destruct b'; intros;
    simpl in *; subst.
  rewrite (shatter_word front0),
  (shatter_word front).
  unfold ByteString_transformer; simpl.
  rewrite ByteString_push_char_id_right; simpl; eauto.
  f_equal; apply le_uniqueness_proof.
Qed.

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

Lemma transform_padding_eq
  : forall b b',
    padding (transform b b') = NPeano.modulo (padding b + padding b') 8.
Proof.
  intros.
  rewrite (ByteString_into_list_eq b),
  (ByteString_into_list_eq b').
  rewrite ByteString_transform_list_into.
  rewrite !padding_list_into_ByteString.
  rewrite app_length.
  rewrite NPeano.Nat.add_mod; eauto.
Qed.

Lemma padding_eq_mod_8
  : forall b,
    padding b = NPeano.modulo (length_ByteString b) 8.
Proof.
  intros.
  rewrite (ByteString_into_list_eq b).
  unfold length_ByteString.
  rewrite !padding_list_into_ByteString.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_r; eauto.
  rewrite (fun c => proj2 (NPeano.Nat.mod_divides (8 * _) 8 c));
    eauto.
  rewrite <- plus_n_O, NPeano.Nat.mod_mod; eauto.
Qed.

Lemma add_padding_OK
  : forall b,
    padding (transform b
                       (if Peano_dec.eq_nat_dec (padding b) 0 then transform_id
                       else encode_word' _ (wzero (8 - (padding b))))) = 0.
Proof.
  intros; rewrite transform_padding_eq.
  find_if_inside; subst; simpl.
  - rewrite e; simpl; eauto.
  - pose proof (paddingOK b).
    destruct (padding b); simpl; eauto.
    destruct (n0); simpl; eauto.
    destruct (n0); simpl; eauto.
    destruct (n0); simpl; eauto.
    destruct (n0); simpl; eauto.
    destruct (n0); simpl; eauto.
    destruct (n0); simpl; eauto.
    destruct (n0); simpl; eauto.
    omega.
Qed.

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

Lemma padding_transform_commute
  : forall b b',
    padding (transform b b') = padding (transform b' b).
Proof.
  intros; rewrite !transform_padding_eq.
  rewrite Plus.plus_comm; eauto.
Qed.

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

Lemma transformer_pop_word_inj
  : forall sz w w' p,
    WordOpt.transformer_pop_word sz w = Some p
    -> WordOpt.transformer_pop_word sz w' = Some p
    -> w = w'.
Proof.
  induction sz; simpl; intros.
  - injections; eauto.
  - destruct (ByteString_pop w) as [ [? ?] | ] eqn : ? ;
      destruct (ByteString_pop w') as [ [? ?] | ] eqn : ?;
      try discriminate.
    destruct (WordOpt.transformer_pop_word sz b0) as [ [? ?] | ] eqn : ? ;
      destruct (WordOpt.transformer_pop_word sz b2) as [ [? ?] | ]  eqn : ? ;
      try discriminate.
    destruct p as [? ?].
    injection H; injection H0; intros; subst.
    pose proof (f_equal (@whd _) H4);
      pose proof (f_equal (@wtl _) H4);
      simpl in *; subst.
    assert (b0 = b2) by eauto.
    subst.
    eapply ByteString_transform_pop_opt_inj; eauto.
Qed.

Lemma decode_IPChecksum_pf'
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
Qed.

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
  rewrite transform_ByteString_measure; erewrite H0, H1; eauto.
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
  rewrite !transform_ByteString_measure; simpl.
  unfold encode_checksum.
  erewrite length_encode_word', H0, H1; eauto; omega.
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
                    ThenChecksum checksum ThenCarryOn rest) ctx) (b, ctx'')
    -> exists b' b'' ctx' ctx''' ,
      computes_to (rest' ctx') (b', ctx''')
      /\ computes_to (rest ctx''') (b'', ctx'')
      /\ forall ext, decode_unused_word' sz (transform b ext) = Some ((), transform (transform b' (transform (checksum (transform (encode_word' _ w) b') b'') b'')) ext).
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
  intros; rewrite <- transformer_pop_word_eq_decode_word'.
  rewrite <- !ByteString_transform_assoc.
  pose proof transformer_pop_encode_word' as H''; simpl in H'';
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
  rewrite <- !ByteString_transform_assoc.
  pose proof transformer_pop_encode_word' as H''; simpl in H'';
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
  eapply length_encode_word'.
Qed.

Lemma length_ByteString_word
  : forall sz (w : word sz) (b : ByteString) (ctx ctx' : CacheEncode),
    encode_word_Spec w ctx ↝ (b, ctx')
    -> length_ByteString b = sz.
Proof.
  unfold encode_word_Spec; simpl.
  intros; computes_to_inv; injections.
  eapply length_encode_word'.
Qed.

Lemma length_ByteString_bool
  : forall (b' : bool) (b : ByteString) (ctx ctx' : CacheEncode),
    encode_bool_Spec b' ctx ↝ (b, ctx')
    -> length_ByteString b = 1.
Proof.
  unfold encode_bool_Spec; simpl.
  intros; computes_to_inv; injections.
  eapply length_ByteString_push.
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
    erewrite transform_ByteString_measure.
    erewrite H; eauto.
    rewrite Mult.mult_succ_l.
    erewrite <- IHl; eauto with arith.
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

(*Lemma IPChecksum_unique
  : forall x x3 x1 ext u ctx ctx',
    IPChecksum_ByteAligned x
    -> IPChecksum_ByteAligned x1
    -> IPChecksum_Valid (length_ByteString (ByteString_transformer x (ByteString_transformer x3 x1)))
                     (ByteString_transformer x (ByteString_transformer x3 (ByteString_transformer x1 ext)))
    -> decode_IPChecksum (ByteString_transformer x3 (ByteString_transformer x1 ext)) ctx = Some (u, (ByteString_transformer x1 ext), ctx')
    -> x3 = IPChecksum x x1.
Proof.
Admitted. *)

Lemma compose_IPChecksum_encode_correct
  : forall (A : Type)
           (B := ByteString)
           (trans : Transformer B := transformer)
           (trans_opt : TransformerUnitOpt trans bool :=
              ByteString_TransformerUnitOpt)
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
         (len_encode1 : A' -> nat)
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
                encode1 (project a) ctx ↝ (b, ctx') ->
                encode2 a ctx' ↝ (b'', ctx'') ->
                predicate a ->
                len_encode1 (project a) + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform (encode_checksum _ _ _ 16 c) b'')) ext)) ->
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
    rewrite length_encode_word'.
    erewrite <- H4; eauto; try omega.
  - eassumption.
  - eassumption.
  - eassumption.
  - intros; unfold decodeChecksum, IPChecksum, decode_IPChecksum,
    decode_unused_word, decode_unused_word'.
    rewrite <- !transform_assoc.
    unfold B in *.
    rewrite transformer_pop_encode_word'; simpl; eauto.
  - unfold decodeChecksum, IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
    intros; destruct (WordOpt.transformer_pop_word 16 b) eqn : ? ;
      try discriminate; intuition.
    destruct p.
    injections.
    eexists w.
    erewrite (transformer_pop_word_inj _ b);
    [ | eauto
        | pose proof transformer_pop_encode_word' as H'; simpl in H';
          eapply H'].
    reflexivity.
  - eassumption.
  - intros.
    unfold IPChecksum_Valid in *.
    rewrite ByteString2ListOfChar_Over.
    rewrite ByteString2ListOfChar_Over in H12.
    eauto.
    simpl.
    rewrite !transform_padding_eq.
    apply H0 in H10.
    pose proof (H2 (project data)).
    rewrite <- H10 in H13.
    rewrite padding_eq_mod_8, H13.
    pose proof (H3 data).
    unfold encode_checksum.
    rewrite encode_word'_padding.
    rewrite <- (H1 _ _ _ _ H11) in H14.
    rewrite padding_eq_mod_8, H14.
    reflexivity.
    rewrite !transform_padding_eq.
    apply H0 in H10.
    pose proof (H2 (project data)).
    rewrite <- H10 in H13.
    rewrite padding_eq_mod_8, H13.
    pose proof (H3 data).
    unfold encode_checksum.
    rewrite encode_word'_padding.
    rewrite <- (H1 _ _ _ _ H11) in H14.
    rewrite padding_eq_mod_8, H14.
    reflexivity.
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
           (trans_opt : TransformerUnitOpt trans bool :=
              ByteString_TransformerUnitOpt)
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
         (len_encode1 : A' -> nat)
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
                encode1 (project a) ctx ↝ (b, ctx') ->
                encode2 a ctx' ↝ (b'', ctx'') ->
                predicate a ->
                len_encode1 (project a) + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform (encode_checksum _ _ _ 16 c) b'')) ext)) ->
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
    try omega.
    eassumption.
    eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
  - intros; unfold decodeChecksum, IPChecksum, decode_IPChecksum,
    decode_unused_word, decode_unused_word'.
    rewrite <- !transform_assoc.
    unfold B in *.
    rewrite transformer_pop_encode_word'; simpl; eauto.
  - unfold decodeChecksum, IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
    unfold B in *.
    intros; destruct (WordOpt.transformer_pop_word 16 b) eqn : ? ;
      try discriminate; intuition.
    destruct p.
    simpl in H10.
    injection H10; intros.
    unfold encode_checksum.
    eexists w.
    erewrite (transformer_pop_word_inj _ b);
        [ | eapply Heqo
      | pose proof (@transformer_pop_encode_word' _ transformer ByteString_TransformerUnitOpt) as H';
        simpl in H'; eapply H' ].
    rewrite H12; reflexivity.
  - eassumption.
  - intros.
    unfold checksum_Valid, IPChecksum_Valid in *.
    rewrite <- bextra_len_eq in *.
    simpl bin_measure in *; simpl transform in *.
    rewrite <- transform_ByteString_measure in *.
    rewrite !ByteString_transform_assoc in *.
    rewrite ByteString2ListOfChar_Over.
    rewrite ByteString2ListOfChar_Over in H12.
    eauto.
    rewrite !transform_padding_eq.
    apply H0 in H10.
    pose proof (H2 (project data)).
    rewrite <- H10 in H13.
    unfold encode_checksum.
    rewrite encode_word'_padding.
    rewrite !padding_eq_mod_8.
    pose proof (H3 data).
    rewrite <- (H1 _ _ _ _ H11) in H14.
    rewrite H13, H14, bextra_ByteAligned.
    reflexivity.
    rewrite !transform_padding_eq.
    apply H0 in H10.
    pose proof (H2 (project data)).
    rewrite <- H10 in H13.
    unfold encode_checksum.
    rewrite encode_word'_padding.
    rewrite !padding_eq_mod_8.
    pose proof (H3 data).
    rewrite <- (H1 _ _ _ _ H11) in H14.
    rewrite H13, H14, bextra_ByteAligned.
    reflexivity.
Qed.

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
