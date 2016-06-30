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
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Start Example Derivation. *)

Definition IPv4_Packet :=
  @Tuple <"TotalLength" :: word 16,
          "ID" :: word 16,
          "DF" :: bool, (* Don't fragment flag *)
          "MF" :: bool, (*  Multiple fragments flag *)
          "FragmentOffset" :: word 13,
          "TTL" :: char,
          "Protocol" :: EnumType ["ICMP"; "TCP"; "UDP"],
          (* So many to choose from: http://www.iana.org/assignments/protocol-numbers/protocol-numbers.xhtml*)
          "SourceAddress" :: word 32,
          "DestAddress" :: word 32,
          "Options" :: list (word 32)>.

Definition ProtocolTypeCodes : Vector.t char 3 :=
  [WO~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~1~0~0~0~1
  ].

Variable onesComplement : list char -> word 16.

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
    (encode_word' _ (onesComplement
                    (ByteString2ListOfChar (bin_measure (transform b b')) (transform b b')))).

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition IPv4_Packet_Header_Len (ip4 : IPv4_Packet) := 5 + |ip4!"Options"|.

Definition encode_IPv4_Packet_Spec (ip4 : IPv4_Packet)  :=
          (encode_word_Spec (natToWord 4 4)
    ThenC encode_nat_Spec 4 (IPv4_Packet_Header_Len ip4)
    ThenC encode_unused_word_Spec 8 (* TOS Field! *)
    ThenC encode_word_Spec ip4!"TotalLength"
    ThenC encode_word_Spec ip4!"ID"
    ThenC encode_unused_word_Spec 1 (* Unused flag! *)
    ThenC encode_bool_Spec ip4!"DF"
    ThenC encode_bool_Spec ip4!"MF"
    ThenC encode_word_Spec ip4!"FragmentOffset"
    ThenC encode_word_Spec ip4!"TTL"
    ThenC encode_enum_Spec ProtocolTypeCodes ip4!"Protocol"
    DoneC)
    ThenChecksum IPChecksum
    ThenCarryOn (encode_word_Spec ip4!"SourceAddress"
    ThenC encode_word_Spec ip4!"DestAddress"
    ThenC encode_list_Spec encode_word_Spec ip4!"Options"
    DoneC).

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4!"Options"|) 11 /\
  lt (20 + 4 * |ipv4!"Options"|) (wordToNat ipv4!"TotalLength").

Variable onesComplement_commute :
  forall b b',
    (exists n, length b = 2 * n)
    -> (exists n, length b' = 2 * n)
    -> onesComplement (b ++ b') = onesComplement (b' ++ b).

Variable onesComplement_onesComplement :
  forall b,
    (exists n, length b = 2 * n)
    -> onesComplement (b ++ (byteString (encode_word' 16 (onesComplement b)))) = wones 16.

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

Lemma even_IPChecksum
  : forall w, (|byteString (encode_word' 16 w) |) = 2.
Proof.
  intros; pose proof (length_encode_word' 16 w) as H'''; simpl in H'''.
  unfold length_ByteString in H'''.
  setoid_rewrite encode_word'_padding in H'''; simpl in H'''.
  omega.
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
  
Lemma IPchecksum_Valid_OK' :
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
Qed.

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
  forall checksum encode1 encode2 b (ctx ctx' : CacheEncode) n n' n'',
    computes_to (composeChecksum _ _ checksum encode1 encode2 ctx) (b, ctx')
    -> (forall ctx b ctx', computes_to (encode1 ctx) (b, ctx')
                           -> length_ByteString b = n)
    -> (forall ctx b ctx', computes_to (encode2 ctx) (b, ctx')
                           -> length_ByteString b = n')
    -> (forall ctx b b' ctx' ctx'',
           computes_to (encode1 ctx) (b, ctx')
           -> computes_to (encode2 ctx') (b', ctx'')
           -> length_ByteString (checksum b b') = n'')
    -> length_ByteString b = n + n' + n''.
Proof.
  unfold composeChecksum, Bind2; intros; computes_to_inv; injections.
  destruct v; destruct v0.
  rewrite !transform_ByteString_measure; simpl.
  erewrite H0, H2, H1; eauto; omega.
Qed.

Transparent pow2.
Arguments pow2 : simpl never.

Lemma computes_to_composeChecksum_decode_unused_word
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
Qed.

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

Lemma IPv4_Packet_encoded_measure_OK_1 :
  forall (a : IPv4_Packet) (ctx ctx' : ()) (b ext : ByteString)
         (a_OK : IPv4_Packet_OK a),
    encode_IPv4_Packet_Spec a ctx ↝ (b, ctx')
    -> IPv4_Packet_encoded_measure (ByteString_transformer b ext)
       = 32 * (IPv4_Packet_Header_Len a).
Proof.
  unfold encode_IPv4_Packet_Spec; intros.
  unfold IPv4_Packet_encoded_measure;
  eapply computes_to_composeChecksum_decode_unused_word in H;
    let H' := fresh in 
    destruct H as [? [? [? [? [? [? H'] ] ] ] ] ];
      rewrite H'; simpl.
  rewrite <- !ByteString_transform_assoc.
  intros.
  eapply computes_to_compose_decode_word in H;
    let H' := fresh in 
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold fst.
  rewrite wordToNat_natToWord_idempotent; try reflexivity.
  eauto using IPv4_Packet_Headiner_Len_Bound.
Qed. (* Qed takes forever. *)

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

Definition length_ByteString_ByteString_id
  : length_ByteString ByteString_id = 0 := eq_refl.

Ltac calculate_length_ByteString :=
  intros; 
  match goal with
  | H : computes_to _ _ |- _ => 
    first [ eapply (length_ByteString_composeChecksum _ _ _ _ _ _ _ _ _ H);
            try (simpl transform_id; rewrite length_ByteString_ByteString_id)
          | eapply (length_ByteString_compose _ _ _ _ _ _ _ H);
            try (simpl transform_id; rewrite length_ByteString_ByteString_id)
          | eapply (length_ByteString_unused_word _ _ _ _ H)
          | eapply (length_ByteString_bool _ _ _ _ H)
          | eapply (length_ByteString_word _ _ _ _ _ H)
          | eapply (fun H' => length_ByteString_encode_list _ _ _ _ _ _ H' H)
          | eapply (length_ByteString_ret _ _ _ _ H) ]; clear H
  end.

Lemma IPChecksum_unique
  : forall x x3 x1 ext u ctx ctx',
    IPChecksum_ByteAligned x
    -> IPChecksum_ByteAligned x1
    -> IPChecksum_Valid (length_ByteString (ByteString_transformer x (ByteString_transformer x3 x1)))
                     (ByteString_transformer x (ByteString_transformer x3 (ByteString_transformer x1 ext)))
    -> decode_IPChecksum (ByteString_transformer x3 (ByteString_transformer x1 ext)) ctx = Some (u, (ByteString_transformer x1 ext), ctx')
    -> ByteString_transformer x (ByteString_transformer x3 (ByteString_transformer x1 ext)) =
       ByteString_transformer x
                              (ByteString_transformer (IPChecksum x x1) (ByteString_transformer x1 ext)).
Proof.
Admitted.

Lemma compose_IPChecksum_encode_correct
  : forall (A : Type)
           (B := ByteString)
           (trans : Transformer B := transformer)
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
         -> (forall a, NPeano.modulo (len_encode1 a) 16 = 0)
         -> (forall a, NPeano.modulo (len_encode2 a) 16 = 0)
         -> (forall (a : A) (ctx ctx' ctx'' : CacheEncode) (b b' b'' ext : B),
                encode1 (project a) ctx ↝ (b, ctx') ->
                bin_measure b' = bin_measure (calculate_checksum b b'') ->
                encode2 a ctx' ↝ (b'', ctx'') ->
                predicate a ->
                len_encode1 (project a) + len_encode2 a + 16 = encoded_A_measure (transform (transform b (transform b' b'')) ext)) ->         
       forall decode1 : B -> CacheDecode -> option (A' * B * CacheDecode),
       (cache_inv_Property P P_inv1 ->
        encode_decode_correct_f _ transformer predicate' predicate_rest encode1 decode1 P) ->
       (forall data : A, predicate data -> predicate' (project data)) ->
       (forall (a' : A') (b : B) (a : A) (ce ce' ce'' : CacheEncode) (b' b'' : B),
        encode1 a' ce ↝ (b', ce') ->
        project a = a' ->
        predicate a ->
        encode2 a ce' ↝ (b'', ce'') ->
        predicate_rest' a b ->
        predicate_rest a' (transform (transform (calculate_checksum b' b'') b'') b)) ->
       forall decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode),
       (forall proj : A',
        predicate' proj ->
        cache_inv_Property P P_inv2 ->
        encode_decode_correct_f _ transformer
          (fun data : A => predicate data /\ project data = proj) predicate_rest' encode2
          (decode2 proj) P) ->       
       encode_decode_correct_f _ transformer predicate predicate_rest'
         (fun data : A =>
          encode1 (project data) ThenChecksum calculate_checksum ThenCarryOn encode2 data)
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
    simpl; rewrite (H1 _ _ _ _ H11).
    simpl in H10.
    rewrite H10, length_ByteString_IPChecksum.
    erewrite <- H4; eauto; try omega.
    
    eapply length_ByteString_IPChecksum_ByteAligned; eauto.
    erewrite H0; eauto.
  - intros; eapply IPchecksum_Valid_OK'.
    eapply length_ByteString_IPChecksum_ByteAligned; eauto.
    erewrite H0; eauto.
    eapply length_ByteString_IPChecksum_ByteAligned; eauto.
    erewrite H1; eauto.
  - eassumption.
  - eassumption.
  - eassumption.
  - intros; eapply decode_IPChecksum_pf; eauto.
    eapply length_ByteString_IPChecksum_ByteAligned; eauto.
    erewrite H0; eauto.
  - unfold decodeChecksum, IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
    intros; destruct (WordOpt.transformer_pop_word 16 b) eqn : ? ;
      try discriminate; intuition.
    destruct p.
    injections.
    eexists (encode_word' 16 w).
    erewrite (transformer_pop_word_inj _ b); 
      [ | eassumption
        | pose proof transformer_pop_encode_word' as H'; simpl in H'; 
          eapply H'].
    split; intros; eauto.
    unfold calculate_checksum.
    rewrite length_ByteString_IPChecksum.
    apply length_encode_word'.
    eapply length_ByteString_IPChecksum_ByteAligned;
      erewrite H0; eauto.
  - eassumption.
  - intros; erewrite IPChecksum_unique; try eassumption.
    reflexivity.
    eapply length_ByteString_IPChecksum_ByteAligned;
      erewrite H0; eauto.
    eapply length_ByteString_IPChecksum_ByteAligned;
      erewrite H1; eauto.
Qed. 

Lemma plus_32_mod_16 :
  forall n, NPeano.modulo (32 + n) 16 = NPeano.modulo n 16.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
Qed.

Lemma mult_16_mod16 :
  forall n n', NPeano.modulo (n' * 16 + n) 16 = NPeano.modulo n 16.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
  rewrite NPeano.Nat.mod_mul; eauto.
Qed.

Lemma mult_32_mod16 :
  forall n n', NPeano.modulo (n' * 32 + n) 16 = NPeano.modulo n 16.
Proof.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
  pose proof (NPeano.Nat.mod_mul (2 * n') 16) as H'';
    rewrite <- Mult.mult_assoc, Mult.mult_comm, <- Mult.mult_assoc in H''.
  unfold mult at 2 in H''; simpl plus in H''.
  simpl rewrite H''; eauto.
Qed.

Ltac solve_mod_16 := 
  intros; cbv beta; simpl transform_id;
    repeat first [
             rewrite plus_32_mod_16
           | rewrite length_ByteString_ByteString_id
           | rewrite mult_32_mod16
           | rewrite mult_16_mod16
           | reflexivity ].

Definition EthernetHeader_decoder
  : { decodePlusCacheInv |
      exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
         -> encode_decode_correct_f _ transformer IPv4_Packet_OK (fun _ _ => True)
                                    encode_IPv4_Packet_Spec
                                    (fst decodePlusCacheInv) (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  eexists (_, _); intros; eexists _; split; simpl.
  unfold encode_IPv4_Packet_Spec; pose_string_ids.
  intro.
  let p := (eval unfold Domain in (fun ip4 : IPv4_Packet => (|ip4!StringId11|, (ip4!StringId, (ip4!StringId0, (ip4!StringId1,
                                                                                                               (ip4!StringId2, (ip4!StringId3, (ip4!StringId4, ip4!StringId5))))))))) in
  let p := eval simpl in p in
      eapply (@compose_IPChecksum_encode_correct
                IPv4_Packet 
                (nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))))
                _ _ _ H
                p
                IPv4_Packet_OK
                _ _ _
                (fun data' : nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))) =>
                   (encode_word_Spec (natToWord 4 4)
                                   ThenC encode_nat_Spec 4 (5 + fst data')
                                   ThenC encode_unused_word_Spec 8 (* TOS Field! *)
                                   ThenC encode_word_Spec (fst (snd data'))
                                   ThenC encode_word_Spec (fst (snd (snd data')))
                                   ThenC encode_unused_word_Spec 1
                                   ThenC encode_bool_Spec (fst (snd (snd (snd data'))))
                                   ThenC encode_bool_Spec (fst (snd (snd (snd (snd data')))))
                                   ThenC encode_word_Spec (fst (snd (snd (snd (snd (snd data'))))))
                                   ThenC encode_word_Spec (fst (snd (snd (snd (snd (snd (snd data')))))))
                                   ThenC encode_enum_Spec ProtocolTypeCodes (snd (snd (snd (snd (snd (snd (snd data')))))))
                                   DoneC))).
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  solve_mod_16.
  solve_mod_16.
  { (* Grossest Proof By Far. *)
    intros; simpl transform_id; rewrite length_ByteString_ByteString_id.
    instantiate (1 := IPv4_Packet_encoded_measure).
    unfold IPv4_Packet_encoded_measure.
    rewrite <- !transform_assoc.
    eapply computes_to_compose_decode_unused_word in H0;
      let H' := fresh in 
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold DecodeBindOpt, If_Opt_Then_Else.
    eapply computes_to_compose_decode_word in H0;
      let H' := fresh in 
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold fst.
    rewrite wordToNat_natToWord_idempotent; try reflexivity;
      eauto using IPv4_Packet_Headiner_Len_Bound.
    rewrite !Plus.plus_assoc.
    rewrite Mult.mult_plus_distr_l.
    clear.
    repeat match goal with
             |- context [length ?l] => remember (length l)
           end.
    assert (n = n0) by (rewrite Heqn, Heqn0; f_equal).
    rewrite H.
    omega. }
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Nat_decode_correct.
  solve_data_inv.
  solve_data_inv.
  unfold encode_unused_word_Spec.
  apply_compose.
  eapply unused_word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply unused_word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply bool_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply bool_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Enum_decode_correct.
  Discharge_NoDupVector.
  solve_data_inv.
  solve_data_inv.
  unfold encode_decode_correct_f; intuition eauto.
  instantiate
    (1 := fun p b env => if Compare_dec.le_lt_dec proj 4 then None else _ p b env).
  simpl in *.
  rewrite <- H24; simpl.
  assert (a = proj - 5) by
      (rewrite <- H24; simpl; auto with arith).
  instantiate
    (1 := fun p b env => if Compare_dec.le_lt_dec (wordToNat proj0) (4 * proj) then None else _ p b env).
  rewrite H24; clear H24.
  revert H16.
  instantiate (2 := fun data : nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))) => lt (20 + 4 * (fst data)) (wordToNat (fst (snd data)))).
  rewrite H13, H23.
  simpl; intros.
  assert (~ le (wordToNat proj0) (4 * proj)) by omega.
  destruct (Compare_dec.le_lt_dec (wordToNat proj0) (4 * proj)).
  intuition.
  computes_to_inv; injections; subst; simpl.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  eexists env'; simpl; intuition eauto.
  instantiate (1 := fun proj6 ext env' => Some (proj - 5, (proj0, (proj1, (proj2, (proj3, (proj4, (proj5, proj6)))))), ext, env')).
  reflexivity.
  find_if_inside; try discriminate.
  find_if_inside; try discriminate.
  simpl in H14; injections; eauto.
  simpl in H14; repeat find_if_inside; try discriminate.
  injections.
  simpl.
  eexists _; eexists tt;
    intuition eauto; injections; eauto using idx_ibound_eq;
      try match goal with
            |-  ?data => destruct data;
                           simpl in *; eauto
          end.
  destruct env; computes_to_econstructor.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  reflexivity.
  omega.
  omega.
  omega.
  unfold IPv4_Packet_OK; clear; intros ? H'; destruct H' as [? ?]; repeat split.
  simpl.
  eassumption.
  simpl.
  revert H; unfold StringId11; unfold pow2, mult; simpl; auto with arith.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  intro; eapply FixList_decode_correct.
  revert H3; eapply Word_decode_correct.
  simpl in *; split.
  intuition eauto.
  eapply (f_equal fst H8).
  intros; eauto.
  simpl; intros; eauto using FixedList_predicate_rest_True.
  simpl; intros;
    unfold encode_decode_correct_f; intuition eauto.
  destruct data as [? [? [? [? [? [? [? [? [? [? [ ] ] ] ] ] ] ] ] ] ] ];
    unfold GetAttribute, GetAttributeRaw in *;
    simpl in *.
  pose proof (f_equal fst H14).
  pose proof (f_equal (fun z => fst (snd z)) H14).
  pose proof (f_equal (fun z => fst (snd (snd z))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd z)))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd z))))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd (snd z)))))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd (snd (snd z))))))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd (snd (snd z))))))) H14).
  pose proof (f_equal (fun z => snd (snd (snd (snd (snd (snd (snd z))))))) H14).
  simpl in *.
  clear H14.
  computes_to_inv; injections; subst; simpl.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  eexists env'; simpl; intuition eauto.
  simpl in *.
  simpl in H8; injections; eauto.
  simpl in H8; repeat find_if_inside; try discriminate.
  eexists _; eexists tt.
  injections; simpl in *; repeat split.
  destruct env; computes_to_econstructor.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  reflexivity.
  unfold GetAttribute, GetAttributeRaw; simpl.
  rewrite H5; eauto.
  intuition.
  simpl in *.
  unfold pow2 in H9; simpl in H9; auto with arith.
  omega.
  unfold GetAttribute, GetAttributeRaw.
  simpl.
  rewrite H5.
  omega.
  destruct proj as [? [? [? [? [? [? [? ?] ] ] ] ] ] ].
  simpl.
  unfold GetAttribute, GetAttributeRaw; simpl in *.
  repeat f_equal.
  eauto.
  simpl.
  repeat (instantiate (1 := fun _ => True)).
  unfold cache_inv_Property; intuition.
  Grab Existential Variables.
  decide equality.
  decide equality.
  exact (@weq _).
Defined.

Definition IPv4_decoder_impl :=
  Eval simpl in (fst (projT1 EthernetHeader_decoder)).

Print IPv4_decoder_impl.
  
