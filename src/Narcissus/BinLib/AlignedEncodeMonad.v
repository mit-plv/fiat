Require Import
        Bedrock.Word
        Coq.omega.Omega
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString.

Section AlignedEncodeM.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Definition AlignedEncodeM
             (n : nat) :=
    Vector.t char n (* Vector of bytes that is being written to *)
    -> nat          (* The current index *)
    -> CacheFormat  (* The current environment *)
    -> option (Vector.t char n * nat * CacheFormat) (* Error monad + value + updated index + updated cache *).

  Definition AppendAlignedEncodeM
             {n : nat}
             (a : AlignedEncodeM n)
             (b : AlignedEncodeM n)
    : AlignedEncodeM n :=
    fun v idx c => (Ifopt a v idx c  as a' Then (b (fst (fst a')) (snd (fst a')) (snd a')) Else None).

  Definition ReturnAlignedEncodeM
             {numBytes : nat}
    : AlignedEncodeM numBytes :=
    fun v idx c => Some (v, idx, c).

  Definition AlignedEncodeMEquiv
             {n}
             (a1 a2 : AlignedEncodeM n) : Prop :=
    forall v idx c, a1 v idx c = a2 v idx c.

  Lemma AlignedEncodeMEquiv_refl  {n}:
    forall (a : AlignedEncodeM n),
      AlignedEncodeMEquiv a a.
  Proof.
    unfold AlignedEncodeMEquiv; intros; reflexivity.
  Qed.

  Lemma AlignedEncodeMEquiv_sym  {n}:
    forall (a1 a2 : AlignedEncodeM n),
      AlignedEncodeMEquiv a1 a2 -> AlignedEncodeMEquiv a2 a1.
  Proof.
    unfold AlignedEncodeMEquiv; intros; congruence.
  Qed.

  Lemma AlignedEncodeMEquiv_trans  {n}:
    forall (a1 a2 a3 : AlignedEncodeM n),
      AlignedEncodeMEquiv a1 a2 ->
      AlignedEncodeMEquiv a2 a3 ->
      AlignedEncodeMEquiv a1 a3.
  Proof.
    unfold AlignedEncodeMEquiv; intros; congruence.
  Qed.

  Global Instance PreOrder_AlignedEncodeMEquiv  {n} :
    PreOrder (@AlignedEncodeMEquiv n) :=
    {| PreOrder_Reflexive := AlignedEncodeMEquiv_refl;
       PreOrder_Transitive := AlignedEncodeMEquiv_trans|}.

  Lemma AppendAlignedEncodeM_assoc {n}:
    forall (a : AlignedEncodeM n)
           (f : AlignedEncodeM n)
           (g : AlignedEncodeM n),
      AlignedEncodeMEquiv (AppendAlignedEncodeM (AppendAlignedEncodeM a f) g)
                          (AppendAlignedEncodeM a (AppendAlignedEncodeM f g)).
  Proof.
    unfold AppendAlignedEncodeM, AlignedEncodeMEquiv; simpl; intros.
    destruct (a v idx c); simpl; eauto.
  Qed.

  Lemma ReturnAlignedEncodeM_LeftUnit {n}:
    forall (f : AlignedEncodeM n),
      AlignedEncodeMEquiv (AppendAlignedEncodeM (@ReturnAlignedEncodeM _) f)
                          f.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma ReturnAlignedEncodeM_RightUnit {n}:
    forall (f : AlignedEncodeM n),
      AlignedEncodeMEquiv (AppendAlignedEncodeM f ReturnAlignedEncodeM) f.
  Proof.
    unfold ReturnAlignedEncodeM, AppendAlignedEncodeM, AlignedEncodeMEquiv; simpl; intros.
    destruct (f v idx c) as [ [ [? ?] ?] | ] ; simpl; reflexivity.
  Qed.

  Definition ThrowAlignedEncodeM
             {n : nat}
    : AlignedEncodeM n:=
    fun _ _ _ => None.

  Fixpoint set_nth'
           {n : nat}
           (v : Vector.t char n)
           (m : nat)
           (a : char)
    : Vector.t char n :=
    match m, v with
    | 0,  Vector.cons _ _ v' => Vector.cons _ a _ v'
    | S m', Vector.cons a' _ v' => Vector.cons _ a' _ (set_nth' v' m' a)
    | _, _ => @Vector.nil _
    end.

  Definition SetCurrentByte (* Sets a single byte at the current index and increments the current index. *)
             {n : nat}
             (a : char)
    : AlignedEncodeM n :=
    fun v idx ce => if (idx <? n) then Some (set_nth' v idx a, S idx, addE ce 8) else None.

  Definition SetByteAt (* Sets the bytes at the specified index and sets the current index
                          to the following position. *)
             {n : nat}
             (a : word 8)
             (idx' : nat)
    : AlignedEncodeM n :=
    fun v idx ce => if (NPeano.ltb idx' n) then Some (set_nth' v idx' a, S idx', addE ce 8) else None.

  (* Equivalence Criteria:
     A bit-aligned encoder and byte-aligned encoder are equivalent when
     - the byte aligned encoder fails when the bit aligned encoder would write past
       the end of the bytestring
     - encodes the same bit sequence values as the bit-aligned encoder (and who can
       say about the rest of the .
   *)

  Definition EncodeMEquivAlignedEncodeM
             (f : EncodeM ByteString)
             (f' : forall numBytes, AlignedEncodeM numBytes)
    := forall ce idx,
      (padding (fst (f ce)) = 0 ->
       forall (v1 : Vector.t char idx) v m v2,
       exists v',
         f' _ (Vector.append v1 (Vector.append (n := numBytes (fst (f ce))) (p := m)
                                               v v2)) idx ce = Some (v', idx + numBytes (fst (f ce)), snd (f ce)) /\
         ByteString_enqueue_ByteString (build_aligned_ByteString v1)
                                       (ByteString_enqueue_ByteString (fst (f ce))
                                                                      (build_aligned_ByteString v2))
         = build_aligned_ByteString v')%nat
      /\ (forall numBytes' v, 8 + 8 * numBytes' <= length_ByteString (fst (f ce)) + (8 * idx)
          -> f' numBytes' v idx ce = None)%nat
      /\ (forall numBytes' v, padding (fst (f ce)) <> 0 -> f' numBytes' v idx ce = None)%nat.

  Lemma EncodeMEquivAlignedEncodeM_trans :
    forall bit_decoder1 byte_decoder1 bit_decoder2 byte_decoder2,
      EncodeMEquivAlignedEncodeM bit_decoder1 byte_decoder1
      -> (forall ce, bit_decoder1 ce  = bit_decoder2 ce)
      -> (forall n, AlignedEncodeMEquiv (byte_decoder1 n) (byte_decoder2 n))
      -> EncodeMEquivAlignedEncodeM bit_decoder2 byte_decoder2.
  Proof.
    unfold EncodeMEquivAlignedEncodeM; intros; intuition.
    - revert v1 v v2 H2; rewrite <- ?H0, <- ?H1; intros.
      destruct (proj1 (H _ _) H2 v1 v m v2); intuition.
      eexists; intuition eauto.
      rewrite <- H1; eauto.
    - rewrite <- ?H0, <- ?H1; intros.
      eapply (proj1 (proj2 (H _ _))); rewrite H0; eauto.
    - rewrite <- ?H0, <- ?H1; intros.
      eapply H; rewrite ?H0; eauto.
  Qed.

  Local Arguments mult : simpl never.

  Definition AlignedEncode_Nil
             numBytes
    : AlignedEncodeM numBytes :=
    (fun v idx ce => (if idx <? S numBytes then @ReturnAlignedEncodeM _ v idx ce else None)).

  Lemma Return_EncodeMEquivAlignedEncodeM
    : EncodeMEquivAlignedEncodeM
        (fun (ce : CacheFormat) => (mempty, ce))
        AlignedEncode_Nil.
  Proof.
    unfold EncodeMEquivAlignedEncodeM, AlignedEncode_Nil, ReturnAlignedEncodeM;
      intros; simpl in *; intuition.
    - assert (idx < S (idx + m))%nat as H' by omega;
        rewrite <- ltb_lt in H'; rewrite H'.
      revert v.
      eapply Vector.case0; simpl.
      rewrite (plus_comm idx 0); simpl; eexists _; intuition.
      pose proof (mempty_left (build_aligned_ByteString v2)) as H'';
        simpl in H'';
      rewrite H'', <- build_aligned_ByteString_append; reflexivity.
    - destruct (idx <? (S numBytes')) eqn: ?; auto.
      rewrite ltb_lt in Heqb; omega.
  Qed.

  Definition AppendEncodeM
             {B}
             (B_Monoid : Monoid B)
             (encode1 encode2 : EncodeM B)
    : EncodeM B :=
    fun ce => let (c, ce') := encode1 ce in
                let (c', ce') := encode2 ce' in
                (mappend c c', ce').

  Lemma Append_EncodeMEquivAlignedEncodeM
        (encode1 encode2 : EncodeM ByteString)
        (encode1_aligned encode2_aligned : forall {numBytes}, AlignedEncodeM numBytes)
        (encode1_OK : forall ce, padding (fst (encode1 ce)) = 0)
    : EncodeMEquivAlignedEncodeM encode1 (@encode1_aligned)
      -> EncodeMEquivAlignedEncodeM encode2 (@encode2_aligned)
      -> EncodeMEquivAlignedEncodeM
           (AppendEncodeM _ encode1 encode2)
           (fun numBytes => AppendAlignedEncodeM encode1_aligned encode2_aligned).
  Proof.
    unfold EncodeMEquivAlignedEncodeM; intros; specialize (encode1_OK ce); split; intros.
    - destruct (H ce idx) as [ H' [? ?] ].
      revert v H' H1 H2 H3;
        unfold AppendEncodeM;
        destruct (encode1 ce) as [c' ce'] eqn: ? ;
        destruct (encode2 ce') eqn: ? ; simpl in *;
          rewrite numBytes_ByteString_enqueue_ByteString;
          intros; eauto.
      destruct (H0 ce' (idx + (numBytes c'))) as [H0' [? ?] ].
      erewrite <- padding_ByteString_enqueue_aligned_ByteString, Heqp0 in H0'.
      destruct (H' encode1_OK v1 (fst (Vector_split _ _ v)) _
                   (Vector.append (snd (Vector_split _ _ v)) v2)) as [? [? ?] ].
      assert (idx + (numBytes c' + (numBytes b + m)) =
              (idx + numBytes c') + (numBytes b + m)) by omega; simpl in *.
      destruct (H0' H1 (fst (Vector_split _ _ (eq_rect _ (Vector.t char) x _ H8)))
                    (fst (Vector_split _ _ (snd (Vector_split _ _ (eq_rect _ (Vector.t char) x _ H8)))))
                    _ (snd (Vector_split _ _ (snd (Vector_split _ _ (eq_rect _ (Vector.t char) x _ H8)))))
               ).
      assert (idx + numBytes c' + (numBytes b + m) =
              idx + (numBytes c' + numBytes b + m)) as H11 by omega.
      assert (idx + (numBytes c' + (numBytes b + m)) =
              (idx + (numBytes c' + numBytes b + m))) by omega; simpl in *.
      unfold AppendAlignedEncodeM.
      replace (encode1_aligned (idx + ((numBytes c' + numBytes b) + m))
                               (Vector.append v1 (Vector.append v v2)) idx ce)
        with (Some (eq_rect _ (Vector.t char) x _ H10, idx + numBytes c', ce'));
        simpl.
      + revert H10; rewrite <- H11; intros.
        rewrite (plus_assoc idx (numBytes c') (numBytes b)).
        eexists _; intuition.
        * etransitivity; [ | apply H12].
          f_equal.
          rewrite <- !Vector_split_append.
          f_equal; eapply UIP_dec; intros; decide equality.
        * rewrite <- H13.
          rewrite ByteString_enqueue_ByteString_assoc.
          rewrite ByteString_enqueue_ByteString_assoc.
          rewrite <- ByteString_enqueue_ByteString_assoc.
          symmetry in H7; destruct (build_aligned_ByteString_split' _ _ _ H7)
            as [? H']; symmetry in H'; destruct (build_aligned_ByteString_split _ _ _ H').
          revert H14 H7; clear.
          intro.
          revert H8 x v.
          assert (idx + (numBytes c' + (numBytes b + m)) - idx - (numBytes b + m) = numBytes c')
            as H'' by omega; revert x2 H14; rewrite H''; clear H''.
          generalize (numBytes c'); intros; subst.
          rewrite <- !build_aligned_ByteString_append in H7;
            apply build_aligned_ByteString_inj in H7; subst.
          rewrite <- !build_aligned_ByteString_append; repeat f_equal.
          erewrite Vector_append_assoc.
          rewrite <- Equality.transport_pp.
          erewrite (UIP_dec _ _ (eq_refl _)); simpl.
          rewrite <- Vector_append_split_fst; reflexivity.
          erewrite Vector_append_assoc.
          rewrite <- Equality.transport_pp.
          erewrite (UIP_dec _ _ (eq_refl _)); simpl.
          rewrite <- !Vector_append_split_snd; reflexivity.
      + generalize x H6 H10; clear; intros.
         replace (Some
                    (eq_rect (idx + (numBytes c' + (numBytes b + m)))
                             (Vector.t char) x (idx + (numBytes c' + numBytes b + m)) H10,
                     idx + numBytes c', ce')) with
             (eq_rect _ (fun x => option ((Vector.t char x) * nat * CacheFormat))%type (Some (x, idx + numBytes c', ce')) _ H10).
         rewrite <- H6.
         assert (idx + (numBytes c' + numBytes b + m) =
                 idx + (numBytes c' + (numBytes b + m))) by omega.
         replace (Vector.append v1 (Vector.append (fst (Vector_split (numBytes c') (numBytes b) v))
                                                  (Vector.append (snd (Vector_split (numBytes c') (numBytes b) v)) v2)))
           with (eq_rect _ (Vector.t char) (Vector.append v1 (Vector.append v v2)) _ H).
         assert (forall n m (H' : n = m) (v : Vector.t char n),
                    encode1_aligned m (eq_rect n (Vector.t char) v _ H') idx ce =
                    eq_rect n (fun x => option ((Vector.t char x) * nat * CacheFormat))%type
                            (encode1_aligned _ v idx ce) _ H') as H'
             by (intros ? ? H'; rewrite H'; reflexivity).
         rewrite H', <- Equality.transport_pp.
         erewrite (UIP_dec _ _ (eq_refl _)); reflexivity.
         assert (numBytes c' + numBytes b + m = numBytes c' + (numBytes b + m)) by omega.
         replace (Vector.append (fst (Vector_split (numBytes c') (numBytes b) v))
                                (Vector.append (snd (Vector_split (numBytes c') (numBytes b) v)) v2))
           with (eq_rect _ (Vector.t char) (Vector.append v v2) _ H0)
           by (erewrite Vector_append_assoc, <- Vector_split_append; reflexivity).
         erewrite Vector_append_assoc', Vector_append_assoc, <- Equality.transport_pp.
         reflexivity.
         destruct H10; reflexivity.
      + apply encode1_OK.
    - specialize (H ce idx);
        unfold AppendEncodeM;
        destruct (encode1 ce) as [c' ce'] eqn: ? ;
        destruct (encode2 ce') eqn: ? ; simpl in *; split; intros.
      + pose proof (proj1 H encode1_OK ).
        rewrite length_ByteString_enqueue_ByteString in H1.
        unfold AppendAlignedEncodeM; destruct (encode1_aligned numBytes' v idx ce) eqn: ? ;
          simpl; eauto.
        destruct (le_lt_dec (8 + 8 * numBytes')
                            (length_ByteString c' + 8 * idx)).
        { eauto; simpl in l; eapply (proj1 (proj2 H)) in l; rewrite l in Heqo; discriminate. }
        rewrite length_ByteString_no_padding in l by eauto.
        pose proof (proj1 (proj2 (H0 ce' (snd (fst p))))) as H'.
        assert (numBytes c' + idx < S numBytes')%nat by omega; clear l.
        assert (idx + numBytes c' <= numBytes')%nat by omega.
        destruct (Vector_split_lt _ _ H4 v) as [? [? [? [? ?] ] ] ].
        pose proof (proj1 (proj2 (H))) as H'' .
        destruct (H2 (fst (Vector_split _ _ x0)) (snd (Vector_split _ _ x0)) _ x1) as [v' [? ?] ].
        erewrite <- H'; f_equal; clear H'.
        * revert p Heqo H6.
          rewrite H5.
          rewrite <- x2; simpl; clear.
          rewrite Vector_append_assoc with (H := sym_eq (plus_assoc idx (numBytes c') x)), <- Vector_split_append.
          generalize v' (eq_sym (plus_assoc idx (numBytes c') x)).
          rewrite (plus_assoc idx (numBytes c') x).
          intros. erewrite (UIP_dec _ _ (eq_refl _)) in H6; simpl in H6.
          rewrite Heqo in H6; destruct p as [ [? ?] ?]; simpl in *; congruence.
        * rewrite Heqp0; simpl.
          replace (8 * snd (fst p)) with (length_ByteString c' + 8 * idx); try omega.
          rewrite length_ByteString_no_padding by eauto.
          revert p Heqo H6.
          rewrite H5.
          rewrite <- x2; simpl; clear.
          rewrite Vector_append_assoc with (H := sym_eq (plus_assoc idx (numBytes c') x)), <- Vector_split_append.
          generalize v' (eq_sym (plus_assoc idx (numBytes c') x)).
          rewrite (plus_assoc idx (numBytes c') x).
          intros. erewrite (UIP_dec _ _ (eq_refl _)) in H6; simpl in H6.
          rewrite Heqo in H6; destruct p as [ [? ?] ?]; simpl in *; injections.
          omega.
      + pose proof (proj1 H encode1_OK ).
        rewrite padding_ByteString_enqueue_aligned_ByteString in H1 by eauto.
        unfold AppendAlignedEncodeM; destruct (encode1_aligned numBytes' v idx ce) eqn: ? ;
          simpl; eauto.
        destruct (le_lt_dec (8 + 8 * numBytes')
                            (length_ByteString c' + 8 * idx)).
        { eauto; simpl in l; eapply (proj1 (proj2 H)) in l; rewrite l in Heqo; discriminate. }
        rewrite length_ByteString_no_padding in l by eauto.
        pose proof (proj2 (proj2 (H0 ce' (snd (fst p))))) as H'.
        assert (numBytes c' + idx < S numBytes')%nat by omega; clear l.
        assert (idx + numBytes c' <= numBytes')%nat by omega.
        destruct (Vector_split_lt _ _ H4 v) as [? [? [? [? ?] ] ] ].
        pose proof (proj2 (proj2 (H))) as H'' .
        destruct (H2 (fst (Vector_split _ _ x0)) (snd (Vector_split _ _ x0)) _ x1) as [v' [? ?] ].
        erewrite <- H'; f_equal; clear H'.
        * revert p Heqo H6.
          rewrite H5.
          rewrite <- x2; simpl; clear.
          rewrite Vector_append_assoc with (H := sym_eq (plus_assoc idx (numBytes c') x)), <- Vector_split_append.
          generalize v' (eq_sym (plus_assoc idx (numBytes c') x)).
          rewrite (plus_assoc idx (numBytes c') x).
          intros. erewrite (UIP_dec _ _ (eq_refl _)) in H6; simpl in H6.
          rewrite Heqo in H6; destruct p as [ [? ?] ?]; simpl in *; congruence.
        * rewrite Heqp0; simpl.
          replace (8 * snd (fst p)) with (length_ByteString c' + 8 * idx); try omega.
          rewrite !length_ByteString_no_padding; eauto.
          revert p Heqo H6.
          rewrite H5.
          rewrite <- x2; simpl; clear.
          rewrite Vector_append_assoc with (H := sym_eq (plus_assoc idx (numBytes c') x)), <- Vector_split_append.
          generalize v' (eq_sym (plus_assoc idx (numBytes c') x)).
          rewrite (plus_assoc idx (numBytes c') x).
          intros. erewrite (UIP_dec _ _ (eq_refl _)) in H6; simpl in H6.
          rewrite Heqo in H6; destruct p as [ [? ?] ?]; simpl in *; injections.
          omega.
      Grab Existential Variables.
      decide equality.
      decide equality.
      decide equality.
      decide equality.
      omega.
      decide equality.
      decide equality.
      omega.
      decide equality.
      omega.
  Qed.

  Definition CorrectAlignedEncoder
             (format : CacheFormat -> Comp (ByteString * CacheFormat))
             (encoder : forall sz, AlignedEncodeM sz)
    := {encoder' : _ &
                   (forall ce, refine (format ce) (ret (encoder' ce)))
                   /\ (forall ce, padding (fst (encoder' ce)) = 0)
                   /\ EncodeMEquivAlignedEncodeM encoder' encoder}.

  Lemma CorrectAlignedEncoderForDoneC
    : CorrectAlignedEncoder (fun e => Return (ByteString_id, e)) AlignedEncode_Nil.
  Proof.
    unfold CorrectAlignedEncoder; intros.
    eexists _; split; [ | split].
    intros; higher_order_reflexivity.
    reflexivity.
    eapply Return_EncodeMEquivAlignedEncodeM.
  Qed.

  (* Lemma CorrectAlignedEncoderForDoneC A
        (format_A : FormatM A ByteString)
        (encode_A : A -> forall sz, AlignedEncodeM sz)
        (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
    : CorrectAlignedEncoder
        (fun a => format_A a DoneC)
        encode_A.
  Proof.
    unfold CorrectAlignedEncoder; intros.
    destruct encoder_A_OK as [encoder [? [? ?] ] ].
    exists encoder; split; intros; eauto.
    intros; rewrite <- H.
    unfold compose, Bind2.
    setoid_rewrite Monad.refineEquiv_bind_unit; simpl.
    pose proof mempty_right as H'; simpl in H'; setoid_rewrite H'.
    intros v Comp_v; computes_to_inv; subst.
    destruct v; simpl in *; auto.
    computes_to_econstructor; eauto.
  Qed. *)

  Lemma CorrectAlignedEncoderForThenC
        (format_A format_B : CacheFormat -> Comp (ByteString * CacheFormat))
        (encode_A : forall sz, AlignedEncodeM sz)
        (encode_B : forall sz, AlignedEncodeM sz)
        (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
        (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
    : CorrectAlignedEncoder
        (format_B ThenC format_A)
        (fun sz => AppendAlignedEncodeM (encode_B sz) (encode_A sz)).
  Proof.
    unfold CorrectAlignedEncoder; intros.
    destruct encoder_A_OK as [encoder_A ?], encoder_B_OK as [encoder_B ?]; intuition
    eexists; split; [ | split]; intros.
    3: eapply Append_EncodeMEquivAlignedEncodeM.
    4: apply H5.
    4: apply H4.
    3: apply H0.
    unfold compose, Bind2.
    rewrite H1, Monad.refineEquiv_bind_unit.
    rewrite H, Monad.refineEquiv_bind_unit.
    simpl; unfold AppendEncodeM.
    destruct (encoder_B ce); simpl;
      destruct (encoder_A c); simpl; reflexivity.
    simpl; unfold AppendEncodeM.
    specialize (H0 ce); destruct (encoder_B ce); simpl.
    specialize (H3 c); destruct (encoder_A c); simpl.
    simpl in *.
    rewrite padding_ByteString_enqueue_aligned_ByteString; eauto.
  Qed.

End AlignedEncodeM.

Lemma refine_CorrectAlignedEncoder {cache : Cache}
  : forall format format' encode,
    (forall ce : CacheFormat, refine (format ce) (format' ce))
    -> (CorrectAlignedEncoder format' encode)
    -> (CorrectAlignedEncoder format encode).
Proof.
  unfold CorrectAlignedEncoder; intros.
  destruct X; eexists; intuition.
  - rewrite H; eauto.
Qed.

Lemma CorrectAlignedEncoderThenCAssoc {cache : Cache}
      (format_A format_B format_C : CacheFormat -> Comp (ByteString * CacheFormat))
      (encode : forall sz, AlignedEncodeM sz)
  : CorrectAlignedEncoder
      ((format_A ThenC format_B) ThenC format_C)
      encode
    -> CorrectAlignedEncoder
         (format_A ThenC format_B ThenC format_C)
         encode.
Proof.
  intros; eapply refine_CorrectAlignedEncoder; eauto.
  unfold compose; intros.
  unfold Bind2.
  repeat setoid_rewrite Monad.refineEquiv_bind_bind.
  setoid_rewrite Monad.refineEquiv_bind_unit; simpl; f_equiv; intro.
  simpl; f_equiv; intro.
  simpl; f_equiv; intro.
  rewrite ByteString_enqueue_ByteString_assoc; reflexivity.
Qed.

Corollary Guarded_CorrectAlignedEncoderThenCAssoc {cache : Cache}
          (format_A format_B format_C : CacheFormat -> Comp (ByteString * CacheFormat))
          (encode : forall sz, AlignedEncodeM sz)
  : (forall ce bs ce', computes_to (format_A ce) (bs, ce') ->
                       length_ByteString bs < 8)%nat
    -> CorrectAlignedEncoder
         ((format_A ThenC format_B) ThenC format_C)
         encode
    -> CorrectAlignedEncoder
         (format_A ThenC format_B ThenC format_C)
         encode.
Proof.
  intros; eapply CorrectAlignedEncoderThenCAssoc; eauto.
Qed.

Lemma CorrectAlignedEncoderThenCAssoc' {cache : Cache}
      (format_A format_B format_C : CacheFormat -> Comp (ByteString * CacheFormat))
      (encode : forall sz, AlignedEncodeM sz)
  : CorrectAlignedEncoder
      (format_A ThenC format_B ThenC format_C)
      encode
    -> CorrectAlignedEncoder
         ((format_A ThenC format_B) ThenC format_C)
         encode.
Proof.
  intros; eapply refine_CorrectAlignedEncoder; eauto.
  unfold compose; intros.
  unfold Bind2.
  repeat setoid_rewrite Monad.refineEquiv_bind_bind.
  setoid_rewrite Monad.refineEquiv_bind_unit; simpl; f_equiv; intro.
  simpl; f_equiv; intro.
  simpl; f_equiv; intro.
  rewrite ByteString_enqueue_ByteString_assoc; reflexivity.
Qed.

Definition Format_Source_Intersection
           {A B}
           {cache}
           (format : @FormatM A B cache)
           (predicate : A -> Prop)
  : @FormatM A B cache
  := fun a ce bce =>
       predicate a /\
       format a ce bce.

Definition CorrectAlignedEncoderFor {A} {cache}
           (format : @FormatM A ByteString cache)
           (predicate : A -> Prop)
  := {encode : _ & forall a,
          predicate a ->
          CorrectAlignedEncoder (format a) (encode a)}.

Delimit Scope AlignedEncodeM_scope with AlignedEncodeM.
Notation "y >> z" := (AppendAlignedEncodeM y z) : AlignedEncodeM_scope.
