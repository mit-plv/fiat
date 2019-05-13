Require Import
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.DomainNameOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BaseFormats.

Require Import
        Bedrock.Word.

Section AlignedList.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Definition bytebuffer_of_bytebuffer_range {sz: nat} (from: nat) (len: nat) (v: ByteBuffer.t sz) : { n : _ & ByteBuffer.t n } :=
    let l := List.firstn len (List.skipn from (Vector.to_list v)) in
    existT ByteBuffer.t _ (Vector.of_list l).

  Definition ByteBufferAlignedDecodeM {m : nat} (len: nat) : @AlignedDecodeM cache {n : _ & ByteBuffer.t n} m :=
    fun (v: ByteBuffer.t m) idx env =>
      let lastidx := idx + len in
      if Coq.Init.Nat.leb lastidx m then
        Some ((bytebuffer_of_bytebuffer_range idx len v, lastidx, addD env (8 * len)))
      else
        None.

  Variable addD_addD_plus :
    forall (ce : CacheDecode) (n m : nat), addD (addD ce n) m = addD ce (n + m).
  Variable addD_0 :
    forall ce, addD ce 0 = ce.

  Lemma nth_opt_some
    : forall sz (v : ByteBuffer.t sz) idx,
      lt idx sz
      -> exists b, nth_opt v idx = Some b.
  Proof.
    induction v; simpl; intros.
    - inversion H.
    - destruct idx; simpl.
      + unfold nth_opt; simpl; eauto.
      + apply_in_hyp lt_S_n.
        unfold nth_opt; simpl; eauto.
  Qed.

  Lemma nth_opt_None
    : forall sz (v : ByteBuffer.t sz) idx,
      le sz idx
      -> nth_opt v idx = None.
  Proof.
    induction v; simpl; intros.
    - destruct idx; simpl; try reflexivity.
    - inversion H; subst.
      + eapply IHv; eauto.
      + eapply IHv; Omega.omega.
  Qed.

  Lemma AlignedDecodeByteBufferM {C : Type}
        (n : nat)
    : forall (t : { n : _ & ByteBuffer.t n } -> DecodeM (C * _) ByteString)
        (t' : { n : _ & ByteBuffer.t n } -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
          (fun v cd => `(b, bs, cd') <- decode_bytebuffer n v cd;
                      t b bs cd')
          (fun numBytes => b <- ByteBufferAlignedDecodeM n;
                          t' b)%AlignedDecodeM%list.
  Proof.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans with
        (bit_decoder1 := (fun v cd => `(l, bs, cd') <- decode_list decode_word n v cd;
                                      t (existT ByteBuffer.t _ (ByteBuffer.of_list l)) bs cd'))
        (byte_decoder1 := (fun numBytes => l <- ListAlignedDecodeM (fun numBytes : nat => GetCurrentByte) n;
                                           fun v idx cd =>
                                             if (Coq.Init.Nat.leb idx numBytes) then
                                               t' (existT ByteBuffer.t _ (ByteBuffer.of_list l)) _ v idx cd
                                             else None
                          )%AlignedDecodeM%list).
    - eapply AlignedDecodeListM; eauto using AlignedDecodeCharM.
      intros; repeat (eapply conj; intros).
      + simpl; destruct (Coq.Init.Nat.leb n0 (numBytes_hd)) eqn: ? ;
          repeat apply_in_hyp Compare_dec.leb_complete;
          repeat apply_in_hyp Compare_dec.leb_complete_conv;
          try Omega.omega; simpl; eauto.
        pattern numBytes_hd, v; apply caseS; simpl; intros.
        rewrite (proj1 (H _)); reflexivity.
      + eapply H in H0; eauto.
      + rewrite (proj1 (proj2 (proj2 (H _)) _ _ _)) in H0; rewrite H0;
          find_if_inside; reflexivity.
      + destruct (Coq.Init.Nat.leb 0 n0) eqn: ? ;
        repeat apply_in_hyp Compare_dec.leb_complete;
          repeat apply_in_hyp Compare_dec.leb_complete_conv;
          try Omega.omega; simpl; eauto.
        apply (proj2 (proj2 (H _)) _ _ _) in H0; eauto.
      + destruct (Coq.Init.Nat.leb 0 n0) eqn: ? ;
        repeat apply_in_hyp Compare_dec.leb_complete;
          repeat apply_in_hyp Compare_dec.leb_complete_conv;
          try Omega.omega; simpl; eauto.
        eapply H; eauto.
      + eapply H; eauto.
    - clear t' H; revert t; induction n; simpl; intros.
      + reflexivity.
      + unfold decode_bytebuffer.
        destruct (decode_Vector decode_word (S n) b cd) as [ [ [? ?] ? ] | ] eqn: ?; simpl.
        * unfold decode_Vector in Heqo.
          destruct (decode_word b cd) as [ [ [? ?] ?]  | ]; simpl in *; eauto; try discriminate.
          fold (decode_Vector (decode_word (sz := 8)) n b1 c0) in Heqo.
          rewrite DecodeBindOpt2_assoc; simpl.
          erewrite IHn with (t := fun l => t (existT ByteBuffer.t _ (ByteBuffer.cons w (projT2 l)))).
          unfold decode_bytebuffer.
          destruct (decode_Vector decode_word n b1 c0) as [ [ [? ?] ?]  | ]; simpl in *; eauto; try discriminate.
          injections.
          reflexivity.
        * unfold decode_Vector in Heqo.
          destruct (decode_word b cd) as [ [ [? ?] ?]  | ]; simpl in *; eauto; try discriminate.
          fold (decode_Vector (decode_word (sz := 8)) n b0 c) in Heqo.
          rewrite DecodeBindOpt2_assoc; simpl.
          erewrite IHn with (t := fun l => t (existT ByteBuffer.t _ (ByteBuffer.cons w (projT2 l)))).
          unfold decode_bytebuffer.
          destruct (decode_Vector decode_word n b0 c) as [ [ [? ?] ?]  | ]; simpl in *; eauto; try discriminate.
    - intros n0 v idx; generalize t'; revert addD_addD_plus addD_0 n0 idx v. clear; induction n; simpl; intros.
      + eapply AlignedDecodeMEquiv_trans. eapply ReturnAlignedDecodeM_LeftUnit.
        unfold AlignedDecodeMEquiv, ByteBufferAlignedDecodeM, BindAlignedDecodeM; simpl; intros.
        rewrite <- plus_n_O; find_if_inside; simpl; eauto.
        unfold bytebuffer_of_bytebuffer_range; simpl.
        simpl; rewrite addD_0; reflexivity.
      + eapply AlignedDecodeMEquiv_trans.
        eapply BindAlignedDecodeM_assoc.
        eapply AlignedDecodeMEquiv_trans.
        { instantiate (1 := (a <- GetCurrentByte;
                             l <- ListAlignedDecodeM (fun numBytes : nat => GetCurrentByte) n;
                             (fun (v0 : ByteBuffer.t n0) (idx0 : nat) (cd : CacheDecode) =>
                                if Coq.Init.Nat.leb idx0 n0
                                then t' (existT ByteBuffer.t (| (a :: l) |) (ByteBuffer.of_list (a :: l))) n0 v0 idx0 cd
                                else None))%AlignedDecodeM).
          intros ? ? ?; f_equal; apply functional_extensionality; intros.
          unfold AlignedDecodeMEquiv, ByteBufferAlignedDecodeM, BindAlignedDecodeM in *; simpl in *; intros.
          repeat (apply functional_extensionality; intros).
          destruct (ListAlignedDecodeM (fun numBytes : nat => GetCurrentByte) n x0 x1 x2); simpl; eauto.
        }
        unfold AlignedDecodeMEquiv, ByteBufferAlignedDecodeM, BindAlignedDecodeM in *; simpl in *; intros.
        unfold GetCurrentByte at 1.
        destruct (Coq.Init.Nat.leb (idx0 + S n) n0) as [ | ] eqn: ?; simpl;
          repeat apply_in_hyp Compare_dec.leb_complete;
          repeat apply_in_hyp Compare_dec.leb_complete_conv;
          try Omega.omega; simpl; eauto.
        * destruct (nth_opt_some _ v0 idx0); try Omega.omega;
            rewrite H; simpl.
          pose proof (fun t' => IHn addD_addD_plus addD_0 _ (S idx0) v0 t' (addD c0 8)).
          rewrite (Compare_dec.leb_correct (S idx0 + n) n0) in H0 by Omega.omega;
            simpl in H0.
          pose proof (H0 (fun n => t' (existT ByteBuffer.t (S (projT1 n)) (Vector.cons _ x _ (projT2 n))))).
          cbv beta in H1.
          simpl projT1 at 1 in H1; simpl projT2 at 1 in H1.
          simpl projT1 at 1 in H1.
          unfold ByteBuffer.of_list in *; simpl.
          revert Heqb H.
          rewrite H1, addD_addD_plus; clear; intros.
          unfold bytebuffer_of_bytebuffer_range.
          unfold projT1; unfold projT2.
          f_equal; eauto.
          2: f_equal; Omega.omega.
          replace ((skipn idx0 (to_list v0))) with (x :: (skipn (S idx0) (to_list v0)));
            auto.
          generalize n0 v0 H; clear.
          induction idx0; destruct v0; intros.
          -- compute in H; discriminate.
          -- compute in H; injections; reflexivity.
          -- compute in H; discriminate.
          -- unfold nth_opt in H; simpl in H;
               apply_in_hyp IHidx0.
             unfold to_list at 1; fold (@to_list _ n v0).
             replace (skipn (S (S idx0)) (h :: to_list v0)) with
                 (skipn (S idx0) (to_list v0)) by reflexivity.
             rewrite H; reflexivity.
        * destruct (nth_opt v0 idx0); simpl; eauto.
          assert (Coq.Init.Nat.leb (S idx0 + n) n0 = false)
            by (apply Compare_dec.leb_correct_conv; Omega.omega).
          pose proof (fun t' => IHn addD_addD_plus addD_0 _ (S idx0) v0 t' (addD c0 8)).
          rewrite H in H0; simpl in H0.
          pose proof (H0 (fun n => t' (existT ByteBuffer.t (S (projT1 n)) (Vector.cons _ c1 _ (projT2 n))))).
          erewrite <- H1 at -1.
          f_equal; apply functional_extensionality; intro.
  Qed.

  Fixpoint buffer_blit_buffer' {sz1 sz2} start (src: ByteBuffer.t sz1) (dst: ByteBuffer.t sz2) :=
    match src with
    | Vector.nil => dst
    | Vector.cons h _ t => buffer_blit_buffer' (S start) t (set_nth' dst start h)
    end.

  Definition buffer_blit_buffer {sz1 sz2} start (src: ByteBuffer.t sz1) (dst: ByteBuffer.t sz2) :=
    let idx' := start + sz1 in
    if Coq.Init.Nat.leb idx' sz2 then
      Some (buffer_blit_buffer' start src dst, idx')
    else None.

  Definition AlignedEncodeByteBuffer
    : forall sz, AlignedEncodeM (S := { n : _ & ByteBuffer.t n }) sz :=
    fun sz2 (dst: ByteBuffer.t sz2) idx src env =>
      let '(existT len src) := src in
      match buffer_blit_buffer idx src dst with
      | Some (v', idx') => Some (v', idx', addE env (8 * len))
      | None => None
      end.

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).
  Variable addE_0 :
    forall ce, addE ce 0 = ce.

  Lemma CorrectAlignedEncoderForFormatByteBuffer
    (encode_word_OK : forall (a : word (1 * 8)) (l : list (word (1 * 8))) (env : CacheFormat)
              (tenv' tenv'' : ByteString * CacheFormat),
            format_word a env ∋ tenv' ->
            format_list format_word l (snd tenv') ∋ tenv'' ->
            exists tenv3 tenv4 : ByteString * CacheFormat,
              projT1 (CorrectAlignedEncoderForFormatNChar addE_addE_plus addE_0) a env = Some tenv3 /\
              format_list format_word l (snd tenv3) ∋ tenv4)
    : CorrectAlignedEncoder format_bytebuffer AlignedEncodeByteBuffer.
  Proof.
    eapply refine_CorrectAlignedEncoder
      with (format' := fun s env => format_list format_word (ByteBuffer.to_list (projT2 s)) env);
      [ | eapply CorrectAlignedEncoder_morphism with
              (encode := fun sz v idx w c => AlignedEncodeList (@SetCurrentByte _ _) sz v idx (ByteBuffer.to_list (projT2 w)) c)].
    - intros [? ?]; clear; split.
      + revert env; induction t; simpl; intros.
        * reflexivity.
        * unfold format_bytebuffer in *; simpl in *; apply refine_under_bind; intros.
          unfold Bind2; rewrite IHt; reflexivity.
      + unfold format_bytebuffer, Bind2 in *.
        intros; intro; eapply (H v).
        clear H; revert env v H0; induction t; simpl; intros.
        * eapply H0.
        * unfold Bind2 in *.
          computes_to_inv.
          computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
          rewrite H0''; eauto.
    - apply EquivFormat_reflexive.
    - intros ? ? ? [n t]; revert sz v idx; induction t.
      + simpl; intros.
        unfold buffer_blit_buffer.
        destruct (Coq.Init.Nat.leb (idx + 0) sz) eqn: ?; intros.
        * eapply PeanoNat.Nat.leb_le in Heqb.
          rewrite (proj2 (PeanoNat.Nat.ltb_lt idx (S sz))) by Omega.omega.
          unfold ReturnAlignedEncodeM.
          simpl. rewrite <- (addE_0 c) at 2.
          simpl; repeat f_equal; try Omega.omega.
        * eapply PeanoNat.Nat.leb_gt in Heqb.
          rewrite (proj2 (PeanoNat.Nat.ltb_ge idx (S sz))) by Omega.omega.
          reflexivity.
      + simpl; intros.
        unfold buffer_blit_buffer.
        destruct (Coq.Init.Nat.leb (idx + (S n)) sz) eqn: ?; intros.
        * eapply PeanoNat.Nat.leb_le in Heqb.
          unfold SetCurrentByte at 1.
          rewrite (proj2 (PeanoNat.Nat.ltb_lt idx sz)) by Omega.omega; simpl.
          rewrite <- IHt.
          simpl.
          unfold buffer_blit_buffer.
          destruct (Coq.Init.Nat.leb (S idx + n) sz) eqn: ?; intros.
          eapply PeanoNat.Nat.leb_le in Heqb0; simpl;
            rewrite addE_addE_plus; repeat (f_equal; try Omega.omega).
          eapply PeanoNat.Nat.leb_gt in Heqb0; Omega.omega.
        * eapply PeanoNat.Nat.leb_gt in Heqb.
          unfold SetCurrentByte at 1.
          destruct (PeanoNat.Nat.ltb idx sz) eqn: ? ; simpl; auto.
          rewrite <- IHt.
          unfold AlignedEncodeByteBuffer, buffer_blit_buffer.
          destruct (Coq.Init.Nat.leb (S idx + n) sz) eqn: ? ; simpl; auto.
          eapply PeanoNat.Nat.leb_le in Heqb0;
            eapply PeanoNat.Nat.leb_le in Heqb1; Omega.omega.
    - eexists (fun s env => _); repeat apply conj; intros;
        try eapply ((projT2 (CorrectAlignedEncoderForFormatList
                               _ _
                               (CorrectAlignedEncoderForFormatNChar (sz := 1) addE_addE_plus addE_0) encode_word_OK))); eauto.
      pose proof (proj2 (proj2 ((projT2 (CorrectAlignedEncoderForFormatList
                                           _ _
                                           (CorrectAlignedEncoderForFormatNChar (sz := 1) addE_addE_plus addE_0) encode_word_OK))))).
      unfold EncodeMEquivAlignedEncodeM in *; intros ? [? ?] ?; simpl in *.
      intuition.
      eapply H; eauto.
      eapply (proj1 (proj2 (H _ _ _))); eauto.
      eapply (proj1 (proj2 (proj2 (H _ _ _)))); eauto.
      eapply (proj2 (proj2 (proj2 (H _ _ _)))); eauto.
  Qed.

End AlignedList.
