Require Export
        Coq.Lists.List.
Require Import
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig.

Set Implicit Arguments.

Section FixListEncoder.
  Variable size : nat.
  Variable A : Type.
  Variable cache : Cache.
  Variable transformer : Transformer.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> bin * CacheEncode.
  Variable A_decoder : decoder cache transformer A_predicate A_encode.

  Definition FixList := { xs : list A | length xs < exp2_nat size }.

  Definition FixList_getlength
             (ls : FixList) : {n : N | (n < exp2 size)%N}.
    refine (exist _ (N_of_nat (length (proj1_sig ls))) _).
    destruct ls as [ xs xs_pf ]. unfold exp2_nat in xs_pf. simpl.
    rewrite <- Nnat.N2Nat.id. rewrite <- N.compare_lt_iff.
    rewrite <- Nnat.Nat2N.inj_compare.
    rewrite <- Compare_dec.nat_compare_lt.
    eauto.
  Defined.

  Definition FixList_predicate (len : {n : N | (n < exp2 size)%N}) (l : FixList) :=
    FixList_getlength l = len /\
    forall x, In x (proj1_sig l) -> A_predicate x.

  Fixpoint FixList_encode' (xs : list A) (ce : CacheEncode) : bin * CacheEncode :=
    match xs with
    | nil => (transform_id, ce)
    | x :: xs' => let (b1, env1) := A_encode x ce in
                  let (b2, env2) := FixList_encode' xs' env1 in
                      (transform b1 b2, env2)
    end.

  Definition FixList_encode (l : FixList) := FixList_encode' (proj1_sig l).

  Fixpoint FixList_decode' (s : nat) (b : bin) (cd : CacheDecode) : list A * bin * CacheDecode :=
    match s with
    | O => (nil, b, cd)
    | S s' => let (x1, e1) := decode b cd in
              let (x, b1) := x1 in
              let (x2, e2) := FixList_decode' s' b1 e1 in
              let (xs, b2) := x2 in
              (x :: xs, b2, e2)
    end.

  Lemma decode'_length :
    forall len bin env, length (fst (fst (FixList_decode' len bin env))) = len.
  Proof.
    induction len; intuition eauto.
    simpl. destruct (decode bin env) as [[? ?] ?].
    specialize (IHlen b c). destruct (FixList_decode' len b c) as [[? ?] ?]. simpl. f_equal. eauto.
  Qed.

  Lemma exp2_nat_nonzero :
    forall size, exp2_nat size <> O.
  Proof.
    assert (forall size, exp2_nat size > O) as lt_pf.
    intro s. unfold exp2_nat. unfold exp2. rewrite Znat.positive_N_nat.
    destruct (Pnat.Pos2Nat.is_succ (exp2' s)). rewrite H. omega.
    intro s. specialize (lt_pf s). omega.
  Qed.

  Definition FixList_decode (len : nat) (b : bin) (env' : CacheDecode) : FixList * bin * CacheDecode.
    refine (let x := FixList_decode' len b env' in
            (exist _ (fst (fst (FixList_decode' (min (pred (exp2_nat size)) len) b env'))) _,
             snd (fst x),
             snd x)).
    abstract (
    rewrite decode'_length;
    rewrite NPeano.Nat.min_lt_iff;
    left; unfold lt;
    rewrite NPeano.Nat.succ_pred; [ | eapply exp2_nat_nonzero ]; eauto).
  Defined.

  Theorem FixList_encode_correct :
    forall len,
      encode_decode_correct cache transformer (FixList_predicate len) FixList_encode (FixList_decode (nat_of_N (proj1_sig len))).
  Proof.
    unfold encode_decode_correct, FixList_predicate, FixList_encode, FixList_decode.
    intros [len len_pf] env env' xenv xenv' [l l_pf] [l' l'_pf] bin ext ext' Eeq Ppred Penc Pdec. simpl in *.
    inversion Penc; clear Penc; inversion Pdec; clear Pdec.
    rewrite <- (sig_equivalence _ (fun xs => length xs < exp2_nat size) l l' l_pf l'_pf).
    assert (min (pred (exp2_nat size)) (N.to_nat len) = N.to_nat len) as pmin.
    rewrite Min.min_r; eauto. eapply NPeano.Nat.lt_le_pred. unfold exp2_nat.
    eapply Compare_dec.nat_compare_lt. rewrite <- Nnat.N2Nat.inj_compare. eauto.
    unfold FixList_getlength in *. rewrite <- sig_equivalence in Ppred. simpl in *.
    destruct Ppred. subst. rewrite Nnat.Nat2N.id in *.
    rewrite pmin in *. clear pmin len_pf l_pf.
    generalize dependent size; generalize dependent env; generalize dependent env';
      generalize dependent xenv; generalize dependent bin.
    induction l; simpl in *.

    intros; inversion H0; subst; intuition eauto; rewrite transform_id_left; eauto.

    intros.
    specialize (IHl (fun x pf => H4 x (or_intror pf))).
    specialize (H4 a (or_introl eq_refl)).
    destruct (A_encode a env) eqn: ?.
    destruct (decode (transform bin ext) env') as [[? ?] ?] eqn: ?.
    destruct (FixList_encode' l c) eqn: ?. inversion H0; subst; clear H0.
    rewrite <- transform_assoc in Heqp0.
    pose proof (decode_correct (decoder:=A_decoder) env env' _ _ Eeq H4 Heqp Heqp0); clear Eeq H4 Heqp Heqp0.
    destruct H as [? [? ?]]. subst.
    destruct (FixList_decode' (length l) (transform b1 ext) c0) as [[? ?] ?] eqn: ?.
    specialize (IHl b1 xenv c0 c H Heqp1 size0).
    rewrite Heqp in IHl. simpl in *.
    assert (length l0 < exp2_nat size0) by omega.
    intuition. subst. intuition.
  Qed.
End FixListEncoder.

Global Instance FixList_decoder size A len cache
       (transformer : Transformer)
       (A_predicate : A -> Prop)
       (A_encode : A -> CacheEncode -> bin * CacheEncode)
       (A_decoder : decoder cache transformer A_predicate A_encode)
  : decoder cache transformer
            (FixList_predicate A_predicate len)
            (FixList_encode cache transformer A_encode) :=
  { decode := @FixList_decode size _  _ _ _ _ _ (nat_of_N (proj1_sig len));
    decode_correct := @FixList_encode_correct _ _ _ _ _ _ _ _ }.

Arguments FixList_encode {_ _ _} _ _ _ _.