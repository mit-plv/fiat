Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedString
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Compose
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.DomainNameOpt
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Narcissus.Formats.IPChecksum
        Fiat.Narcissus.Common.ComposeCheckSum.

Require Import
        Bedrock.Word.

Section AlignedDecoders.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Lemma AlignedFormatThenC
    : forall ce (c1 : _ -> Comp _) (c2 : _ -> Comp _)
             (v1 : _ -> {n : nat & t (word 8) n})
             (v2 : _ -> {n : nat & t (word 8) n})
             (ce2 : _ -> CacheFormat)
             (ce1 : _ -> CacheFormat),
      refine (c1 ce) (ret (build_aligned_ByteString (projT2 (v1 ce)), (ce1 ce)))
      -> (forall v ce',
             computes_to (c1 ce) (v, ce')
             -> refine (c2 ce') (ret (build_aligned_ByteString (projT2 (v2 ce')), (ce2 ce'))))
      -> refine ((c1 ThenC c2) ce)
                (ret (build_aligned_ByteString
                        (Vector.append (projT2 (v1 ce)) (projT2 (v2 (ce1 ce)))),
                      (ce2 (ce1 ce)))).
  Proof.
    unfold compose; intros.
    unfold Bind2.
    etransitivity.
    apply refine_under_bind_both; eauto.
    intros [? ?] ?.
    rewrite H0; try eassumption.
    simplify with monad laws.
    simpl.
    instantiate (1 := fun bc => ret (ByteString_enqueue_ByteString (fst bc) (build_aligned_ByteString (projT2 (v2 (snd bc)))), ce2 (snd bc))); simpl.
    reflexivity.
    simplify with monad laws.
    simpl.
    rewrite <- build_aligned_ByteString_append.
    reflexivity.
  Qed.

  Lemma AlignedFormatDoneC
    : forall ce (c1 : _ -> Comp _)
             (v1 : _ -> {n : nat & t (word 8) n})
             (ce1 : _ -> CacheFormat),
      refine (c1 ce) (ret (build_aligned_ByteString (projT2 (v1 ce)), (ce1 ce)))
      -> refine ((c1 DoneC) ce)
                (ret (build_aligned_ByteString (projT2 (v1 ce)), (ce1 ce))).
  Proof.
    unfold compose; intros.
    unfold Bind2.
    rewrite H.
    simplify with monad laws.
    simpl.
    f_equiv.
  Qed.

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).

  Lemma AlignedFormat2Char' {numBytes}
    : forall (w : word 16) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 16)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_word (monoidUnit := ByteString_QueueMonoidOpt) w)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons
                                                  _ (split1' 8 8 w) _
                                                  (Vector.cons _ (split2' 8 8 w) _ v)), ce')).
  Proof.
    unfold compose, Bind2; intros.
    intros; setoid_rewrite (@format_words' _ _ 8 8 addE_addE_plus w).
    rewrite (@AlignedFormatChar _ _ 1) by apply aligned_format_char_eq.
    simplify with monad laws.
    unfold snd.
    rewrite addE_addE_plus.
    rewrite H.
    simplify with monad laws.
    unfold fst.
    rewrite <- build_aligned_ByteString_append.
    unfold append.
    reflexivity.
  Qed.

  Lemma AlignedFormat2Char {numBytes}
    : forall (w : word 16) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 16)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_word (monoidUnit := ByteString_QueueMonoidOpt) w)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons
                                                  _ (split2 8 8 w) _
                                                  (Vector.cons _ (split1 8 8 w) _ v)), ce')).
  Proof.
    unfold compose, Bind2; intros.
    intros; setoid_rewrite (@format_words _ _ 8 8 addE_addE_plus w).
    rewrite (@AlignedFormatChar _ _ 1) by apply aligned_format_char_eq.
    simplify with monad laws.
    unfold snd.
    rewrite addE_addE_plus.
    rewrite H.
    simplify with monad laws.
    unfold fst.
    rewrite <- build_aligned_ByteString_append.
    unfold append.
    f_equiv.
  Qed.

  Local Arguments split1 : simpl never.
  Local Arguments split2 : simpl never.

  Lemma CorrectAlignedEncoderForFormat2Char
    : forall (w : word 16),
      CorrectAlignedEncoder
        (format_word (monoidUnit := ByteString_QueueMonoidOpt) w)
        (fun sz => AppendAlignedEncodeM (@SetCurrentByte _ _ sz (split2 8 8 w))
                                        (SetCurrentByte (split1 8 8 w))).
  Proof.
    intro; pose proof (@format_words _ _ 8 8 addE_addE_plus w) as H';
      eapply refine_CorrectAlignedEncoder.
    unfold flip, pointwise_relation; intros.
    instantiate (1 := (format_word (split2 8 8 (eq_rect (8 + 8) word w (8 + 8) (trans_plus_comm 8 8)))
                                   ThenC (format_word (split1 8 8 (eq_rect (8 + 8) word w (8 + 8) (trans_plus_comm 8 8)))))).
    rewrite (H' ce).
    unfold compose, Bind2; simpl.
    repeat setoid_rewrite Monad.refineEquiv_bind_bind;
      repeat setoid_rewrite <- Monad.refine_bind_unit'.
    f_equiv; intro.
    eapply (CorrectAlignedEncoderForThenC
              _ _ _
              (fun sz => SetCurrentByte (n := sz) _)).
    simpl in *|-*.
    eapply (CorrectAlignedEncoderForFormatChar_f).
    eapply (CorrectAlignedEncoderForFormatChar_f).
  Qed.

  Corollary AlignedDecode2Nat {C}
            {numBytes}
    : forall (v : Vector.t (word 8) (S (S numBytes)))
             (t : _ -> C)
             e
             cd,
      Ifopt (decode_nat (monoidUnit := ByteString_QueueMonoidOpt) 16 (build_aligned_ByteString v) cd) as w
                                                                                                           Then t w Else e
                                                                                                         =
                                                                                                         Let n := wordToNat (Core.append_word (Vector.nth v (Fin.FS Fin.F1)) (Vector.nth v Fin.F1)) in
        t (n, build_aligned_ByteString (snd (Vector_split 2 _ v)), addD cd 16).
  Proof.
    unfold CacheDecode.
    unfold decode_nat, DecodeBindOpt2; intros.
    unfold BindOpt at 1.
    rewrite AlignedDecode2Char.
    reflexivity.
  Qed.

  Local Open Scope AlignedDecodeM_scope.

  Lemma AlignedDecodeNatM {C : Set}
        (t : nat -> DecodeM C ByteString)
        (t' : nat -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_nat (monoidUnit := ByteString_QueueMonoidOpt) 8 v cd;
                          t a b0 cd')
           (fun numBytes => b <- GetCurrentByte;
                              n <- return (wordToNat b);
                                            t' n).
  Proof.
    replace
      (fun (v : ByteString) (cd : CacheDecode) => `(a, b0, cd') <-
                                                   decode_nat 8 v cd;
                                                  t a b0 cd') with
        (fun (v : ByteString) (cd : CacheDecode) =>
           `(w, b, cd') <- decode_word (sz := 8) v cd;
           t (wordToNat w) b cd'); intros.
    eapply AlignedDecodeBindCharM; intros.
    replace (fun numBytes : nat => n <- return (wordToNat b);
                                               t' n numBytes) with
        (fun numBytes : nat => t'  (wordToNat b) numBytes).
    eapply H.
    unfold BindAlignedDecodeM, ReturnAlignedDecodeM; simpl.
    repeat (apply functional_extensionality_dep; intros); reflexivity.
    repeat (apply functional_extensionality_dep; intros).
    unfold decode_nat, DecodeBindOpt2; intros.
    rewrite BindOpt_assoc; f_equal.
    repeat (apply functional_extensionality_dep; intros).
    unfold BindOpt.
    destruct x1; destruct p; simpl.
    reflexivity.
  Qed.


  Corollary AlignedFormat2Nat'
            {numBytes}
    : forall (n : nat) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 16)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_nat 16 (monoidUnit := ByteString_QueueMonoidOpt) n)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons
                                                  _ (split1' 8 8 (natToWord 16 n)) _
                                                  (Vector.cons _ (split2' 8 8 (natToWord 16 n)) _ v)), ce')).
  Proof.
    unfold format_nat; cbv beta; intros.
    rewrite <- AlignedFormat2Char'; eauto.
    reflexivity.
  Qed.

  Corollary AlignedFormat2Nat
            {numBytes}
    : forall (n : nat) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 16)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_nat 16 (monoidUnit := ByteString_QueueMonoidOpt) n)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons
                                                  _ (split2 8 8 (natToWord 16 n)) _
                                                  (Vector.cons _ (split1 8 8 (natToWord 16 n)) _ v)), ce')).
  Proof.
    unfold format_nat; cbv beta; intros.
    rewrite <- AlignedFormat2Char; eauto.
    reflexivity.
  Qed.

  Lemma CorrectAlignedEncoderForFormatNat
    : forall (n : nat),
      CorrectAlignedEncoder
        (format_nat 8 (monoidUnit := ByteString_QueueMonoidOpt) n)
        (fun sz => @SetCurrentByte _ _ sz (natToWord 8 n)).
  Proof.
    eapply CorrectAlignedEncoderForFormatChar_f.
  Qed.

  Lemma optimize_under_if_opt {A ResultT}
    : forall (a_opt : option A) (t t' : A -> ResultT) (e e' : ResultT),
      (forall a, t a = t' a) -> e = e' ->
      Ifopt a_opt as a Then t a Else e = Ifopt a_opt as a Then t' a Else e'.
  Proof.
    intros; subst; eauto.
    destruct a_opt; eauto.
  Qed.

  Lemma rewrite_under_LetIn
        {A B}
    : forall (a : A) (k k' : A -> B),
      (forall a, k a = k' a) -> LetIn a k = LetIn a k'.
  Proof.
    intros; unfold LetIn; eauto.
  Qed.

  Fixpoint Guarded_Vector_split
           (sz n : nat)
           {struct sz}
    : Vector.t (word 8) n
      -> Vector.t (word 8) (sz + (n - sz)) :=
    match sz, n return
          Vector.t _ n
          -> Vector.t (word 8) (sz + (n - sz))
    with
    | 0, _ => fun v => (eq_rect _ (Vector.t _) v _ (minus_n_O n))
    | S n', 0 =>
      fun v =>
        Vector.cons _ (wzero _) _ (Guarded_Vector_split n' _ v)
    | S n', S sz' =>
      fun v =>
        Vector.cons _ (Vector.hd v) _ (Guarded_Vector_split n' _ (Vector.tl v))
    end .

  Lemma le_B_Guarded_Vector_split
        {n}
        (b : Vector.t _ n)
        (m : nat)
    : {b' : ByteString | le_B b' (build_aligned_ByteString b)}.
    eexists (build_aligned_ByteString
               (snd (Vector_split _ _ (Guarded_Vector_split m n b)))).
    abstract (unfold build_aligned_ByteString, le_B; simpl;
              unfold length_ByteString; simpl; omega).
  Defined.

  Lemma build_aligned_ByteString_eq_split
    : forall m n b H0,
      (m <= n)%nat
      -> build_aligned_ByteString b =
         (build_aligned_ByteString (eq_rect (m + (n - m)) (t (word 8)) (Guarded_Vector_split m n b) n H0)).
  Proof.
    intros.
    intros; eapply ByteString_f_equal; simpl.
    instantiate (1 := eq_refl _); reflexivity.
    instantiate (1 := eq_refl _).
    simpl.
    revert n b H0 H; induction m; simpl.
    intros ? ?; generalize (minus_n_O n).
    intros; rewrite <- Equality.transport_pp.
    apply Eqdep_dec.eq_rect_eq_dec; auto with arith.
    intros.
    inversion H; subst.
    - revert b H0 IHm; clear.
      intro; pattern m, b; apply Vector.caseS; simpl; intros.
      assert ((n + (n - n)) = n) by omega.
      rewrite eq_rect_Vector_cons with (H' := H).
      f_equal.
      erewrite <- IHm; eauto.
    - revert b H0 IHm H1; clear.
      intro; pattern m0, b; apply Vector.caseS; simpl; intros.
      assert ((m + (n - m)) = n) by omega.
      erewrite eq_rect_Vector_cons with (H' := H).
      f_equal.
      erewrite <- IHm; eauto.
      omega.
  Qed.

  Lemma ByteAlign_Decode_w_Measure_le {A}
    : forall (dec_a : ByteString -> CacheDecode -> option (A * ByteString * CacheDecode))
             (n m : nat)
             (dec_a' : Vector.t (word 8) (m + (n - m)) -> A)
             (cd : CacheDecode)
             (f : CacheDecode -> CacheDecode)
             (b : Vector.t (word 8) n)
             decode_a_le
             (dec_fail : ~ (m <= n)%nat
                         -> forall b cd, dec_a (build_aligned_ByteString (numBytes := n) b) cd = None),
      (forall b cd, dec_a (build_aligned_ByteString b) cd =
                    Some (dec_a' b, build_aligned_ByteString (snd (Vector_split m (n - m) b)), f cd))
      -> Decode_w_Measure_le dec_a (build_aligned_ByteString b) cd decode_a_le =
         match Compare_dec.le_dec m n with
         | left e => (Let a := dec_a' (Guarded_Vector_split m n b) in
                          Some (a, le_B_Guarded_Vector_split b m, f cd))
         | right _ => None
         end.
  Proof.
    intros.
    destruct (Compare_dec.le_dec m n).
    assert (m + (n - m) = n) by omega.
    assert (forall b, Decode_w_Measure_le dec_a (build_aligned_ByteString b) cd decode_a_le
                      = Decode_w_Measure_le dec_a (build_aligned_ByteString ( eq_rect _ _ (Guarded_Vector_split m n b) _ H0)) cd decode_a_le).
    { revert l; clear; intros.
      destruct (Decode_w_Measure_le dec_a (build_aligned_ByteString b) cd decode_a_le)
        as [ [ [? [? ?] ] ?] | ] eqn: ?.
      apply Decode_w_Measure_le_eq' in Heqo.
      simpl in Heqo.
      destruct (Decode_w_Measure_le dec_a
                                    (build_aligned_ByteString (eq_rect (m + (n - m)) (t (word 8)) (Guarded_Vector_split m n b) n H0)) cd decode_a_le) as [ [ [? [? ?] ] ?] | ] eqn: ?.
      apply Decode_w_Measure_le_eq' in Heqo0.
      simpl in *.
      rewrite <- build_aligned_ByteString_eq_split in Heqo0 by eauto.
      rewrite Heqo0 in Heqo.
      injection Heqo; intros.
      rewrite H, H2;
        repeat f_equal.
      revert l0 l1. rewrite H1; intros; f_equal.
      f_equal; apply Core.le_uniqueness_proof.
      apply ByteString_id.
      eapply Decode_w_Measure_le_eq'' in Heqo0.
      rewrite <- build_aligned_ByteString_eq_split in Heqo0 by eauto.
      rewrite Heqo0 in Heqo.
      discriminate.
      apply ByteString_id.
      erewrite build_aligned_ByteString_eq_split in Heqo by eauto.
      rewrite Heqo; reflexivity.
    }
    rewrite H1.
    match goal with
      |- ?a = _ => destruct a as [ [ [? ?] ? ] | ] eqn: ?
    end.
    eapply Decode_w_Measure_le_eq' in Heqo.
    assert (dec_a (build_aligned_ByteString (Guarded_Vector_split m n b)) cd
            = Some (a, proj1_sig s, c)).
    { destruct s; simpl in *.
      rewrite <- Heqo.
      unfold build_aligned_ByteString; repeat f_equal; simpl.
      eapply ByteString_f_equal; simpl.
      instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := sym_eq H0).
      clear H1.
      destruct H0; reflexivity.
    }
    rewrite H in H2; injection H2; intros.
    rewrite H3, H5; unfold LetIn; simpl.
    repeat f_equal.
    destruct s; simpl in *.
    unfold le_B_Guarded_Vector_split; simpl.
    clear H1; revert l0.
    rewrite <- H4; intros.
    f_equal; apply Core.le_uniqueness_proof.
    apply ByteString_id.
    apply Decode_w_Measure_le_eq'' in Heqo.
    pose proof (H (Guarded_Vector_split m n b) cd).
    assert (Some (dec_a' (Guarded_Vector_split m n b),
                  build_aligned_ByteString (snd (Vector_split m (n - m) (Guarded_Vector_split m n b))),
                  f cd) = None).
    { rewrite <- Heqo.
      rewrite <- H.
      repeat f_equal.
      eapply ByteString_f_equal; simpl.
      instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := sym_eq H0).
      clear H1.
      destruct H0; reflexivity.
    }
    discriminate.
    eapply dec_fail in n0; simpl.
    eapply Specs.Decode_w_Measure_le_eq' in n0.
    apply n0.
  Qed.

  Lemma lt_B_Guarded_Vector_split
        {n}
        (b : Vector.t _ n)
        (m : nat)
        (m_OK : lt 0 m)
        (_ : ~ lt n m)
    : {b' : ByteString | lt_B b' (build_aligned_ByteString b)}.
    eexists (build_aligned_ByteString
               (snd (Vector_split _ _ (Guarded_Vector_split m n b)))).
    abstract (unfold build_aligned_ByteString, lt_B; simpl;
              unfold length_ByteString; simpl; omega).
  Defined.

  Fixpoint BytesToString {sz}
           (b : Vector.t (word 8) sz)
    : string :=
    match b with
    | Vector.nil => EmptyString
    | Vector.cons a _ b' => String (Ascii.ascii_of_N (wordToN a)) (BytesToString b')
    end.

  Fixpoint StringToBytes
           (s : string)
    : Vector.t (word 8) (String.length s) :=
    match s return Vector.t (word 8) (String.length s) with
    | EmptyString => Vector.nil _
    | String a s' => Vector.cons _ (NToWord 8 (Ascii.N_of_ascii a)) _ (StringToBytes s')
    end.

  Lemma ByteAlign_Decode_w_Measure_lt {A}
    : forall (dec_a : nat -> ByteString -> CacheDecode -> option (A * ByteString * CacheDecode))
             (n m : nat)
             (dec_a' : forall m n, Vector.t (word 8) (m + n) -> A)
             (cd : CacheDecode)
             (f : nat -> CacheDecode -> CacheDecode)
             (b : Vector.t (word 8) n)
             (m_OK : lt 0 m)
             decode_a_le
             (dec_fail : (lt n m)%nat
                         -> forall b cd, dec_a m (build_aligned_ByteString (numBytes := n) b) cd = None),
      (forall n m b cd, dec_a m (build_aligned_ByteString b) cd =
                        Some (dec_a' _ _ b, build_aligned_ByteString (snd (Vector_split m n b)), f m cd))
      -> Decode_w_Measure_lt (dec_a m) (build_aligned_ByteString b) cd decode_a_le =
         match Compare_dec.lt_dec n m with
         | left _ => None
         | right n' => (Let a := dec_a' _ _ (Guarded_Vector_split m n b) in
                            Some (a, lt_B_Guarded_Vector_split b m m_OK n' , f m cd))
         end.
  Proof.
    intros.
    destruct (Compare_dec.lt_dec m n);
      destruct (Compare_dec.lt_dec n m); try omega.
    - assert (m + (n - m) = n) by omega.
      assert (forall b, Decode_w_Measure_lt (dec_a m) (build_aligned_ByteString b) cd decode_a_le
                        = Decode_w_Measure_lt (dec_a m)(build_aligned_ByteString ( eq_rect _ _ (Guarded_Vector_split m n b) _ H0)) cd decode_a_le).
      { revert l; clear; intros.
        destruct (Decode_w_Measure_lt (dec_a m) (build_aligned_ByteString b) cd decode_a_le)
          as [ [ [? [? ?] ] ?] | ] eqn: ?.
        apply Decode_w_Measure_lt_eq' in Heqo.
        simpl in Heqo.
        destruct (Decode_w_Measure_lt (dec_a m)
                                      (build_aligned_ByteString (eq_rect _ (t (word 8)) (Guarded_Vector_split m n b) n H0)) cd decode_a_le) as [ [ [? [? ?] ] ?] | ] eqn: ?.
        apply Decode_w_Measure_lt_eq' in Heqo0.
        unfold proj1_sig in Heqo0.
        rewrite <- build_aligned_ByteString_eq_split in Heqo0.
        rewrite Heqo0 in Heqo.
        injection Heqo; intros.
        rewrite H, H2;
          repeat f_equal.
        revert l1 l0. rewrite H1; intros; f_equal.
        f_equal; apply Core.le_uniqueness_proof.
        omega.
        apply ByteString_id.
        eapply Decode_w_Measure_lt_eq'' in Heqo0.
        rewrite <- build_aligned_ByteString_eq_split in Heqo0 by omega.
        rewrite Heqo0 in Heqo.
        discriminate.
        apply ByteString_id.
        erewrite (build_aligned_ByteString_eq_split m n) in Heqo by omega.
        rewrite Heqo; reflexivity.
      }
      rewrite H1.
      match goal with
        |- ?a = _ => destruct a as [ [ [? ?] ? ] | ] eqn: ?
      end.
      eapply Decode_w_Measure_lt_eq' in Heqo.
      assert (dec_a m (build_aligned_ByteString (Guarded_Vector_split m n b)) cd
              = Some (a, proj1_sig s, c)).
      { destruct s; simpl in *.
        rewrite <- Heqo.
        unfold build_aligned_ByteString; repeat f_equal; simpl.
        eapply ByteString_f_equal; simpl.
        instantiate (1 := eq_refl _); reflexivity.
        instantiate (1 := sym_eq H0).
        clear H1.
        destruct H0; reflexivity.
      }
      rewrite H in H2; injection H2; intros.
      rewrite H3, H5; unfold LetIn; simpl.
      repeat f_equal.
      destruct s; simpl in *.
      unfold lt_B_Guarded_Vector_split; simpl.
      clear H1; revert l0.
      rewrite <- H4; intros.
      f_equal. apply Core.le_uniqueness_proof.
      apply ByteString_id.
      apply Decode_w_Measure_lt_eq'' in Heqo.
      pose proof (H _ _ (Guarded_Vector_split m n b) cd).
      assert (Some (dec_a' _ _ (Guarded_Vector_split m n b),
                    build_aligned_ByteString (snd (Vector_split m (n - m) (Guarded_Vector_split m n b))),
                    f m cd) = None).
      { rewrite <- Heqo.
        rewrite <- H.
        repeat f_equal.
        eapply ByteString_f_equal; simpl.
        instantiate (1 := eq_refl _); reflexivity.
        instantiate (1 := sym_eq H0).
        clear H1.
        destruct H0; reflexivity.
      }
      discriminate.
    - eapply dec_fail in l; simpl.
      eapply Specs.Decode_w_Measure_lt_eq' in l.
      apply l.
    - assert (m = n) by omega; subst.
      assert (n + (n - n) = n) by omega.
      assert (forall b, Decode_w_Measure_lt (dec_a n) (build_aligned_ByteString b) cd decode_a_le
                        = Decode_w_Measure_lt (dec_a n)(build_aligned_ByteString ( eq_rect _ _ (Guarded_Vector_split n n b) _ H0)) cd decode_a_le).
      { clear; intros.
        destruct (Decode_w_Measure_lt (dec_a n) (build_aligned_ByteString b) cd decode_a_le)
          as [ [ [? [? ?] ] ?] | ] eqn: ?.
        apply Decode_w_Measure_lt_eq' in Heqo.
        simpl in Heqo.
        destruct (Decode_w_Measure_lt (dec_a n)
                                      (build_aligned_ByteString (eq_rect _ (t (word 8)) (Guarded_Vector_split n n b) n H0)) cd decode_a_le) as [ [ [? [? ?] ] ?] | ] eqn: ?.
        apply Decode_w_Measure_lt_eq' in Heqo0.
        unfold proj1_sig in Heqo0.
        rewrite <- build_aligned_ByteString_eq_split in Heqo0.
        rewrite Heqo0 in Heqo.
        injection Heqo; intros.
        rewrite H, H2;
          repeat f_equal.
        revert l l0. rewrite H1; intros; f_equal.
        f_equal; apply Core.le_uniqueness_proof.
        omega.
        apply ByteString_id.
        eapply Decode_w_Measure_lt_eq'' in Heqo0.
        rewrite <- build_aligned_ByteString_eq_split in Heqo0 by omega.
        rewrite Heqo0 in Heqo.
        discriminate.
        apply ByteString_id.
        erewrite (build_aligned_ByteString_eq_split n n) in Heqo by omega.
        rewrite Heqo; reflexivity.
      }
      rewrite H1.
      match goal with
        |- ?a = _ => destruct a as [ [ [? ?] ? ] | ] eqn: ?
      end.
      eapply Decode_w_Measure_lt_eq' in Heqo.
      assert (dec_a n (build_aligned_ByteString (Guarded_Vector_split n n b)) cd
              = Some (a, proj1_sig s, c)).
      { destruct s; simpl in *.
        rewrite <- Heqo.
        unfold build_aligned_ByteString; repeat f_equal; simpl.
        eapply ByteString_f_equal; simpl.
        instantiate (1 := eq_refl _); reflexivity.
        instantiate (1 := sym_eq H0).
        clear H1.
        destruct H0; reflexivity.
      }
      rewrite H in H2; injection H2; intros.
      rewrite H3, H5; unfold LetIn; simpl.
      repeat f_equal.
      destruct s; simpl in *.
      unfold lt_B_Guarded_Vector_split; simpl.
      clear H1; revert l.
      rewrite <- H4; intros.
      f_equal. apply Core.le_uniqueness_proof.
      apply ByteString_id.
      apply Decode_w_Measure_lt_eq'' in Heqo.
      pose proof (H _ _ (Guarded_Vector_split n n b) cd).
      assert (Some (dec_a' _ _ (Guarded_Vector_split n n b),
                    build_aligned_ByteString (snd (Vector_split n (n - n) (Guarded_Vector_split n n b))),
                    f n cd) = None).
      { rewrite <- Heqo.
        rewrite <- H.
        repeat f_equal.
        eapply ByteString_f_equal; simpl.
        instantiate (1 := eq_refl _); reflexivity.
        instantiate (1 := sym_eq H0).
        clear H1.
        destruct H0; reflexivity.
      }
      discriminate.
  Qed.

  Lemma optimize_under_match {A B} {P}
    : forall (a a' : A) (f : {P a a'} + {~P a a'}) (t t' : _ -> B)
             (e e' : _ -> B),
      (forall (a a' : A) (a_eq : _), t a_eq = t' a_eq)
      -> (forall (a a' : A) (a_neq : _), e a_neq = e' a_neq)
      -> match f with
         | left e => t e
         | right n => e n
         end =
         match f with
         | left e => t' e
         | right n => e' n
         end.
  Proof.
    destruct f; simpl; intros; eauto.
  Qed.

  Lemma optimize_Fix {A}
    : forall
      (body : forall x : ByteString,
          (forall y : ByteString,
              lt_B y x -> (fun _ : ByteString => CacheDecode -> option (A * ByteString * CacheDecode)) y) ->
          (fun _ : ByteString => CacheDecode -> option (A * ByteString * CacheDecode)) x)
      (body' : forall x : nat,
          (forall y : nat,
              (lt y x)%nat ->
              (fun m : nat =>
                 t (word 8) m -> CacheDecode ->
                 option (A * {n : _ & Vector.t _ n} * CacheDecode)) y) ->
          t (word 8) x -> CacheDecode -> option (A * {n : _ & Vector.t _ n} * CacheDecode) )
      n (b : Vector.t _ n) (cd : CacheDecode)
      (body_Proper :
         forall (x0 : ByteString)
                (f g : forall y : ByteString, lt_B y x0 -> CacheDecode -> option (A * ByteString * CacheDecode)),
           (forall (y : ByteString) (p : lt_B y x0), f y p = g y p) -> body x0 f = body x0 g)
      (body'_Proper :
         forall (x0 : nat)
                (f
                   g : forall y : nat,
                    (lt y x0)%nat -> t (word 8) y -> CacheDecode -> option (A * {n0 : nat & t Core.char n0} * CacheDecode)),
           (forall (y : nat) (p : (lt y x0)%nat), f y p = g y p) -> body' x0 f = body' x0 g)
    ,
      (forall n (b : Vector.t (word 8) n)
              (rec : forall x : ByteString,
                  lt_B x (build_aligned_ByteString b) -> CacheDecode -> option (A * ByteString * CacheDecode))
              (rec' : forall x : nat,
                  (lt x n)%nat -> t Core.char x -> CacheDecode ->
                  option (A * {n : _ & Vector.t _ n} * CacheDecode))
              cd,
          (forall m cd b a b' cd' b_lt b_lt' ,
              rec' m b_lt' b cd = Some (a, b', cd')
              -> rec (build_aligned_ByteString b) b_lt cd = Some (a, build_aligned_ByteString (projT2 b'), cd'))
          -> (forall m cd b b_lt b_lt' ,
                 rec' m b_lt' b cd = None
                 -> rec (build_aligned_ByteString b) b_lt cd = None)
          -> body (build_aligned_ByteString b) rec cd
             = match (body' n rec' b cd) with
               | Some (a, b', cd') => Some (a, build_aligned_ByteString (projT2 b'), cd')
               | None => None
               end)
      -> Fix well_founded_lt_b (fun _ : ByteString => CacheDecode -> option (A * ByteString * CacheDecode)) body (build_aligned_ByteString b) cd =
         match Fix Wf_nat.lt_wf (fun m : nat => Vector.t (word 8) m -> CacheDecode -> option (A * { n : _ & Vector.t _ n} * CacheDecode)) body' n b cd with
         | Some (a, b', cd') => Some (a, build_aligned_ByteString (projT2 b'), cd')
         | None => None
         end.
  Proof.
    intros.
    revert cd b; pattern n.
    eapply (well_founded_ind Wf_nat.lt_wf); intros.
    rewrite Init.Wf.Fix_eq, Init.Wf.Fix_eq.
    apply H; intros.
    erewrite H0, H1; eauto.
    rewrite H0, H1; eauto.
    eauto.
    eauto.
  Qed.

  Lemma lift_match_if_ByteAlign
        {T1}
        {T2 T3 T4 A : T1 -> Type}
        {B B' C}
    : forall (b : bool)
             (t1 : T1)
             (t e : option (A t1 * B * C))
             (b' : forall t1, T2 t1 -> T3 t1 -> T4 t1 -> bool)
             (t' e' : forall t1, T2 t1 -> T3 t1 -> T4 t1 -> option (A t1 * B' * C))
             (f : B' -> B)
             (t2 : T2 t1)
             (t3 : T3 t1)
             (t4 : T4 t1),
      (b = b' t1 t2 t3 t4)
      -> (t = match t' t1 t2 t3 t4 with
              | Some (a, b', c) => Some (a, f b', c)
              | None => None
              end)
      -> (e = match e' t1 t2 t3 t4 with
              | Some (a, b', c) => Some (a, f b', c)
              | None => None
              end)
      -> (if b then t else e) =
         match (fun t1 t2 t3 t4 => if b' t1 t2 t3 t4 then t' t1 t2 t3 t4 else e' t1 t2 t3 t4) t1 t2 t3 t4 with
         | Some (a, b', c) => Some (a, f b', c)
         | None => None
         end.
  Proof.
    intros; destruct b; eauto; rewrite <- H; simpl; eauto.
  Qed.

  Lemma lift_match_if_sumbool_ByteAlign
        {T1}
        {T3 : T1 -> Type}
        {P : forall t1 (t3 : T3 t1), Prop}
        {T2 T4 A : T1 -> Type}
        {B B' C}
    : forall (t1 : T1)
             (t3 : T3 t1)
             (b : forall t1 t3, {P t1 t3} + {~P t1 t3})
             (t : _ -> option (A t1 * B * C))
             (e : _ -> option (A t1 * B * C))
             (b' : forall t1 t3, T2 t1 -> T4 t1 -> {P t1 t3} + {~P t1 t3})
             (t' : forall t1 t3, T2 t1 -> T4 t1 -> _ -> option (A t1 * B' * C))
             (e' : forall t1 t3, T2 t1 -> T4 t1 -> _ -> option (A t1 * B' * C))
             (f : B' -> B)
             (t2 : T2 t1)
             (t4 : T4 t1),
      (b t1 t3 = b' t1 t3 t2 t4)
      -> (forall e'',
             t e'' = match t' t1 t3 t2 t4 e'' with
                     | Some (a, b', c) => Some (a, f b', c)
                     | None => None
                     end)
      -> (forall e'',
             e e'' = match e' t1 t3 t2 t4 e'' with
                     | Some (a, b', c) => Some (a, f b', c)
                     | None => None
                     end)
      -> (match b t1 t3 with
            left e'' => t e''
          | right e'' => e e''
          end) =
         match (fun t1 t2 t3 t4 =>
                  match b' t1 t3 t2 t4 with
                  | left e'' => t' t1 t3 t2 t4 e''
                  | right e'' => e' t1 t3 t2 t4 e''
                  end) t1 t2 t3 t4 with
         | Some (a, b', c) => Some (a, f b', c)
         | None => None
         end.
  Proof.
    intros; destruct b; eauto; rewrite <- H; simpl; eauto.
  Qed.

  Lemma build_aligned_ByteString_eq_split'
    : forall n sz v,
      (n <= sz)%nat
      ->
      build_aligned_ByteString v
      = build_aligned_ByteString (Guarded_Vector_split n sz v).
  Proof.
    intros; eapply ByteString_f_equal; simpl.
    instantiate (1 := eq_refl _); reflexivity.
    instantiate (1 := (le_plus_minus_r _ _ H)).
    generalize (le_plus_minus_r n sz H); clear.
    revert sz v; induction n; simpl; intros.
    unfold Guarded_Vector_split.
    rewrite <- Equality.transport_pp.
    generalize (eq_trans (minus_n_O sz) e); clear;
      intro.
    apply Eqdep_dec.eq_rect_eq_dec; auto with arith.
    destruct v; simpl in *.
    omega.
    unfold Guarded_Vector_split; fold Guarded_Vector_split;
      simpl.
    erewrite eq_rect_Vector_cons; eauto.
    f_equal.
    apply IHn.
    Grab Existential Variables.
    omega.
  Qed.

  Lemma optimize_Guarded_Decode {sz} {C} n
    : forall (a_opt : ByteString -> option C)
             (a_opt' : ByteString -> option C) v,
      (~ (n <= sz)%nat
       -> a_opt (build_aligned_ByteString v) = None)
      -> (le n sz -> a_opt  (build_aligned_ByteString (Guarded_Vector_split n sz v))
                     = a_opt'
                         (build_aligned_ByteString (Guarded_Vector_split n sz v)))
      -> a_opt (build_aligned_ByteString v) =
         If NPeano.leb n sz Then
            a_opt' (build_aligned_ByteString (Guarded_Vector_split n sz v))
            Else None.
  Proof.
    intros; destruct (NPeano.leb n sz) eqn: ?.
    - apply NPeano.leb_le in Heqb.
      rewrite <- H0.
      simpl; rewrite <- build_aligned_ByteString_eq_split'; eauto.
      eauto.
    - rewrite H; simpl; eauto.
      intro.
      rewrite <- NPeano.leb_le in H1; congruence.
  Qed.

  Lemma AlignedDecode4Char {C}
        {numBytes}
    : forall (v : Vector.t (word 8) (S (S (S (S numBytes)))))
             (t : _ -> C)
             (e : C)
             cd,
      Ifopt (decode_word
               (monoidUnit := ByteString_QueueMonoidOpt) (sz := 32) (build_aligned_ByteString v) cd) as w
                                                                                                          Then t w Else e  =
                                                                                                        Let n := Core.append_word (Vector.nth v (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
                                                                                                                                  (Core.append_word (Vector.nth v (Fin.FS (Fin.FS Fin.F1)))
                                                                                                                                                    (Core.append_word (Vector.nth v (Fin.FS Fin.F1)) (Vector.nth v Fin.F1))) in
        t (n, build_aligned_ByteString (snd (Vector_split 4 _ v)), addD cd 32).
  Proof.
    unfold LetIn; intros.
    unfold decode_word, WordOpt.decode_word.
    match goal with
      |- context[Ifopt ?Z as _ Then _ Else _] => replace Z with
        (let (v', v'') := Vector_split 4 numBytes v in Some (VectorByteToWord v', build_aligned_ByteString v'')) by (symmetry; apply (@aligned_decode_char_eq' _ 3 v))
    end.
    Local Transparent Vector_split.
    unfold Vector_split, If_Opt_Then_Else, If_Opt_Then_Else.
    f_equal.
    rewrite !Vector_nth_tl, !Vector_nth_hd.
    erewrite VectorByteToWord_cons.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    f_equal.
    erewrite VectorByteToWord_cons.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    erewrite VectorByteToWord_cons.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    erewrite VectorByteToWord_cons.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    Grab Existential Variables.
    omega.
    omega.
    omega.
    omega.
  Qed.

  Lemma split2_split2
    : forall n m o (w : word (n + (m + o))),
      split2' m o (split2' n (m + o) w) =
      split2' (n + m) o (eq_rect _ _ w _ (plus_assoc _ _ _)).
  Proof.
    induction n; simpl; intros.
    - rewrite <- Eqdep_dec.eq_rect_eq_dec; auto with arith.
    - rewrite IHn.
      f_equal.
      pose proof (shatter_word_S w); destruct_ex; subst.
      clear.
      rewrite <- WS_eq_rect_eq with (H := plus_assoc n m o).
      revert m o x0 x; induction n; simpl; intros.
      + rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
      + erewrite <- WS_eq_rect_eq; fold plus; pose proof (shatter_word_S x0);
          destruct_ex; subst; f_equal.
        rewrite IHn; f_equal.
        erewrite <- WS_eq_rect_eq; reflexivity.
  Qed.

  Lemma AlignedFormat32Char' {numBytes}
    : forall (w : word 32) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 32)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_word (monoidUnit := ByteString_QueueMonoidOpt) w)
                    ThenC c) ce)
                (ret (build_aligned_ByteString
                        (Vector.cons
                           _ (split1' 8 24 w) _
                           (Vector.cons
                              _
                              (split1' 8 16 (split2' 8 24 w)) _
                              (Vector.cons
                                 _
                                 (split1' 8 8 (split2' 16 16 w)) _
                                 (Vector.cons
                                    _
                                    (split2' 24 8 w) _ v)))), ce')).
  Proof.
    unfold compose, Bind2; intros.
    intros; setoid_rewrite (@format_words' _ _ 8 24 addE_addE_plus w).
    rewrite (@AlignedFormatChar _ _ 3).
    simplify with monad laws.
    unfold snd.
    rewrite H.
    simplify with monad laws.
    unfold fst.
    unfold mappend.
    unfold ByteStringQueueMonoid.
    rewrite <- build_aligned_ByteString_append.
    instantiate (1 := Vector.cons _ _ _ (Vector.cons _ _ _ (Vector.cons _ _ _ (Vector.nil _)))).
    unfold append.
    reflexivity.
    setoid_rewrite (@format_words' _ _ 8 16 addE_addE_plus _).
    rewrite (@AlignedFormatChar _ _ 2).
    reflexivity.
    setoid_rewrite (@format_words' _ _ 8 8 addE_addE_plus ).
    rewrite (@AlignedFormatChar _ _ 1) by apply aligned_format_char_eq.
    rewrite !addE_addE_plus; simpl plus.
    rewrite !split2_split2.
    simpl plus.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; auto with arith.
    reflexivity.
  Qed.

  Lemma AlignedFormat32Char {numBytes}
    : forall (w : word 32) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 32)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_word (monoidUnit := ByteString_QueueMonoidOpt) w)
                    ThenC c) ce)
                (ret (build_aligned_ByteString
                        (Vector.cons
                           _ (split2 24 8 w) _
                           (Vector.cons
                              _
                              (split2 16 8 (split1 24 8 w)) _
                              (Vector.cons
                                 _
                                 (split2 8 8 (split1 16 16 w)) _
                                 (Vector.cons
                                    _
                                    (split1 8 24 w) _ v)))), ce')).
  Proof.
    unfold compose, Bind2; intros.
    intros; setoid_rewrite (@format_words _ _ 8 24 addE_addE_plus w).
    rewrite (@AlignedFormatChar _ _ 3).
    simplify with monad laws.
    unfold snd.
    rewrite H.
    simplify with monad laws.
    unfold fst.
    unfold mappend.
    unfold ByteStringQueueMonoid.
    rewrite <- build_aligned_ByteString_append.
    instantiate (1 := Vector.cons _ _ _ (Vector.cons _ _ _ (Vector.cons _ _ _ (Vector.nil _)))).
    unfold append.
    reflexivity.
    setoid_rewrite (@format_words _ _ 8 16 addE_addE_plus  _).
    rewrite (@AlignedFormatChar _ _ 2).
    reflexivity.
    setoid_rewrite (@format_words _ _ 8 8).
    rewrite (@AlignedFormatChar _ _ 1) by apply aligned_format_char_eq.
    rewrite !addE_addE_plus; simpl plus.
    f_equiv.
    eauto.
  Qed.

  Fixpoint align_decode_list {A}
           (A_decode_align : forall n,
               Vector.t (word 8) n
               -> CacheDecode
               -> option (A * {n : _ & Vector.t _ n}
                          * CacheDecode))
           (n : nat)
           {sz}
           (v : Vector.t (word 8) sz)
           (cd : CacheDecode)
    : option (list A *  {n : _ & Vector.t _ n} * CacheDecode) :=
    match n with
    | 0 => Some (@nil _, existT _ _ v, cd)
    | S s' => `(x, b1, e1) <- A_decode_align sz v cd;
                `(xs, b2, e2) <- align_decode_list A_decode_align s' (projT2 b1) e1;
                Some ((x :: xs)%list, b2, e2)
    end.

  Lemma optimize_align_decode_list
        {A}
        (A_decode :
           ByteString
           -> CacheDecode
           -> option (A * ByteString * CacheDecode))
        (A_decode_align : forall n,
            Vector.t (word 8) n
            -> CacheDecode
            -> option (A * {n : _ & Vector.t _ n}
                       * CacheDecode))
        (A_decode_OK :
           forall n (v : Vector.t _ n) cd,
             A_decode (build_aligned_ByteString v) cd =
             Ifopt A_decode_align n v cd as a Then
                                              Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                              Else
                                              None)
    : forall (n : nat)
             {sz}
             (v : Vector.t (word 8) sz)
             (cd : CacheDecode),
      decode_list A_decode n (build_aligned_ByteString v) cd =
      Ifopt align_decode_list A_decode_align n v cd as a Then
                                                         Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                                         Else
                                                         None.
  Proof.
    induction n; simpl; intros; eauto.
    rewrite A_decode_OK.
    rewrite (If_Opt_Then_Else_DecodeBindOpt).
    destruct (A_decode_align sz v cd) as [ [ [? [? ?] ] ?]  | ]; simpl; eauto.
    rewrite IHn.
    rewrite (If_Opt_Then_Else_DecodeBindOpt).
    destruct (align_decode_list A_decode_align n t c)
      as [ [ [? [? ?] ] ?]  | ]; simpl; eauto.
  Qed.

  Lemma LetIn_If_Opt_Then_Else {A B C}
    : forall (a : A)
             (k : A -> option B)
             (t : B -> C)
             (e : C),
      (Ifopt LetIn a k as b Then t b Else e)
      = LetIn a (fun a => Ifopt k a as b Then t b Else e).
  Proof.
    reflexivity.
  Qed.

  Lemma decode_unused_word_aligned_ByteString_overflow
    : forall {sz'}
             (b : t (word 8) sz')
             {sz}
             (cd : CacheDecode),
      lt sz' sz
      -> decode_unused_word (8 * sz) (build_aligned_ByteString b) cd = None.
  Proof.
    induction b; intros.
    - unfold build_aligned_ByteString; simpl.
      inversion H; subst; reflexivity.
    - destruct sz; try omega.
      apply lt_S_n in H.
      pose proof (IHb _ cd H).
      unfold decode_unused_word, WordOpt.decode_word.
      rewrite <- mult_n_Sm, plus_comm.
      rewrite decode_unused_word_plus'.
      rewrite (@aligned_decode_unused_char_eq ).
      simpl.
      unfold decode_unused_word in H0.
      simpl in H0.
      destruct (decode_unused_word' (8 * sz)
                                    (build_aligned_ByteString b));
        simpl in *; try congruence.
  Qed.

  Lemma AlignedDecodeUnusedChar {C}
        {numBytes}
    : forall (v : Vector.t (word 8) (S numBytes))
             (t : (() * ByteString * CacheDecode) -> C)
             (e : C)
             cd,
      Ifopt (decode_unused_word
               (monoidUnit := ByteString_QueueMonoidOpt) 8 (build_aligned_ByteString v) cd)
      as w Then t w Else e
         =

         (t ((), build_aligned_ByteString (snd (Vector_split 1 _ v)), addD cd 8)).
  Proof.
    unfold LetIn; intros.
    unfold decode_unused_word, WordOpt.decode_word.
    rewrite aligned_decode_unused_char_eq; simpl.
    f_equal.
  Qed.

  Variable addD_addD_plus :
    forall cd n m, addD (addD cd n) m = addD cd (n + m).

  Lemma AlignedDecodeUnusedChars {C}
        {numBytes numBytes'}
    : forall (v : Vector.t (word 8) (numBytes' + numBytes))
             (k : _ -> option C)
             cd,
      BindOpt (decode_unused_word
                 (monoidUnit := ByteString_QueueMonoidOpt) (8 * numBytes') (build_aligned_ByteString v) cd) k =
      k ((), build_aligned_ByteString (snd (Vector_split numBytes' _ v)), addD cd (8 * numBytes')).
  Proof.
    induction numBytes'.
    - Local Transparent Vector_split.
      simpl; intros; unfold Vector_split; simpl.
      reflexivity.
    - simpl.
      replace (8 * S numBytes') with (8 + 8 * numBytes') by omega.
      unfold decode_unused_word; intros.
      rewrite decode_unused_word_plus'.
      rewrite (@aligned_decode_unused_char_eq ).
      simpl BindOpt.
      pose proof (IHnumBytes' (Vector.tl v) k (addD cd 8)).
      simpl in H.
      unfold decode_unused_word in H.
      simpl in *.
      fold plus in *. unfold Core.char in *.
      revert H;
        repeat match goal with
                 |- context [decode_unused_word' ?z ?b] =>
                 destruct (decode_unused_word' z b) as [ [? ?] | ] eqn: ?; simpl in *
               end; intros.
      destruct u.
      rewrite addD_addD_plus in H; simpl in H; rewrite H.
      destruct ((Vector_split numBytes' numBytes (Vector.tl v))); simpl.
      reflexivity.
      rewrite addD_addD_plus in H; simpl in H; rewrite H.
      destruct ((Vector_split numBytes' numBytes (Vector.tl v))); simpl.
      reflexivity.
  Qed.

  Lemma aligned_format_unused_char_eq
    : forall cd,
      refine (format_unused_word (monoidUnit := ByteString_QueueMonoidOpt) 8 cd)
             (ret (build_aligned_ByteString (Vector.cons _ (wzero 8) _ (Vector.nil _)), addE cd 8)).
  Proof.
    unfold format_unused_word, format_unused_word'; simpl.
    intros; refine pick val (wzero 8); eauto; simplify with monad laws.
    compute; intros.
    computes_to_inv; subst.
    match goal with
      |- computes_to (ret ?c) ?v => replace c with v
    end.
    computes_to_econstructor.
    f_equal.
    eapply ByteString_f_equal; simpl.
    instantiate (1 := eq_refl _).
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    erewrite eq_rect_Vector_cons; repeat f_equal.
    instantiate (1 := eq_refl _); reflexivity.
    Grab Existential Variables.
    reflexivity.
  Qed.

  Lemma AlignedFormatUnusedChar {numBytes}
    : forall ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 8)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_unused_word (monoidUnit := ByteString_QueueMonoidOpt) 8)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons _ (wzero 8) _ v), ce')).
  Proof.
    unfold compose, Bind2; simpl; intros.
    rewrite aligned_format_unused_char_eq.
    simplify with monad laws.
    simpl snd; rewrite H; simplify with monad laws.
    simpl.
    rewrite <- build_aligned_ByteString_append.
    reflexivity.
  Qed.

  Lemma AlignedFormat2UnusedChar {numBytes}
    : forall ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 16)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_unused_word (monoidUnit := ByteString_QueueMonoidOpt) 16)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons _ (wzero 8) _ (Vector.cons _ (wzero 8) _ v)), ce')).
  Proof.
    unfold compose, Bind2; intros.
    rewrite <- (AlignedFormat2Char (wzero 16)); eauto.
    unfold format_unused_word, format_word, compose, Bind2.
    simpl.
    unfold format_unused_word'; simpl.
    intros; refine pick val (wzero 16); eauto; simpl.
    simplify with monad laws.
    rewrite refineEquiv_bind_unit; simpl.
    reflexivity.
  Qed.

  Definition align_decode_sumtype
             {m : nat}
             {types : t Type m}
             (decoders :
                ilist (B := fun T =>
                              forall n,
                                Vector.t (word 8) n
                                -> CacheDecode
                                -> option (T * {n : _ & Vector.t (word 8) n} * CacheDecode)) types)
             (idx : Fin.t m)
             {n : nat}
             (v : Vector.t (word 8) n)
             (cd : CacheDecode)
    := `(a, b', cd') <- ith (decoders) idx n v cd;
         Some (inj_SumType types idx a, b', cd').

  Lemma align_decode_sumtype_OK'
        {m : nat}
        {types : t Type m}
        (align_decoders :
           ilist (B := fun T =>
                         forall n,
                           Vector.t (word 8) n
                           -> CacheDecode
                           -> option (T * {n : _ & Vector.t (word 8) n} * CacheDecode)) types)

        (decoders : ilist (B := fun T => ByteString -> CacheDecode -> option (T * ByteString * CacheDecode)) types)
        (decoders_OK : forall n v cd idx',
            ith decoders idx' (build_aligned_ByteString v) cd
            = Ifopt ith align_decoders idx' n v cd as a Then
                                                        Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                                        Else
                                                        None)
    : forall
      (idx : Fin.t m)
      {n : nat}
      (v : Vector.t (word 8) n)
      (cd : CacheDecode),
      decode_SumType types decoders idx (build_aligned_ByteString v) cd
      =
      Ifopt align_decode_sumtype align_decoders idx
            v cd as a Then
                      Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                      Else
                      None.
  Proof.
    intros.
    unfold decode_SumType, align_decode_sumtype.
    rewrite decoders_OK.
    destruct (ith align_decoders idx n v cd) as [ [ [? ?] ?] | ];
      reflexivity.
  Qed.

  Corollary align_decode_sumtype_OK
            {m : nat}
            {types : t Type m}
            (align_decoders :
               ilist (B := fun T =>
                             forall n,
                               Vector.t (word 8) n
                               -> CacheDecode
                               -> option (T * {n : _ & Vector.t (word 8) n} * CacheDecode)) types)

            (decoders : ilist (B := fun T => ByteString -> CacheDecode -> option (T * ByteString * CacheDecode)) types)
            (decoders_OK : forall n v cd,
                Iterate_Ensemble_BoundedIndex
                  (fun idx' => ith decoders idx' (build_aligned_ByteString v) cd
                               = Ifopt ith align_decoders idx' n v cd as a Then
                                                                           Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                                                           Else
                                                                           None))
    : forall
      (idx : Fin.t m)
      {n : nat}
      (v : Vector.t (word 8) n)
      (cd : CacheDecode),
      decode_SumType types decoders idx (build_aligned_ByteString v) cd
      =
      Ifopt align_decode_sumtype align_decoders idx
            v cd as a Then
                      Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                      Else
                      None.
  Proof.
    intros; eapply align_decode_sumtype_OK'; intros.
    pose proof (decoders_OK n0 v0 cd0).
    eapply Iterate_Ensemble_BoundedIndex_equiv in H.
    apply H.
  Qed.

  Lemma nth_Vector_split {A}
    : forall {sz} n v idx,
      Vector.nth (snd (Vector_split (A := A) n sz v)) idx
      = Vector.nth v (Fin.R n idx).
  Proof.
    induction n; simpl; intros; eauto.
    assert (forall A n b, exists a b', b = Vector.cons A a n b')
      by (clear; intros; pattern n, b; apply caseS; eauto).
    pose proof (H _ _ v); destruct_ex; subst.
    simpl.
    destruct (Vector_split n sz x0) as [? ?] eqn: ?.
    rewrite <- IHn.
    rewrite Heqp; reflexivity.
  Qed.

  Lemma eq_rect_Vector_tl {A}
    : forall n (v : Vector.t A (S n)) m H H',
      Vector.tl (eq_rect (S n) (t A) v (S m) H)
      = eq_rect _ (Vector.t A) (Vector.tl v) _ H'.
  Proof.
    intros n v; pattern n, v; apply Vector.caseS; simpl; intros.
    erewrite eq_rect_Vector_cons; simpl; eauto.
  Qed.

  Lemma Vector_split_merge {A}
    : forall sz m n (v : Vector.t A _),
      snd (Vector_split m _ (snd (Vector_split n (m + sz) v))) =
      snd (Vector_split (n + m) _ (eq_rect _ _ v _ (plus_assoc _ _ _))).
  Proof.
    induction m; intros; simpl.
    - induction n; simpl.
      + simpl in *.
        apply Eqdep_dec.eq_rect_eq_dec; auto with arith.
      + simpl in v.
        assert (forall A n b, exists a b', b = Vector.cons A a n b')
          by (clear; intros; pattern n, b; apply caseS; eauto).
        pose proof (H _ _ v); destruct_ex; subst.
        simpl.
        pose proof (IHn x0).
        destruct (Vector_split n sz x0) eqn: ?.
        simpl in *.
        rewrite H0.
        erewrite eq_rect_Vector_cons with (H' := (plus_assoc n 0 sz)); eauto; simpl.
        destruct (Vector_split (n + 0) sz (eq_rect (n + sz) (Vector.t A) x0 (n + 0 + sz) (plus_assoc n 0 sz))); reflexivity.
    - assert (n + (S m + sz) = S n + (m + sz)) by omega.
      fold plus in *; unfold Core.char in *.
      replace (Vector.tl (snd (Vector_split n (S (m + sz)) v)))
        with ((snd (Vector_split n (m + sz) (Vector.tl  (eq_rect _ _ v _ H))))).
      + pose proof (IHm n ((Vector.tl (eq_rect (n + (S m + sz)) (t A) v (S n + (m + sz)) H)))).
        destruct (Vector_split m sz (snd (Vector_split n (m + sz) (Vector.tl (eq_rect (n + (S m + sz)) (t A) v (S n + (m + sz)) H))))) eqn: ?; simpl in *.
        fold plus in *; rewrite Heqp.
        simpl; rewrite H0.
        clear.
        assert ( S (n + (m + sz)) = S (n + m + sz)) by omega.
        rewrite <- eq_rect_Vector_tl with (H1 := H0).
        rewrite <- Equality.transport_pp; simpl; clear.
        generalize (eq_trans H H0);
          generalize (NPeano.Nat.add_assoc n (S m) sz); clear H H0.
        revert sz m v; induction n; simpl.
        * intros.
          rewrite <- !Eqdep_dec.eq_rect_eq_dec; auto with arith.
          destruct (Vector_split m sz (Vector.tl v)) eqn: ?.
          simpl in *; fold plus in *; rewrite Heqp; reflexivity.
        * intros.
          assert (n + S (m + sz) = S (n + m + sz)) by omega.
          assert (n + S (m + sz) = n + S m + sz) by omega.
          (* Again, 8.4 compatibility problems. *)
          erewrite eq_rect_Vector_tl with (H' := H0).
          erewrite eq_rect_Vector_tl with (H' := H1).
          pose proof (IHn _ _ (Vector.tl v) H1 H0).
          destruct ((Vector_split (n + m) sz (Vector.tl (eq_rect (n + S (m + sz)) (t A) (Vector.tl v) (S (n + m + sz)) H0)))) eqn: ?.
          simpl in *; fold plus in *; rewrite Heqp, H2; simpl.
          destruct (Vector_split (n + S m) sz (eq_rect (n + S (m + sz)) (Vector.t A) (Vector.tl v) (n + S m + sz) H1)) eqn: ?.
          replace (plus_assoc n (S m) sz) with H1; simpl.
          rewrite Heqp0; reflexivity.
          eapply Eqdep_dec.eq_proofs_unicity; intros; omega.
      + clear.
        revert H v.
        assert (forall q (v : t A (n + (S q))) H,
                   snd (Vector_split n q (Vector.tl (eq_rect (n + (S q)) (t A) v (S n + (q)) H))) =
                   Vector.tl (snd (Vector_split n (S (q)) v))).
        { induction n; simpl; intros.
          rewrite <- Eqdep_dec.eq_rect_eq_dec; auto with arith.
          assert (n + S q = S (n + q)) by omega.
          rewrite eq_rect_Vector_tl with (H' := H0).
          pose proof (IHn q (Vector.tl v) H0).
          destruct ((Vector_split n q (Vector.tl (eq_rect (n + S q) (t A) (Vector.tl v) (S n + q) H0))))
                   eqn: ?.
          fold plus in *; simpl in *; rewrite Heqp; simpl.
          rewrite H1.
          destruct (Vector_split n (S q) (Vector.tl v)); reflexivity.
        }
        intros; rewrite H; reflexivity.
  Qed.

  Lemma zeta_to_fst {A B C}
    : forall (ab : A * B) (k : A -> B -> C),
      (let (a, b) := ab in (k a b)) =
      k (fst ab) (snd ab).
  Proof.
    destruct ab; reflexivity.
  Qed.

  Lemma zeta_inside_ret {A B C}
    : forall (ab : A * B) (k : A -> B -> C),
      refine (let (a, b) := ab in ret (k a b))
             (ret (let (a, b) := ab in k a b)).
  Proof.
    destruct ab; reflexivity.
  Qed.

  Ltac rewrite_DecodeOpt2_fmap :=
    set_refine_evar;
    progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
    ?DecodeOpt2_fmap_if_bool;
    subst_refine_evar.


  Lemma Ifopt_Ifopt {A A' B}
    : forall (a_opt : option A)
             (t : A -> option A')
             (e : option A')
             (t' : A' -> B)
             (e' :  B),
      Ifopt (Ifopt a_opt as a Then t a Else e) as a' Then t' a' Else e' =
                                                  Ifopt a_opt as a Then (Ifopt (t a) as a' Then t' a' Else e') Else (Ifopt e as a' Then t' a' Else e').
  Proof.
    destruct a_opt; simpl; reflexivity.
  Qed.

  Corollary AlignedDecodeNat {C}
            {numBytes}
    : forall (v : Vector.t (word 8) (S numBytes))
             (t : _ -> C)
             e
             cd,
      Ifopt (decode_nat (monoidUnit := ByteString_QueueMonoidOpt) 8 (build_aligned_ByteString v) cd) as w
                                                                                                          Then t w Else e
                                                                                                        =
                                                                                                        Let n := wordToNat (Vector.nth v Fin.F1) in
        t (n, build_aligned_ByteString (snd (Vector_split 1 _ v)), addD cd 8).
  Proof.
    unfold CacheDecode.
    unfold decode_nat, DecodeBindOpt2; intros.
    unfold BindOpt at 1.
    rewrite AlignedDecodeChar.
    reflexivity.
  Qed.

  Lemma optimize_Guarded_Decode' {sz} {C} n
    : forall (a_opt : ByteString -> C)
             (a_opt' : ByteString -> C) v c,
      (~ (n <= sz)%nat
       -> a_opt (build_aligned_ByteString v) = c)
      -> (le n sz -> a_opt  (build_aligned_ByteString (Guarded_Vector_split n sz v))
                     = a_opt'
                         (build_aligned_ByteString (Guarded_Vector_split n sz v)))
      -> a_opt (build_aligned_ByteString v) =
         If NPeano.leb n sz Then
            a_opt' (build_aligned_ByteString (Guarded_Vector_split n sz v))
            Else c.
  Proof.
    intros; destruct (NPeano.leb n sz) eqn: ?.
    - apply NPeano.leb_le in Heqb.
      rewrite <- H0.
      simpl; rewrite <- build_aligned_ByteString_eq_split'; eauto.
      eauto.
    - rewrite H; simpl; eauto.
      intro.
      rewrite <- NPeano.leb_le in H1; congruence.
  Qed.


  Definition calculate_Checksum {sz}
    : AlignedEncodeM sz :=
    fun v idx' ce =>
      let checksum := InternetChecksum.Vector_checksum v in
      (SetByteAt (split1 8 8 checksum) 10 >>
                 SetByteAt (split2 8 8 checksum) 11)%AlignedEncodeM v idx' ce.

  Lemma CorrectAlignedEncoderForIPChecksumThenC
        (format_A format_B : CacheFormat -> Comp (ByteString * CacheFormat))
        (encode_A : forall sz, AlignedEncodeM sz)
        (encode_B : forall sz, AlignedEncodeM sz)
        (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
        (encoder_A_OK : CorrectAlignedEncoder format_A encode_A)
    : CorrectAlignedEncoder
        (format_B ThenChecksum IPChecksum_Valid' OfSize 16 ThenCarryOn format_A)
        (fun sz => encode_B sz >>
                            SetCurrentByte (wzero 8) >>
                            SetCurrentByte (wzero 8) >>
                            encode_A sz >>
                            calculate_Checksum)% AlignedEncodeM.
  Proof.
  Admitted.

  Lemma AlignedDecode_shift_if_bool {A B C : Type}
        (decode_A : DecodeM A ByteString)
        (decode_B : A -> DecodeM B ByteString)
        (decode_C : A -> B -> DecodeM C ByteString)
        (cond : A -> bool)
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM
        (fun bs cd => `(a, bs', cd') <- decode_A bs cd;
                        `(b, bs', cd') <- decode_B a bs' cd';
                        if cond a
                        then decode_C a b bs' cd'
                        else None)
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => `(a, bs', cd') <- decode_A bs cd;
                           if cond a
                           then `(b, bs', cd') <- decode_B a bs' cd'; decode_C a b bs' cd'
                           else None)
           aligned_decoder.
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans; eauto;
      intros; simpl; try reflexivity.
    simpl; destruct (decode_A b cd) as [ [ [? ?] ?] | ]; simpl; eauto.
    find_if_inside; eauto.
    destruct (decode_B a b0 c) as [ [ [? ?] ?] | ]; simpl; eauto.
  Qed.

  Lemma AlignedDecode_shift_if_Sumb {A B C : Type}
        (decode_A : DecodeM A ByteString)
        (decode_B : A -> DecodeM B ByteString)
        (decode_C : A -> B -> DecodeM C ByteString)
        (P : A -> Prop)
        (cond : forall a, {P a} + {~P a})
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM
        (fun bs cd => `(a, bs', cd') <- decode_A bs cd;
                        `(b, bs', cd') <- decode_B a bs' cd';
                        if cond a
                        then decode_C a b bs' cd'
                        else None)
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => `(a, bs', cd') <- decode_A bs cd;
                           if cond a
                           then `(b, bs', cd') <- decode_B a bs' cd'; decode_C a b bs' cd'
                           else None)
           aligned_decoder.
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans; eauto;
      intros; simpl; try reflexivity.
    simpl; destruct (decode_A b cd) as [ [ [? ?] ?] | ]; simpl; eauto.
    find_if_inside; eauto.
    destruct (decode_B a b0 c) as [ [ [? ?] ?] | ]; simpl; eauto.
  Qed.

  Lemma AlignedDecode_CollapseWord
    : forall (ResultT : Type) (sz sz' : nat)
             aligned_decoder
             (k : word sz -> word sz' -> _ -> CacheDecode -> option (ResultT * _ * CacheDecode)),
      DecodeMEquivAlignedDecodeM
        (fun bs cd => `(w, b', cd') <- decode_word bs cd;
                        k (split1' sz sz' w) (split2' sz sz' w) b' cd')
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => `(w, b', cd') <- decode_word bs cd;
                           `(w', b'0, cd'0) <- decode_word b' cd';
                           k w w' b'0 cd'0)
           aligned_decoder.
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans; eauto;
      intros; simpl; try reflexivity.
    rewrite CollapseWord; eauto.
  Qed.

  Lemma AlignedDecodeBind4CharM:
    forall (cache : Cache) (cacheAddNat : CacheAdd cache nat),
      (forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m)) ->
      forall (C : Type) (t : word 32 -> DecodeM C ByteString)
             (t' : word 32 -> forall numBytes : nat, AlignedDecodeM C numBytes),
        (forall b : word 32, DecodeMEquivAlignedDecodeM (t b) (t' b)) ->
        DecodeMEquivAlignedDecodeM
          (fun (v : ByteString) (cd : CacheDecode) => `(a, b0, cd') <-
                                                       decode_word v cd;
                                                        t a b0 cd')
          (fun numBytes : nat =>
             (b1 <- GetCurrentByte;
                b2 <- GetCurrentByte;
                b3 <- GetCurrentByte;
                b4 <- GetCurrentByte;
                w <- return (Core.append_word b4 (Core.append_word b3 (Core.append_word b2 b1)));
                              t' w numBytes)%AlignedDecodeM).
  Proof.
  Admitted.

  Lemma AlignedDecode_CollapseWord' {A B}
    : forall (ResultT : Type) (sz sz' : nat)
             aligned_decoder
             (decode_A : DecodeM A ByteString)
             (decode_B : DecodeM B ByteString)
             (f : word sz -> A)
             (f' : word sz' -> B)
             (k : A -> B -> _ -> CacheDecode -> option (ResultT * _ * CacheDecode)),
      DecodeMEquivAlignedDecodeM
        (fun bs cd => `(w, b', cd') <- decode_word bs cd;
                        k (f (split1' sz sz' w)) (f' (split2' sz sz' w)) b' cd')
        aligned_decoder
      -> (forall bs cd, Ifopt (decode_word (sz := sz) bs cd) as a Then Some (f (fst (fst a)), (snd (fst a)), snd a) Else None = decode_A bs cd)
      -> (forall bs cd, Ifopt (decode_word (sz := sz') bs cd) as a Then Some (f' (fst (fst a)), (snd (fst a)), snd a) Else None = decode_B bs cd)
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => `(a, b', cd') <- decode_A bs cd;
                           `(b, b'0, cd'0) <- decode_B b' cd';
                           k a b b'0 cd'0)
           aligned_decoder.
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans; eauto;
      intros; simpl; try reflexivity.
    setoid_rewrite <- H0.
    rewrite <- (fun H => CollapseWord H sz sz' b cd (fun w w' => k (f w) (f' w'))) by eauto.
    destruct (decode_word b cd) as [ [ [? ?] ?] | ]; simpl; eauto.
    rewrite <- H1.
    destruct (decode_word b0 c) as [ [ [? ?] ?] | ]; simpl; eauto.
  Qed.

  Definition forget_word {n} := fun (w : word n) => tt.
  Lemma decode_word_eq_decode_unused_word {n}
    : forall (bs : ByteString) (cd : CacheDecode),
      (Ifopt decode_word (sz := n) bs cd as a Then Some (forget_word (fst (fst a)), snd (fst a), snd a) Else None) = decode_unused_word n bs cd.
  Proof.
    intros; pose proof monoid_dequeue_word_eq_decode_word'; simpl in H.
    unfold decode_word; rewrite <- H.
    unfold decode_unused_word, decode_unused_word'.
    destruct (WordOpt.monoid_dequeue_word n bs); reflexivity.
  Qed.

  Lemma decode_word_eq_decode_bool
    : forall (bs : ByteString) (cd : CacheDecode),
      (Ifopt decode_word bs cd as a Then Some (@whd 0 (fst (fst a)), snd (fst a), snd a) Else None) = Bool.decode_bool bs cd.
  Proof.
    intros; pose proof monoid_dequeue_word_eq_decode_word'; simpl in H.
    unfold decode_word; rewrite <- H.
    unfold decode_word, Bool.decode_bool; simpl.
    destruct (ByteString_dequeue bs) as [ [? ?] | ]; reflexivity.
  Qed.

  Lemma decode_word_eq_decode_word {n}
    : forall (bs : ByteString) (cd : CacheDecode),
      (Ifopt decode_word (sz := n) bs cd as a Then Some (id (fst (fst a)), snd (fst a), snd a) Else None) = decode_word bs cd.
  Proof.
    intros; destruct (decode_word bs cd) as [ [ [? ?] ?] | ]; try reflexivity.
  Qed.

  Definition Aligned_decode_enum
             {len : nat}
             {cache : Cache}
             {cacheAddNat : CacheAdd cache nat}
             (tb : t (word 8) (S len)) :=
    (fun n => (w <- GetCurrentByte ;
                 Ifopt word_indexed w tb as idx Then ReturnAlignedDecodeM idx Else ThrowAlignedDecodeM (n := n))%AlignedDecodeM).

  Lemma AlignedDecodeBindEnumM {A}
        {len}
    : forall (t : Fin.t (S len) -> DecodeM A ByteString)
             (t' : Fin.t (S len) -> forall numBytes : nat, AlignedDecodeM A numBytes)
             (tb : Vector.t (word 8) (S len)),
      (forall b2 : Fin.t (S len), DecodeMEquivAlignedDecodeM (t b2) (t' b2)) ->
      DecodeMEquivAlignedDecodeM
        (fun (v : ByteString) (cd : CacheDecode) => `(a, b0, cd') <-
                                                     decode_enum tb v cd;
                                                      t a b0 cd')
        (fun numBytes : nat => (b <- Aligned_decode_enum tb numBytes;
                                  t' b numBytes)%AlignedDecodeM).
  Proof.
  Admitted.

  Lemma AlignedDecodeUnused2CharM:
    DecodeMEquivAlignedDecodeM (decode_unused_word 16)
                               (fun numBytes : nat => SkipCurrentByte).
  Proof.
  Admitted.

  Lemma AlignedDecodeBindUnused2CharM {C : Type}
        (t : unit -> DecodeM C ByteString)
        (t' : unit -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (DecodeMEquivAlignedDecodeM (t ()) (@t' ()))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_unused_word (monoidUnit := ByteString_QueueMonoidOpt) 16 v cd;
                          t a b0 cd')
           (fun numBytes => b <- SkipCurrentByte; @t' b numBytes)%AlignedDecodeM.
  Proof.
    intro; eapply Bind_DecodeMEquivAlignedDecodeM; eauto using AlignedDecodeUnused2CharM.
    intro; destruct a; eauto.
  Qed.

End AlignedDecoders.

Ltac encoder_reflexivity :=
  match goal with
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c ?d ?e ?f), ?store' ?a ?b ?c ?d ?e ?f)) =>
    let encoder'' := (eval pattern a, b, c, d, e, f in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c, d, e, f in store) in
    let store'' := (match store'' with ?store _ _ _ _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c ?d ?e), ?store' ?a ?b ?c ?d ?e)) =>
    let encoder'' := (eval pattern a, b, c, d, e in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c, d, e in store) in
    let store'' := (match store'' with ?store _ _ _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c ?d), ?store' ?a ?b ?c ?d)) =>
    let encoder'' := (eval pattern a, b, c, d in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c, d in store) in
    let store'' := (match store'' with ?store _ _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c), ?store' ?a ?b ?c)) =>
    let encoder'' := (eval pattern a, b, c in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c in store) in
    let store'' := (match store'' with ?store _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b), ?store' ?a ?b)) =>
    let encoder'' := (eval pattern a, b in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ => encoder end) in
    let store'' := (eval pattern a, b in store) in
    let store'' := (match store'' with ?store _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?p), ?store' ?p)) =>
    let encoder'' := (eval pattern p in encoder) in
    let encoder'' := (match encoder'' with ?encoder p => encoder end) in
    let store'' := (eval pattern p in store) in
    let store'' := (match store'' with ?store p => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  end.
(* 8 subgoals, subgoal 1 (ID 13672) *)

(*   H : cache_inv_Property ?6326 *)
(*         (fun P0 : () -> Prop => *)
(*          (fun P : CacheDecode -> Prop => *)
(*           (fun P1 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P1 cd -> P1 (addD cd b)) P /\ *)
(*           (fun P1 : CacheDecode -> Prop => *)
(*            (fun P2 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P2 cd -> P2 (addD cd b)) P1 /\ *)
(*            (fun P2 : CacheDecode -> Prop => *)
(*             (fun P3 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P3 cd -> P3 (addD cd b)) P2 /\ *)
(*             (fun P3 : CacheDecode -> Prop => *)
(*              (fun P4 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P4 cd -> P4 (addD cd b)) P3 /\ *)
(*              (fun P4 : CacheDecode -> Prop => *)
(*               (fun P5 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P5 cd -> P5 (addD cd b)) P4 /\ *)
(*               (fun P5 : CacheDecode -> Prop => *)
(*                (fun P6 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P6 cd -> P6 (addD cd b)) P5 /\ *)
(*                (fun P6 : CacheDecode -> Prop => *)
(*                 (fun P7 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P7 cd -> P7 (addD cd b)) P6 /\ *)
(*                 (fun P7 : CacheDecode -> Prop => *)
(*                  (fun P8 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P8 cd -> P8 (addD cd b)) *)
(*                    P7 /\ (fun P8 : CacheDecode -> Prop => (fun .. => .., ..) P8 /\ (fun .. => .. /\ ..) P8) P7) *)
(*                   P6) P5) P4) P3) P2) P1) P) P0 /\ *)
(*          ?6529 P0 /\ *)
(*          (forall (b : ByteString) (ctx u : ()) (b' : ByteString) (ctx' : ()), *)
(*           decode_IPChecksum b ctx = Some (u, b', ctx') -> P0 ctx -> P0 ctx')) *)
(*   StringId := "TotalLength" : string *)
(*   StringId0 := "ID" : string *)
(*   StringId1 := "DF" : string *)
(*   StringId2 := "MF" : string *)
(*   StringId3 := "FragmentOffset" : string *)
(*   StringId4 := "TTL" : string *)
(*   StringId5 := "Protocol" : string *)
(*   StringId6 := "ICMP" : string *)
(*   StringId7 := "TCP" : string *)
(*   StringId8 := "UDP" : string *)
(*   StringId9 := "SourceAddress" : string *)
(*   StringId10 := "DestAddress" : string *)
(*   StringId11 := "Options" : string *)
(*   H0 : (fun _ : word 4 => True) (natToWord 4 4) *)
(*   proj : nat *)
(*   H1 : (fun n : nat => (n < pow2 4)%nat) proj *)
(*   H2 : (fun _ : () => True) () *)
(*   proj0 : word 16 *)
(*   H3 : (fun _ : word 16 => True) proj0 *)
(*   proj1 : word 16 *)
(*   H4 : (fun _ : word 16 => True) proj1 *)
(*   H5 : (fun _ : () => True) () *)
(*   proj2 : bool *)
(*   H6 : (fun _ : bool => True) proj2 *)
(*   proj3 : bool *)
(*   H7 : (fun _ : bool => True) proj3 *)
(*   proj4 : word 13 *)
(*   H8 : (fun _ : word 13 => True) proj4 *)
(*   proj5 : word 8 *)
(*   H9 : (fun _ : word 8 => True) proj5 *)
(*   proj6 : Fin.t 3 *)
(*   H10 : (fun _ : Fin.t 3 => True) proj6 *)
(*   H11 : cache_inv_Property ?6326 ?11546 *)
(*   ============================ *)
(*    forall *)
(*      a' : nat * *)
(*           (id (word 16) * *)
(*            (id (word 16) * *)
(*             (id bool * *)
(*              (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))), *)
(*    ((((((((?9072 a' /\ (fst a' < pow2 4)%nat) /\ fst a' = proj) /\ fst (snd a') = proj0) /\ *)
(*         fst (snd (snd a')) = proj1) /\ fst (snd (snd (snd a'))) = proj2) /\ *)
(*       fst (snd (snd (snd (snd a')))) = proj3) /\ fst (snd (snd (snd (snd (snd a'))))) = proj4) /\ *)
(*     fst (snd (snd (snd (snd (snd (snd a')))))) = proj5) /\ *)
(*    fst (snd (snd (snd (snd (snd (snd (snd a'))))))) = proj6 ->  *)
(*    a' = ?13671 *)

(* subgoal 2 (ID 13673) is: *)
(*  decides ?13670 *)
(*    (((((((((?9072 ?13671 /\ (fst ?13671 < pow2 4)%nat) /\ fst ?13671 = proj) /\ fst (snd ?13671) = proj0) /\ *)
(*          fst (snd (snd ?13671)) = proj1) /\ fst (snd (snd (snd ?13671))) = proj2) /\ *)
(*        fst (snd (snd (snd (snd ?13671)))) = proj3) /\  *)
(*       fst (snd (snd (snd (snd (snd ?13671))))) = proj4) /\  *)
(*      fst (snd (snd (snd (snd (snd (snd ?13671)))))) = proj5) /\ *)
(*     fst (snd (snd (snd (snd (snd (snd (snd ?13671))))))) = proj6) *)
(* subgoal 3 (ID 6524) is: *)
(*  forall data : IPv4_Packet, *)
(*  ((|data!StringId11 |) < 11)%nat /\ *)
(*  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (4 * (..))))))))))))))))))))) < *)
(*   wordToNat data!StringId)%nat -> *)
(*  (fun *)
(*     a : nat * *)
(*         (id (word 16) * *)
(*          (id (word 16) * *)
(*           (id bool * *)
(*            (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))) => *)
(*   (fun *)
(*      data0 : nat * *)
(*              (id (word 16) * *)
(*               (id (word 16) * *)
(*                (id bool * *)
(*                 (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))) => *)
(*    ?9072 data0 /\ *)
(*    (fun *)
(*       p : nat * *)
(*           (id (word 16) * *)
(*            (id (word 16) * *)
(*             (id bool * *)
(*              (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))) => *)
(*     (fun n : nat => (n < pow2 4)%nat) (fst p)) data0) a) *)
(*    ((fun H0 : IPv4_Packet => *)
(*      (IPv4_Packet_Header_Len H0, *)
(*      (fun H1 : IPv4_Packet => *)
(*       (prim_fst H1, *)
(*       (fun H2 : IPv4_Packet => *)
(*        ((fun a : IPv4_Packet => prim_fst (prim_snd a)) H2, *)
(*        (fun H3 : IPv4_Packet => *)
(*         ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd a))) H3, *)
(*         (fun H4 : IPv4_Packet => *)
(*          ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd a)))) H4, *)
(*          (fun H5 : IPv4_Packet => *)
(*           ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (prim_snd a))))) H5, *)
(*           (fun H6 : IPv4_Packet => *)
(*            ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (prim_snd (prim_snd a)))))) H6, *)
(*            (fun H7 : IPv4_Packet => *)
(*             ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (..))))) H7, ?6964 H7)) H6)) H5)) H4)) *)
(*           H3)) H2)) H1)) H0)) data) *)
(* subgoal 4 (ID 6525) is: *)
(*  forall *)
(*    (a' : nat * *)
(*          (id (word 16) * *)
(*           (id (word 16) * *)
(*            (id bool * *)
(*             (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966)))))))) *)
(*    (b : ByteString) (a : IPv4_Packet) (ce ce' ce'' : CacheFormat)  *)
(*    (b' b'' : ByteString) (c : word 16), *)
(*  (fun *)
(*     (a'0 : nat * *)
(*            (id (word 16) * *)
(*             (id (word 16) * *)
(*              (id bool * *)
(*               (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966)))))))) *)
(*     (env : CacheFormat) => *)
(*   (format_word (natToWord 4 4) *)
(*    ThenC (fun *)
(*             (aa' : nat * *)
(*                    (id (word 16) * *)
(*                     (id (word 16) * *)
(*                      (id bool * *)
(*                       (id bool * *)
(*                        (id (word 13) * *)
(*                         (id (word 8) * (id (EnumType (StringId6 :: StringId7 :: [StringId8])) * ?6966)))))))) *)
(*             (env0 : CacheFormat) => *)
(*           (format_nat 4 (fst aa') *)
(*            ThenC (fun *)
(*                     (a'1 : id (word 16) * *)
(*                            (id (word 16) * *)
(*                             (id bool * *)
(*                              (id bool * *)
(*                               (id (word 13) * *)
(*                                (id (word 8) * (id (EnumType (StringId6 :: StringId7 :: [StringId8])) * ?6966))))))) *)
(*                     (env1 : CacheFormat) => *)
(*                   (format_unused_word 8 *)
(*                    ThenC (fun *)
(*                             (aa'0 : id (word 16) * *)
(*                                     (id (word 16) * *)
(*                                      (id bool * *)
(*                                       (id bool * *)
(*                                        (id (word 13) * *)
(*                                         (id (word 8) * *)
(*                                          (id (EnumType (StringId6 :: StringId7 :: [StringId8])) * ?6966))))))) *)
(*                             (env2 : CacheFormat) => *)
(*                           (format_word (fst aa'0) *)
(*                            ThenC (fun *)
(*                                     (aa'1 : id (word 16) * *)
(*                                             (id bool * *)
(*                                              (id bool * *)
(*                                               (id (word 13) * (id (word 8) * (id (EnumType (..)) * ?6966)))))) *)
(*                                     (env3 : CacheFormat) => *)
(*                                   (format_word (fst aa'1) *)
(*                                    ThenC (fun *)
(*                                             (a'2 : id bool * (id bool * (id (word 13) * (id (..) * (.. * ..))))) *)
(*                                             (env4 : CacheFormat) => *)
(*                                           (format_unused_word 1 *)
(*                                            ThenC (fun (aa'2 : id bool * (.. * ..)) (env5 : CacheFormat) => *)
(*                                                   (format_bool (..) ThenC (..) (..)) env5) a'2) env4)  *)
(*                                            (snd aa'1)) env3)  *)
(*                                    (snd aa'0)) env2) a'1) env1)  *)
(*                    (snd aa')) env0) a'0) env) a' ce ↝  *)
(*  (b', ce') -> *)
(*  (fun H0 : IPv4_Packet => *)
(*   (IPv4_Packet_Header_Len H0, *)
(*   (fun H1 : IPv4_Packet => *)
(*    (prim_fst H1, *)
(*    (fun H2 : IPv4_Packet => *)
(*     ((fun a0 : IPv4_Packet => prim_fst (prim_snd a0)) H2, *)
(*     (fun H3 : IPv4_Packet => *)
(*      ((fun a0 : IPv4_Packet => prim_fst (prim_snd (prim_snd a0))) H3, *)
(*      (fun H4 : IPv4_Packet => *)
(*       ((fun a0 : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd a0)))) H4, *)
(*       (fun H5 : IPv4_Packet => *)
(*        ((fun a0 : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (prim_snd a0))))) H5, *)
(*        (fun H6 : IPv4_Packet => *)
(*         ((fun a0 : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (prim_snd (prim_snd a0)))))) H6, *)
(*         (fun H7 : IPv4_Packet => *)
(*          ((fun a0 : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (..))))) H7, ?6964 H7)) H6)) H5)) H4)) *)
(*        H3)) H2)) H1)) H0)) a = a' -> *)
(*  ((|a!StringId11 |) < 11)%nat /\ *)
(*  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (..)))))))))))))))))))) < wordToNat a!StringId)%nat -> *)
(*  (format_word a!StringId9 *)
(*   ThenC format_word a!StringId10 *)
(*         ThenC format_list format_word a!StringId11 ThenC (fun e : () => ret (ByteString_id, e))) ce' *)
(*  ↝ (b'', ce'') -> *)
(*  True -> *)
(*  {c0 : word 16 | *)
(*  forall ext : ByteString, *)
(*  IPChecksum_Valid' *)
(*    (bin_measure *)
(*       (mappend b' *)
(*          (mappend *)
(*             (format_checksum ByteString AlignedByteString.ByteStringQueueMonoid ByteString_QueueMonoidOpt 16 c0) *)
(*             b''))) *)
(*    (mappend *)
(*       (mappend b' *)
(*          (mappend *)
(*             (format_checksum ByteString AlignedByteString.ByteStringQueueMonoid ByteString_QueueMonoidOpt 16 c0) *)
(*             b'')) ext)} ↝ c -> *)
(*  ?6512 a' *)
(*    (mappend *)
(*       (mappend *)
(*          (format_checksum ByteString AlignedByteString.ByteStringQueueMonoid ByteString_QueueMonoidOpt 16 c) b'') *)
(*       b) *)
(* subgoal 5 (ID 6526) is: *)
(*  forall *)
(*    proj : nat * *)
(*           (id (word 16) * *)
(*            (id (word 16) * *)
(*             (id bool * *)
(*              (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))), *)
(*  (fun *)
(*     a : nat * *)
(*         (id (word 16) * *)
(*          (id (word 16) * *)
(*           (id bool * *)
(*            (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))) => *)
(*   (fun *)
(*      data : nat * *)
(*             (id (word 16) * *)
(*              (id (word 16) * *)
(*               (id bool * *)
(*                (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))) => *)
(*    ?9072 data /\ *)
(*    (fun *)
(*       p : nat * *)
(*           (id (word 16) * *)
(*            (id (word 16) * *)
(*             (id bool * *)
(*              (id bool * (id (word 13) * (id (word 8) * (id (EnumType ("ICMP" :: "TCP" :: ["UDP"])) * ?6966))))))) => *)
(*     (fun n : nat => (n < pow2 4)%nat) (fst p)) data) a) proj -> *)
(*  cache_inv_Property ?6326 ?6529 -> *)
(*  CorrectDecoder AlignedByteString.ByteStringQueueMonoid *)
(*    (fun data : IPv4_Packet => *)
(*     (((|data!StringId11 |) < 11)%nat /\ *)
(*      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (..)))))))))))))))))) < wordToNat data!StringId)%nat) /\ *)
(*     (fun H0 : IPv4_Packet => *)
(*      (IPv4_Packet_Header_Len H0, *)
(*      (fun H1 : IPv4_Packet => *)
(*       (prim_fst H1, *)
(*       (fun H2 : IPv4_Packet => *)
(*        ((fun a : IPv4_Packet => prim_fst (prim_snd a)) H2, *)
(*        (fun H3 : IPv4_Packet => *)
(*         ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd a))) H3, *)
(*         (fun H4 : IPv4_Packet => *)
(*          ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd a)))) H4, *)
(*          (fun H5 : IPv4_Packet => *)
(*           ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (prim_snd a))))) H5, *)
(*           (fun H6 : IPv4_Packet => *)
(*            ((fun a : IPv4_Packet => prim_fst (prim_snd (prim_snd (prim_snd (..))))) H6, *)
(*            (fun H7 : IPv4_Packet => ((fun a : IPv4_Packet => prim_fst (prim_snd (..))) H7, ?6964 H7)) H6)) H5)) *)
(*            H4)) H3)) H2)) H1)) H0)) data = proj) (fun (_ : IPv4_Packet) (_ : ByteString) => True) *)
(*    (fun data : IPv4_Packet => *)
(*     format_word data!StringId9 *)
(*     ThenC format_word data!StringId10 *)
(*           ThenC format_list format_word data!StringId11 ThenC (fun e : () => ret (ByteString_id, e))) *)
(*    (?6507 proj) ?6326 *)
(* subgoal 6 (ID 6333) is: *)
(*  cache_inv_Property ?6326 *)
(*    (fun P0 : () -> Prop => *)
(*     (fun P : CacheDecode -> Prop => *)
(*      (fun P1 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P1 cd -> P1 (addD cd b)) P /\ *)
(*      (fun P1 : CacheDecode -> Prop => *)
(*       (fun P2 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P2 cd -> P2 (addD cd b)) P1 /\ *)
(*       (fun P2 : CacheDecode -> Prop => *)
(*        (fun P3 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P3 cd -> P3 (addD cd b)) P2 /\ *)
(*        (fun P3 : CacheDecode -> Prop => *)
(*         (fun P4 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P4 cd -> P4 (addD cd b)) P3 /\ *)
(*         (fun P4 : CacheDecode -> Prop => *)
(*          (fun P5 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P5 cd -> P5 (addD cd b)) P4 /\ *)
(*          (fun P5 : CacheDecode -> Prop => *)
(*           (fun P6 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P6 cd -> P6 (addD cd b)) P5 /\ *)
(*           (fun P6 : CacheDecode -> Prop => *)
(*            (fun P7 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P7 cd -> P7 (addD cd b)) P6 /\ *)
(*            (fun P7 : CacheDecode -> Prop => *)
(*             (fun P8 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P8 cd -> P8 (addD cd b)) P7 /\ *)
(*             (fun P8 : CacheDecode -> Prop => *)
(*              (fun P9 : CacheDecode -> Prop => forall (b : nat) (cd : CacheDecode), P9 cd -> P9 (..)) P8 /\ *)
(*              (fun P9 : CacheDecode -> Prop => (.. => ..) P9 /\ (.. => ..) P9) P8) P7) P6) P5) P4) P3) P2) P1) P) *)
(*       P0 /\ *)
(*     ?6529 P0 /\ *)
(*     (forall (b : ByteString) (ctx u : ()) (b' : ByteString) (ctx' : ()), *)
(*      decode_IPChecksum b ctx = Some (u, b', ctx') -> P0 ctx -> P0 ctx')) *)
(* subgoal 7 (ID 6338) is: *)
(*  (fun (bin : ByteString) (env : CacheDecode) => *)
(*   if IPChecksum_Valid_dec (IPv4_Packet_formatd_measure bin) bin *)
(*   then *)
(*    `(proj, rest, env') <- (fun (bin0 : ByteString) (env0 : CacheDecode) => *)
(*                            `(a, rest, env') <- decode_word bin0 env0; *)
(*                            (if DecideableEnsembles.A_eq_dec a (natToWord 4 4) *)
(*                             then *)
(*                              (fun (bin1 : ByteString) (env1 : CacheDecode) => *)
(*                               `(proj, rest0, env'0) <-  *)
(*                               decode_nat 4 bin1 env1; *)
(*                               (fun (proj0 : nat) (bin2 : ByteString) (env2 : CacheDecode) => *)
(*                                `(a0, rest1, env'1) <-  *)
(*                                decode_unused_word 8 bin2 env2; *)
(*                                (if DecideableEnsembles.A_eq_dec a0 () *)
(*                                 then *)
(*                                  (fun (bin3 : ByteString) (env3 : CacheDecode) => *)
(*                                   `(proj1, rest2, env'2) <-  *)
(*                                   decode_word bin3 env3; *)
(*                                   (fun (proj2 : word 16) (bin4 : ByteString) (env4 : CacheDecode) => *)
(*                                    `(proj3, rest3, env'3) <-  *)
(*                                    decode_word bin4 env4; *)
(*                                    (fun (proj4 : word 16) (bin5 : ByteString) (env5 : CacheDecode) => *)
(*                                     `(a1, rest4, env'4) <-  *)
(*                                     decode_unused_word 1 bin5 env5; *)
(*                                     (if DecideableEnsembles.A_eq_dec a1 () *)
(*                                      then *)
(*                                       (fun (bin6 : ByteString) (env6 : CacheDecode) => *)
(*                                        `(proj5, rest5, env'5) <-  *)
(*                                        decode_bool bin6 env6; *)
(*                                        (.. => ..) proj5 rest5 env'5) rest4 env'4 *)
(*                                      else None)) proj3 rest3 env'3) proj1 rest2 env'2) rest1 env'1 *)
(*                                 else None)) proj rest0 env'0) rest env' *)
(*                             else None)) bin env; *)
(*    `(_, rest', env'0) <- decode_IPChecksum rest env'; *)
(*    ?6507 proj rest' env'0 *)
(*   else None) b cd = ?6324 b cd *)
(* subgoal 8 (ID 6335) is: *)
(*  DecodeMEquivAlignedDecodeM ?6324 ?6325 *)

(* (dependent evars: ?6321 using , ?6322 using , ?6323 using ?6506 ?6493 ?6492 ?6491 , ?6324 open, ?6325 open, ?6326 open, ?6327 using ?6529 ?6528 , ?6339 using , ?6486 using ?6492 , ?6491 using , ?6492 using ?6498 , ?6493 using ?8533 ?8532 ?8531 ?8530 ?8529 ?8528 , ?6498 using ?6572 ?6571 , ?6505 using , ?6506 using ?6507 , ?6507 open, ?6508 using ?6528 , ?6509 using ?6529 , ?6510 using ?6570 ?6569 ?6568 ?6567 ?6566 , ?6511 using ?8535 ?6966 , ?6512 open, ?6513 using ?6542 ?6498 , ?6514 using ?7035 ?7034 , ?6515 using ?8103 ?8102 , ?6528 using ?8525 ?8524 , ?6529 open, ?6536 using ?6542 , ?6542 using ?6594 ?6572 , ?6561 using ?6566 , ?6562 using ?6567 , ?6566 using ?6571 , ?6567 using ?6572 , ?6568 using , ?6569 using , ?6570 using ?6637 ?6636 ?6635 ?6634 ?6633 , ?6571 using , ?6572 using ?6639 ?6638 , ?6573 using , ?6574 using ?6594 , ?6594 using ?6609 ?6572 , ?6603 using ?6609 , ?6609 using ?6661 ?6639 , ?6628 using ?6633 , ?6629 using ?6634 , ?6633 using ?6638 , ?6634 using ?6639 , ?6635 using , ?6636 using , ?6637 using ?6689 ?6688 ?6687 ?6686 ?6685 , ?6638 using , ?6639 using ?6691 ?6690 , ?6640 using , ?6641 using ?6661 , ?6661 using ?6713 ?6691 , ?6680 using ?6685 , ?6681 using ?6686 , ?6685 using ?6690 , ?6686 using ?6691 , ?6687 using , ?6688 using , ?6689 using ?6756 ?6755 ?6754 ?6753 ?6752 , ?6690 using , ?6691 using ?6758 ?6757 , ?6692 using , ?6693 using ?6713 , ?6713 using ?6728 ?6691 , ?6722 using ?6728 , ?6728 using ?6780 ?6758 , ?6747 using ?6752 , ?6748 using ?6753 , ?6752 using ?6757 , ?6753 using ?6758 , ?6754 using , ?6755 using , ?6756 using ?6808 ?6807 ?6806 ?6805 ?6804 , ?6757 using , ?6758 using ?6810 ?6809 , ?6759 using , ?6760 using ?6780 , ?6780 using ?6832 ?6810 , ?6799 using ?6804 , ?6800 using ?6805 , ?6804 using ?6809 , ?6805 using ?6810 , ?6806 using , ?6807 using , ?6808 using ?6860 ?6859 ?6858 ?6857 ?6856 , ?6809 using , ?6810 using ?6862 ?6861 , ?6811 using , ?6812 using ?6832 , ?6832 using ?6884 ?6862 , ?6851 using ?6856 , ?6852 using ?6857 , ?6856 using ?6861 , ?6857 using ?6862 , ?6858 using , ?6859 using , ?6860 using ?6912 ?6911 ?6910 ?6909 ?6908 , ?6861 using , ?6862 using ?6914 ?6913 , ?6863 using , ?6864 using ?6884 , ?6884 using ?6936 ?6914 , ?6903 using ?6908 , ?6904 using ?6909 , ?6908 using ?6913 , ?6909 using ?6914 , ?6910 using , ?6911 using , ?6912 using ?6964 ?6963 ?6962 ?6961 ?6960 , ?6913 using , ?6914 using ?6966 ?6965 , ?6915 using , ?6916 using ?6936 , ?6936 using ?6988 ?6966 , ?6955 using ?6960 , ?6956 using ?6961 , ?6960 using ?6965 , ?6961 using ?6966 , ?6962 using , ?6963 using , ?6964 open, ?6965 using , ?6966 open, ?6967 using , ?6968 using ?6988 , ?6988 using ?6966 , ?7034 using , ?7035 using ?7128 ?7127 , ?7127 using , ?7128 using ?7221 ?7220 , ?7220 using , ?7221 using ?7305 ?7304 , ?7304 using , ?7305 using ?7398 ?7397 , ?7397 using , ?7398 using ?7491 ?7490 , ?7490 using , ?7491 using ?7575 ?7574 , ?7574 using , ?7575 using ?7663 ?7662 , ?7662 using , ?7663 using ?7751 ?7750 , ?7750 using , ?7751 using ?7844 ?7843 , ?7843 using , ?7844 using ?7937 ?7936 , ?7936 using , ?7937 using , ?8102 using , ?8103 using ?8196 ?8195 , ?8195 using , ?8196 using ?8289 ?8288 , ?8288 using ?8365 , ?8289 using , ?8354 using ?8364 ?8363 ?8362 , ?8355 using ?8362 , ?8362 using , ?8363 using , ?8364 using ?8365 , ?8365 using , ?8516 using ?8530 , ?8517 using ?8529 , ?8518 using ?8528 , ?8520 using , ?8524 using , ?8525 using ?8834 ?8833 , ?8528 using , ?8529 using , ?8530 using ?6966 , ?8531 using ?8689 ?8688 ?8687 ?8686 ?8685 ?8684 , ?8532 using , ?8533 using ?8841 ?8840 ?8839 ?8838 ?8837 , ?8535 using ?9072 ?6966 , ?8536 using ?8542 , ?8537 using ?8543 , ?8542 using , ?8543 using , ?8678 using ?8685 , ?8679 using ?8686 , ?8681 using ?8688 , ?8684 using , ?8685 using , ?8686 using , ?8687 using , ?8688 using , ?8689 using , ?8826 using ?8839 , ?8827 using ?8838 , ?8828 using ?8837 , ?8829 using , ?8833 using , ?8834 using ?9159 ?9158 , ?8837 using , ?8838 using , ?8839 using ?6966 , ?8840 using , ?8841 using ?9169 ?9168 ?9167 ?9166 ?9165 ?9164 ?9163 , ?8842 using ?8848 , ?8843 using ?8849 , ?8848 using , ?8849 using , ?9067 using ?9072 , ?9072 open, ?9150 using ?9165 , ?9151 using ?9164 , ?9152 using ?9163 , ?9154 using , ?9158 using , ?9159 using ?9442 ?9441 , ?9163 using , ?9164 using , ?9165 using ?6966 , ?9166 using , ?9167 using , ?9168 using , ?9169 using ?9449 ?9448 ?9447 ?9446 ?9445 , ?9170 using ?9176 , ?9171 using ?9177 , ?9176 using , ?9177 using , ?9434 using ?9447 , ?9435 using ?9446 , ?9436 using ?9445 , ?9437 using , ?9441 using , ?9442 using ?9755 ?9754 , ?9445 using , ?9446 using , ?9447 using ?6966 , ?9448 using ?9603 ?9602 ?9601 ?9600 ?9599 ?9598 , ?9449 using ?9762 ?9761 ?9760 ?9759 ?9758 , ?9450 using ?9456 , ?9451 using ?9457 , ?9456 using , ?9457 using , ?9592 using ?9599 , ?9593 using ?9600 , ?9595 using ?9602 , ?9598 using , ?9599 using , ?9600 using , ?9601 using , ?9602 using , ?9603 using , ?9747 using ?9760 , ?9748 using ?9759 , ?9749 using ?9758 , ?9750 using , ?9754 using , ?9755 using ?10051 ?10050 , ?9758 using , ?9759 using , ?9760 using ?6966 , ?9761 using ?9916 ?9915 ?9914 ?9913 ?9912 ?9911 , ?9762 using ?10061 ?10060 ?10059 ?10058 ?10057 ?10056 ?10055 , ?9763 using ?9769 , ?9764 using ?9770 , ?9769 using , ?9770 using , ?9905 using ?9912 , ?9906 using ?9913 , ?9908 using ?9915 , ?9911 using , ?9912 using , ?9913 using , ?9914 using , ?9915 using , ?9916 using , ?10042 using ?10057 , ?10043 using ?10056 , ?10044 using ?10055 , ?10046 using , ?10050 using , ?10051 using ?10334 ?10333 , ?10055 using , ?10056 using , ?10057 using ?6966 , ?10058 using , ?10059 using , ?10060 using , ?10061 using ?10341 ?10340 ?10339 ?10338 ?10337 , ?10062 using ?10068 , ?10063 using ?10069 , ?10068 using , ?10069 using , ?10326 using ?10339 , ?10327 using ?10338 , ?10328 using ?10337 , ?10329 using , ?10333 using , ?10334 using ?10627 ?10626 , ?10337 using , ?10338 using , ?10339 using ?6966 , ?10340 using ?10475 ?10474 ?10473 ?10472 ?10471 , ?10341 using ?10634 ?10633 ?10632 ?10631 ?10630 , ?10342 using ?10348 , ?10343 using ?10349 , ?10348 using , ?10349 using , ?10465 using ?10471 , ?10466 using ?10472 , ?10468 using ?10474 , ?10471 using , ?10472 using , ?10473 using , ?10474 using , ?10475 using , ?10619 using ?10632 , ?10620 using ?10631 , ?10621 using ?10630 , ?10622 using , ?10626 using , ?10627 using ?10920 ?10919 , ?10630 using , ?10631 using , ?10632 using ?6966 , ?10633 using ?10768 ?10767 ?10766 ?10765 ?10764 , ?10634 using ?10927 ?10926 ?10925 ?10924 ?10923 , ?10635 using ?10641 , ?10636 using ?10642 , ?10641 using , ?10642 using , ?10758 using ?10764 , ?10759 using ?10765 , ?10761 using ?10767 , ?10764 using , ?10765 using , ?10766 using , ?10767 using , ?10768 using , ?10912 using ?10925 , ?10913 using ?10924 , ?10914 using ?10923 , ?10915 using , ?10919 using , ?10920 using ?11233 ?11232 , ?10923 using , ?10924 using , ?10925 using ?6966 , ?10926 using ?11081 ?11080 ?11079 ?11078 ?11077 ?11076 , ?10927 using ?11240 ?11239 ?11238 ?11237 ?11236 , ?10928 using ?10934 , ?10929 using ?10935 , ?10934 using , ?10935 using , ?11070 using ?11077 , ?11071 using ?11078 , ?11073 using ?11080 , ?11076 using , ?11077 using , ?11078 using , ?11079 using , ?11080 using , ?11081 using , ?11225 using ?11238 , ?11226 using ?11237 , ?11227 using ?11236 , ?11228 using , ?11232 using , ?11233 using ?11546 ?11545 , ?11236 using , ?11237 using , ?11238 using ?6966 , ?11239 using ?11394 ?11393 ?11392 ?11391 ?11390 ?11389 , ?11240 using ?11553 ?11552 ?11551 ?11550 ?11549 , ?11241 using ?11247 , ?11242 using ?11248 , ?11247 using , ?11248 using , ?11383 using ?11390 , ?11384 using ?11391 , ?11386 using ?11393 , ?11389 using , ?11390 using , ?11391 using , ?11392 using , ?11393 using , ?11394 using , ?11538 using ?11551 , ?11539 using ?11550 , ?11540 using ?11549 , ?11541 using , ?11545 using , ?11546 open, ?11549 using , ?11550 using , ?11551 using ?6966 , ?11552 using ?11688 ?11687 ?11686 ?11685 ?11684 , ?11553 using ?13671 ?13670 ?13669 ?13668 ?13667 , ?11554 using ?11560 , ?11555 using ?11561 , ?11560 using , ?11561 using , ?11678 using ?11684 , ?11679 using ?11685 , ?11681 using ?11687 , ?11684 using , ?11685 using , ?11686 using , ?11687 using , ?11688 using , ?13662 using ?13668 , ?13667 using , ?13668 using ?6966 , ?13669 using , ?13670 open, ?13671 open,) *)
