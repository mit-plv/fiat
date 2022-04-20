Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.WordOpt.
Require Import
        Bedrock.Word
        Coq.ZArith.ZArith
        Coq.Strings.Ascii
        Coq.Numbers.BinNums
        Coq.NArith.BinNat.

Section Ascii.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.
  Context {monoidfix : QueueMonoidOptFix monoidUnit}.

  Definition format_ascii (c : ascii) (ce : CacheFormat)
    : Comp (B * CacheFormat) :=
    format_word (NToWord 8 (N_of_ascii c)) ce.

  Definition encode_ascii (c : ascii) (ce : CacheFormat)
    : B * CacheFormat :=
    encode_word (NToWord 8 (N_of_ascii c)) ce.

  Definition decode_ascii (b : B) (cd : CacheDecode) : option (ascii * B * CacheDecode) :=
    `(n, b, cd) <- decode_word (sz:=8) b cd;
      Some (ascii_of_N (wordToN n), b, cd).

  Local Open Scope nat.
  Theorem Ascii_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : forall b cd, P cd -> P (addD cd b))
    :
      CorrectDecoder monoid (fun n => True)
                     (fun n => True)
                     eq
                     format_ascii decode_ascii P
                     format_ascii.
  Proof.
    apply_bijection_rule with (fun n => ascii_of_N (wordToN n));
      intuition eauto using Word_decode_correct.

    rewrite NToWord_nat, wordToN_nat, wordToNat_natToWord_idempotent,
      Nnat.N2Nat.id, ascii_N_embedding; eauto.
    rewrite Nnat.N2Nat.id.
    clear.
    assert (N.lt (N_of_ascii s) 256).
    induction s; repeat (match goal with
                         | B : bool |- _ => destruct B
                         end); simpl; unfold N.lt; eauto.
    eauto.
    rewrite N_ascii_embedding, NToWord_nat, wordToN_nat, Nnat.Nat2N.id, natToWord_wordToNat; eauto.
    rewrite wordToN_nat. eapply Nomega.Nlt_in.
    rewrite Nnat.Nat2N.id. apply wordToNat_bound.

    derive_decoder_equiv.
  Qed.

  Lemma ascii_decode_lt
    : forall (b3 : B) (cd0 : CacheDecode) (a : ascii) (b' : B) (cd' : CacheDecode),
      decode_ascii b3 cd0 = Some (a, b', cd') -> lt_B b' b3.
  Proof.
    unfold decode_ascii; intros.
    destruct (WordOpt.decode_word b3 cd0) as [ [ [? ?] ?] | ] eqn: ? ;
      simpl in *; try discriminate.
    apply WordOpt.decode_word_lt in Heqo.
    injections; eauto.
  Qed.

  Lemma ascii_decode_le :
    forall (b : B) (cd : CacheDecode) (a : ascii) (b' : B) (cd' : CacheDecode),
      decode_ascii b cd = Some (a, b', cd') -> le_B b' b.
  Proof.
    unfold decode_ascii, DecodeBindOpt2; intros.
    destruct (decode_word b cd) as [ [ [? ? ] ?] | ] eqn: decode_b; simpl in H;
      try discriminate; injections.
    eauto using decode_word_le.
  Qed.

  Definition ascii_B_measure := (8 * B_measure_fix).

  Lemma format_ascii_measure
    : forall (a : ascii) ce b ce',
      format_ascii a ce ∋ (b, ce') ->
      bin_measure b = ascii_B_measure.
  Proof.
    eauto using format_word_measure.
  Qed.

  Lemma decode_ascii_measure
    : forall (a : ascii) b cd b' cd',
      decode_ascii b cd = Some (a, b', cd') ->
      bin_measure b = ascii_B_measure + bin_measure b'.
  Proof.
    unfold decode_ascii.
    intros * H.
    destruct decode_word as [[[??]?]|] eqn:Hd; try discriminate.
    simpl in H. injections.
    eauto using decode_word_measure_some.
  Qed.

  Lemma ascii_B_measure_gt_0 : 0 < ascii_B_measure.
  Proof.
    apply word_B_measure_gt_0.
    lia.
  Qed.

  Lemma ascii_B_measure_neq_0 : ascii_B_measure <> 0.
  Proof.
    pose proof ascii_B_measure_gt_0.
    lia.
  Qed.

  Lemma ascii_B_measure_div_add n :
    (ascii_B_measure + n) / ascii_B_measure = S (n / ascii_B_measure).
  Proof.
    assert (ascii_B_measure = 1 * ascii_B_measure) by lia.
    rewrite H at 1.
    rewrite Nat.div_add_l.
    reflexivity.
    apply ascii_B_measure_neq_0.
  Qed.

  Lemma format_ascii_det a : forall ce1 ce1' ce2 ce2' t1 t2,
    format_ascii a ce1 ∋ (t1, ce1') ->
    format_ascii a ce2 ∋ (t2, ce2') ->
    t1 = t2.
  Proof.
    eapply format_word_det.
  Qed.

  Lemma decode_ascii_cache_nonint t a t' cd1 cd1' cd2 :
    decode_ascii t cd1 = Some (a, t', cd1') ->
    exists cd2', decode_ascii t cd2 = Some (a, t', cd2').
  Proof.
    unfold decode_ascii. intros.
    destruct decode_word as [ [[??]?] |] eqn:Hd; simpl in *; injections;
      try discriminate.
    eapply decode_word_cache_nonint in Hd.
    destruct Hd as [? Hd].
    rewrite Hd.
    simpl. eauto.
  Qed.

  Lemma decode_format_ascii a t ce ce' ext cd :
      format_ascii a ce ∋ (t, ce') ->
      exists cd', decode_ascii (mappend t ext) cd = Some (a, ext, cd').
  Proof.
    unfold format_ascii, decode_ascii.
    intros H. eapply decode_format_word in H. destruct H.
    rewrite H. simpl. eexists. repeat f_equal.
    rewrite NToWord_nat, wordToN_nat, wordToNat_natToWord_idempotent,
      Nnat.N2Nat.id, ascii_N_embedding; eauto.
    rewrite Nnat.N2Nat.id. eapply N_ascii_bounded.
  Qed.

End Ascii.
