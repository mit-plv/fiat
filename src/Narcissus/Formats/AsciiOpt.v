Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.WordOpt.
Require Import
        Bedrock.Word
        Coq.omega.Omega
        Coq.Strings.Ascii
        Coq.Numbers.BinNums
        Coq.NArith.BinNat.

Section Ascii.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

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

End Ascii.
