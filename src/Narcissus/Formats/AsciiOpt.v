Require Import
        Fiat.Narcissus.Common.Specs
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
                              (fun _ _ => True)
                              format_ascii decode_ascii P.
  Proof.
    unfold decode_ascii; split.
    {
      intros env env' xenv c c' ext env_OK Eeq Ppred Ppred_rest Penc.
      destruct (proj1 (Word_decode_correct (sz := 8) P_OK) _ _ _ _ _ ext env_OK Eeq I I Penc) as [? [? [? xenv_OK] ] ].
      rewrite H; simpl.
      eexists; intuition eauto.
      repeat f_equal.
      rewrite wordToN_nat. rewrite NToWord_nat.
      destruct (wordToNat_natToWord' 8 (BinNat.N.to_nat (N_of_ascii c))).
      assert (x0 = 0).
      { destruct x0; eauto; exfalso.
        remember (wordToNat (natToWord 8 (BinNat.N.to_nat (N_of_ascii c)))) as xx; clear Heqxx.
        replace (xx + S x0 * pow2 8) with (256 + (xx + x0 * 256)) in H1.
        assert (BinNat.N.to_nat (N_of_ascii c) < 256).
        assert (N.lt (N_of_ascii c) 256).
        clear H. induction c; repeat (match goal with
                                      | B : bool |- _ => destruct B
                                      end); simpl; unfold Nlt; eauto.
        change (256%nat) with (N.to_nat 256).
        apply Nomega.Nlt_out. eauto.
        omega. change (pow2 8) with 256. omega.
      }
      subst. rewrite <- plus_n_O in H1. rewrite H1. clear H1.
      rewrite Nnat.N2Nat.id. rewrite ascii_N_embedding. eauto.
    }
    { intros env xenv xenv' n n' ext Eeq OK_env' Penc.
      destruct (decode_word n' xenv) as [ [ [? ? ] ? ] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      eapply (proj2 (Word_decode_correct P_OK)) in Heqo; eauto;
        destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst; eauto.
      unfold format_word in *; computes_to_inv; injections.
      repeat eexists; eauto.
      repeat f_equal.
      rewrite N_ascii_embedding.
      rewrite NToWord_nat, wordToN_nat.
      rewrite Nnat.Nat2N.id.
      rewrite natToWord_wordToNat; eauto.
      rewrite wordToN_nat.
      pose proof (wordToNat_bound w).
      simpl in H2.
      eapply Nomega.Nlt_in.
      rewrite Nnat.Nat2N.id.
      eauto.
    }
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
