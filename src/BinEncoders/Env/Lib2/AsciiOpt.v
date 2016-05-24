Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.WordOpt.
Require Import
        Bedrock.Word
        Coq.Strings.Ascii
        Coq.Numbers.BinNums
        Coq.NArith.BinNat.

Section Ascii.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Definition encode_ascii (c : ascii) (ce : CacheEncode) : B * CacheEncode :=
    encode_word (NToWord 8 (N_of_ascii c)) ce.

  Definition decode_ascii (b : B) (cd : CacheDecode) : option (ascii * B * CacheDecode) :=
    `(n, b, cd) <- decode_word (sz:=8) b cd;
      Some (ascii_of_N (wordToN n), b, cd).

  Open Local Scope nat.
  Theorem Ascii_decode_correct :
    encode_decode_correct_f cache transformer (fun n => True) encode_ascii decode_ascii.
  Proof.
    unfold encode_decode_correct, encode_ascii, decode_ascii.
    intros env env' xenv c c' ext Eeq Ppred Penc.
    destruct (Word_decode_correct _ _ _ _ _ ext Eeq I Penc) as [? [? ?] ].
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
  Qed.
End Ascii.
