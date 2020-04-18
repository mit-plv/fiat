Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.Word.
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
  Context {transformerUnit : TransformerUnit transformer bool}.

  Definition encode_ascii (c : ascii) (ce : CacheEncode) : B * CacheEncode :=
    encode_word (NToWord 8 (N_of_ascii c)) ce.

  Definition decode_ascii (b : B) (cd : CacheDecode) : ascii * B * CacheDecode :=
    let (bundle, cd) := decode_word (sz:=8) b cd in
    let (n, b) := bundle in
        (ascii_of_N (wordToN n), b, cd).

  Open Local Scope nat.
  Theorem Ascii_decode_correct :
    encode_decode_correct cache transformer (fun n => True) encode_ascii decode_ascii.
  Proof.
    unfold encode_decode_correct, encode_ascii, decode_ascii.
    intros env env' xenv xenv' c c' bin' ext ext' Eeq Ppred Penc Pdec.
    destruct (decode_word (transform bin' ext) env') as [[? ?] ?] eqn: ?.
    inversion Pdec; subst; clear Pdec.
    pose proof (Word_decode_correct env env' xenv xenv' (NToWord 8 (N_of_ascii c)) w
                  bin' ext ext' Eeq I Penc Heqp).
    intuition eauto.
    rewrite <- H. clear.
    rewrite wordToN_nat. rewrite NToWord_nat.
    destruct (wordToNat_natToWord' 8 (BinNat.N.to_nat (N_of_ascii c))).
    assert (x = 0).
    { destruct x; eauto; exfalso.
      remember (wordToNat (natToWord 8 (BinNat.N.to_nat (N_of_ascii c)))) as xx; clear Heqxx.
      replace (xx + S x * pow2 8) with (256 + (xx + x * 256)) in H.
      assert (BinNat.N.to_nat (N_of_ascii c) < 256).
      assert (N.lt (N_of_ascii c) 256).
      clear H. induction c; repeat (match goal with
                                    | B : bool |- _ => destruct B
                                    end); simpl; unfold Nlt; eauto.
      change (256%nat) with (N.to_nat 256).
      apply Nomega.Nlt_out. eauto.
      omega. change (pow2 8) with 256. omega.
    }
    subst. rewrite <- plus_n_O in H. rewrite H. clear H.
    rewrite Nnat.N2Nat.id. rewrite ascii_N_embedding. eauto.
  Qed.
End Ascii.