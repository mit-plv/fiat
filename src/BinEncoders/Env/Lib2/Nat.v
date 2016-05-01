Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.Word.
Require Import
        Bedrock.Word.

Section Nat.
  Variable sz : nat.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnit transformer bool}.

  Definition encode_nat (n : nat) (ce : CacheEncode) : B * CacheEncode :=
    encode_word (natToWord sz n) ce.

  Definition decode_nat (b : B) (cd : CacheDecode) : nat * B * CacheDecode :=
    let (bundle, cd) := decode_word (sz:=sz) b cd in
    let (w, b) := bundle in
        (wordToNat w, b, cd).

  Local Open Scope nat.
  Theorem Nat_decode_correct :
    encode_decode_correct cache transformer (fun n => n < pow2 sz) encode_nat decode_nat.
  Proof.
    unfold encode_decode_correct, encode_nat, decode_nat.
    intros env env' xenv xenv' n n' bin' ext ext' Eeq Ppred Penc Pdec.
    destruct (decode_word (transform bin' ext) env') as [[? ?] ?] eqn: ?.
    inversion Pdec; subst; clear Pdec.
    pose proof (Word_decode_correct env env' xenv xenv' (natToWord sz n) w
                  bin' ext ext' Eeq I Penc Heqp).
    intuition eauto.
    rewrite <- H.
    destruct (wordToNat_natToWord' sz n).
    assert (x = 0).
    { destruct x; eauto.
      rewrite <- H1 in Ppred. exfalso. simpl in Ppred.
      clear - Ppred.
      replace (wordToNat (natToWord sz n) + (pow2 sz + x * pow2 sz)) with
              (pow2 sz + (wordToNat (natToWord sz n) + x * pow2 sz)) in Ppred by omega.
      remember (wordToNat (natToWord sz n) + x * pow2 sz) as n'; clear Heqn'.
      omega. }
    rewrite H3 in H1. simpl in H1. rewrite <- plus_n_O in H1. rewrite H1. reflexivity.
  Qed.
End Nat.