Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.WordOpt.
Require Import
        Bedrock.Word.

Section Nat.
  Variable sz : nat.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Definition encode_nat_Spec (n : nat) (ce : CacheEncode)
    : Comp (B * CacheEncode) :=
    encode_word_Spec (natToWord sz n) ce.

  Definition encode_nat_Impl (n : nat) (ce : CacheEncode) : B * CacheEncode :=
    encode_word_Impl (natToWord sz n) ce.

  Definition decode_nat (b : B) (cd : CacheDecode) : option (nat * B * CacheDecode) :=
    `(w, b, cd) <- decode_word (sz:=sz) b cd;
      Some (wordToNat w, b, cd).

  Local Open Scope nat.
  Theorem Nat_decode_correct :
    encode_decode_correct_f cache transformer (fun n => n < pow2 sz) encode_nat_Spec decode_nat.
  Proof.
    unfold encode_decode_correct_f, encode_nat_Spec, decode_nat.
    split.
    { intros env xenv xenv' n n' ext Eeq Ppred Penc.
      destruct (proj1 Word_decode_correct _ _ _ _ _ ext Eeq I Penc) as [? [? ?] ].
      - rewrite H; simpl; eexists; intuition eauto.
        repeat f_equal.
        destruct (wordToNat_natToWord' sz n).
        assert (x0 = 0).
        { destruct x0; eauto.
          rewrite <- H1 in Ppred. exfalso. simpl in Ppred.
          clear - Ppred.
          replace (wordToNat (natToWord sz n) + (pow2 sz + x0 * pow2 sz)) with
          (pow2 sz + (wordToNat (natToWord sz n) + x0 * pow2 sz)) in Ppred by omega.
          remember (wordToNat (natToWord sz n) + x0 * pow2 sz) as n'; clear Heqn'.
          omega. }
        rewrite H2 in H1. simpl in H1. rewrite <- plus_n_O in H1. eauto.
        }
    { intros env xenv xenv' n n' ext Eeq Penc.
      destruct (decode_word n' xenv) as [ [ [? ? ] ? ] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      eapply (proj2 Word_decode_correct) in Heqo; destruct_ex;
        intuition; subst; eauto.
      unfold encode_word_Spec in H0; computes_to_inv; injections.
      rewrite natToWord_wordToNat; repeat eexists; eauto.
      apply wordToNat_bound.
    }
  Qed.
End Nat.
