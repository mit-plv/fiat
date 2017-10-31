Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.WordOpt.
Require Import
        Bedrock.Word.

Section Nat.
  Variable sz : nat.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition format_nat (n : nat) (ce : CacheFormat)
    : Comp (B * CacheFormat) :=
    format_word (natToWord sz n) ce.

  Definition encode_nat (n : nat) (ce : CacheFormat) : B * CacheFormat :=
    encode_word (natToWord sz n) ce.

  Lemma refine_format_nat :
    forall n ce,
      refine (format_nat n ce) (ret (encode_nat n ce)).
  Proof.
    reflexivity.
  Qed.

  Definition decode_nat (b : B) (cd : CacheDecode) : option (nat * B * CacheDecode) :=
    `(w, b, cd) <- decode_word (sz:=sz) b cd;
      Some (wordToNat w, b, cd).

  Local Open Scope nat.
  Theorem Nat_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    : CorrectDecoder monoid (fun n => n < pow2 sz)
                              (fun _ _ => True) format_nat decode_nat P.
  Proof.
    unfold CorrectDecoder, format_nat, decode_nat.
    split.
    { intros env xenv xenv' n n' ext ? Eeq Ppred Ppred_rest Penc.
      destruct (proj1 (Word_decode_correct P_OK) _ _ _ _ _ ext env_OK Eeq I I Penc) as [? [? [? xenv_OK] ] ].
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
    { intros env xenv xenv' n n' ext Eeq OK_env Penc.
      destruct (decode_word n' xenv) as [ [ [? ? ] ? ] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      eapply (proj2 (Word_decode_correct P_OK)) in Heqo;
        destruct Heqo; destruct_ex; intuition; subst; eauto.
      unfold format_word in *; computes_to_inv; injections.
      eauto.
      rewrite natToWord_wordToNat; repeat eexists; eauto.
      apply wordToNat_bound.
    }
  Qed.
End Nat.
