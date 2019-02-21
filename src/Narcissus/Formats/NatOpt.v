Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Formats.WordOpt.
Require Import
        Coq.omega.Omega
        Bedrock.Word.

Section Nat.
  Variable sz : nat.

  Context {T : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition format_nat (n : nat) (ce : CacheFormat)
    : Comp (T * CacheFormat) :=
    format_word (natToWord sz n) ce.

  Open Scope vector_scope.

  Definition encode_nat (n : nat) (ce : CacheFormat) : T * CacheFormat :=
    encode_word (natToWord sz n) ce.

  Lemma refine_format_nat :
    forall n ce,
      refine (format_nat n ce) (ret (encode_nat n ce)).
  Proof.
    reflexivity.
  Qed.

  Definition decode_nat (b : T) (cd : CacheDecode) : option (nat * T * CacheDecode) :=
    `(w, b, cd) <- decode_word (sz:=sz) b cd;
      Some (wordToNat w, b, cd).

  Local Open Scope nat.
  Theorem Nat_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    : CorrectDecoder monoid (fun n => n < pow2 sz)
                     (fun n => n < pow2 sz)
                     eq format_nat decode_nat P
                     format_nat.
  Proof.
    unfold CorrectDecoder, format_nat, decode_nat.
    split.
    { intros env xenv xenv' n n' ext ? Eeq Ppred Penc.
      destruct (proj1 (Word_decode_correct P_OK) _ _ _ _ _ ext env_OK Eeq I Penc) as [? [? [? xenv_OK] ] ].
      - rewrite H; simpl; eexists _, _; intuition eauto.
        rewrite <- H0.
        rewrite wordToNat_natToWord_idempotent; eauto.
        rewrite <- Npow2_nat in Ppred.
        rewrite <- (Nnat.Nat2N.id n) in Ppred.
        apply Nomega.Nlt_in in Ppred; eauto.
        repeat f_equal.
        destruct (wordToNat_natToWord' sz n).
        assert (x1 = 0).
        { destruct x1; eauto.
          rewrite <- H3 in Ppred. exfalso. simpl in Ppred.
          clear - Ppred.
          replace (wordToNat (natToWord sz n) + (pow2 sz + x1 * pow2 sz)) with
          (pow2 sz + (wordToNat (natToWord sz n) + x1 * pow2 sz)) in Ppred by omega.
          remember (wordToNat (natToWord sz n) + x1 * pow2 sz) as n'; clear Heqn'.
          unfold id in *; omega. }
        rewrite H5 in H3. simpl in H3. rewrite <- plus_n_O in H3.
        congruence.
        }
    { intros env xenv xenv' n n' ext Eeq OK_env Penc.
      destruct (decode_word n' xenv) as [ [ [? ? ] ? ] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      eapply (proj2 (Word_decode_correct P_OK)) in Heqo;
        destruct Heqo; destruct_ex; intuition; subst; eauto.
      unfold format_word in *; computes_to_inv; injections.
      eexists _, _; rewrite natToWord_wordToNat; intuition eauto.
      apply wordToNat_bound.
    }
  Qed.
End Nat.
