Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BaseFormats
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
    apply_bijection_rule;
      intuition eauto using Word_decode_correct, wordToNat_bound, natToWord_wordToNat.
    apply wordToNat_natToWord_idempotent.
    apply Nomega.Nlt_in. rewrite Npow2_nat. rewrite Nnat.Nat2N.id. auto.

    derive_decoder_equiv.
  Qed.
End Nat.
