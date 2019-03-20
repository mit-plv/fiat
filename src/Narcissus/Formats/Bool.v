Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.BaseFormats.

Unset Implicit Arguments.

Section Bool.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition format_bool (b : bool) (ctx : CacheFormat) :=
    ret (enqueue_opt b mempty, addE ctx 1).

  Definition decode_bool (b : B) (ctx : CacheDecode) : option (bool * B * CacheDecode) :=
    Ifopt dequeue_opt b as decoded Then Some (decoded, addD ctx 1) Else None.

  Theorem bool_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder monoid (fun _ => True)
                     (fun _ => True)
                     eq
                     format_bool decode_bool P format_bool.
  Proof.
    eapply format_decode_correct_EquivFormatAndView with (fun b => format_word (WS b WO)).
    unfold flip, EquivFormat. reflexivity.

    apply_bijection_rule with (whd (sz:=_));
      intuition eauto using Word_decode_correct.
    rewrite <- (natToWord_wordToNat v).
    destruct (wordToNat v) eqn:?; reflexivity.

    unfold decode_word, decode_word'; derive_decoder_equiv.
  Qed.

End Bool.
