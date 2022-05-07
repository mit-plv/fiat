Require Import Coq.Strings.String.
Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Delimiter.

Section String.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Variable decode_close : DecodeM (unit * B) B.

  Definition decode_string_with_term
             (b : B) (cd : CacheDecode)
    : option (string * B * CacheDecode).
  Admitted.

  Variable format_close : FormatM unit B.
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable decode_close_OK :
    CorrectDecoder monoid (fun _ => True) (fun _ => True)
        eq format_close
        decode_close
        A_cache_inv
        format_close.


  Axiom decode_string_with_term_inv : string -> Prop.
  Theorem string_decode_with_term_correct
    : CorrectDecoder monoid
        decode_string_with_term_inv
        decode_string_with_term_inv
        eq
        (format_with_term format_close format_string)
        (decode_string_with_term)
        A_cache_inv
        (format_with_term format_close format_string).
  Proof.
  Admitted.

End String.

Axiom decode_string_with_term_inv_axiom : forall s, decode_string_with_term_inv s.

#[export]
Hint Extern 4 (decode_string_with_term_inv _) =>
  apply decode_string_with_term_inv_axiom
  : data_inv_hints.

#[export]
Hint Extern 1 (has_prop_for (format_with_term _ format_string) CorrectDecoder) =>
  exact string_decode_with_term_correct : typeclass_instances.
