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


  Theorem string_decode_with_term_correct
    : CorrectDecoder monoid
                     (* TODO *)
                     (fun s => True)
                     (fun s => True)
                     eq
                     (format_with_term format_close format_string)
                     (decode_string_with_term)
                     A_cache_inv
                     (format_with_term format_close format_string).
  Proof.
  Admitted.

End String.
