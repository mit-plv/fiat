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

  Definition decode_string_with_term (close : string)
             (b : B) (cd : CacheDecode)
    : option (string * B * CacheDecode).
  Admitted.

  Theorem string_decode_with_term_correct
          {P : CacheDecode -> Prop}
          (close : string)
    : CorrectDecoder monoid
                     (* TODO *)
                     (fun s => True)
                     (fun s => True)
                     eq
                     (format_with_term format_string close)
                     (decode_string_with_term close)
                     P
                     (format_with_term format_string close).
  Proof.
  Admitted.

End String.
