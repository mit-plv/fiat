Require Import Coq.Strings.String.
Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.Formats.WithTerm.String
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedString.

Section String.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Variable addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).
  Variable addE_0 :
    forall (ce : CacheFormat), addE ce 0 = ce.

  Open Scope AlignedDecodeM_scope.

  Definition AlignedDecodeStringWithTerm {m}
             (close : string)
    : AlignedDecodeM string m.
  Admitted.

  Lemma AlignedDecodeStringWithTermM {C : Type}
        (close : string)
    : forall (t : string -> DecodeM (C * _) ByteString)
             (t' : string -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(s, bs, cd') <- decode_string_with_term close v cd;
                      t s bs cd')
           (fun numBytes => s <- AlignedDecodeStringWithTerm close;
                          t' s).
  Proof.
  Admitted.

End String.
