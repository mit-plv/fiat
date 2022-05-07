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

  Variable decode_close_aligned : forall {m}, AlignedDecodeM unit m.

  Open Scope AlignedDecodeM_scope.

  Definition AlignedDecodeStringWithTerm {m}
    : AlignedDecodeM string m.
  Admitted.

  Variable decode_close : DecodeM (unit * ByteString) ByteString.
  Variable decode_close_OK :
      DecodeMEquivAlignedDecodeM decode_close (@decode_close_aligned).

  Lemma AlignedDecodeStringWithTermM'
    : DecodeMEquivAlignedDecodeM
        (decode_string_with_term decode_close)
        (fun numBytes => AlignedDecodeStringWithTerm).
  Proof.
    Admitted.

  Lemma AlignedDecodeStringWithTermM {C : Type}
    : forall (t : string -> DecodeM (C * _) ByteString)
        (t' : string -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(s, bs, cd') <- decode_string_with_term decode_close v cd;
                      t s bs cd')
           (fun numBytes => s <- AlignedDecodeStringWithTerm;
                          t' s).
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM;
      eauto using AlignedDecodeStringWithTermM'.
  Qed.

End String.

#[export]
Hint Extern 1 (has_prop_for (decode_string_with_term _)
                 (@DecodeMEquivAlignedDecodeM)) =>
  exact AlignedDecodeStringWithTermM' : typeclass_instances.
