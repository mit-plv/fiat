Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignWord.

Section AlignedDelimter.
  Context {A : Type}.
  Context {cache : Cache}.

  Open Scope AlignedEncodeM_scope.

  Definition AlignedEncodeDelimiter
             (encode_open : forall sz, AlignedEncodeM (S := unit) sz)
             (encode_close : forall sz, AlignedEncodeM (S := unit) sz)
             (encode_A : forall sz, AlignedEncodeM (S := A) sz)
             sz
    : AlignedEncodeM (S := A) sz :=
    (fun v idx _ => encode_open sz v idx tt) >> encode_A sz >>
      (fun v idx _ => encode_close sz v idx tt).


  Lemma CorrectAlignedEncoderForFormatDelimiter
    format_open encode_open
    format_close encode_close
    format_A encode_A
    (encode_open_OK : CorrectAlignedEncoder format_open encode_open)
    (encode_close_OK : CorrectAlignedEncoder format_close encode_close)
    (encode_A_OK : CorrectAlignedEncoder format_A encode_A)
    (* The following two conditions can be easily discharged when cache is
    empty. *)
    (encode_A_OK1 :
      forall s env tenv' tenv'',
        format_A s env ∋ tenv' ->
        (format_close ◦ constant tt) s (snd tenv') ∋ tenv'' ->
        exists tenv3 tenv4,
          projT1 encode_A_OK s env = Some tenv3 /\
            (format_close ◦ constant tt) s (snd tenv3) ∋ tenv4)
    (encode_A_OK2 :
      forall s env tenv' tenv'',
        (format_open ◦ constant tt) s env ∋ tenv' ->
        format_with_term format_close format_A s (snd tenv') ∋ tenv'' ->
        exists tenv3 tenv4,
          projT1
            (CorrectAlignedEncoderForProjection_Format (constant ()) format_open
               encode_open encode_open_OK) s env = Some tenv3 /\
            format_with_term format_close format_A s (snd tenv3) ∋ tenv4)
    : CorrectAlignedEncoder (S:=A)
        (format_delimiter format_open format_close format_A)
        (AlignedEncodeDelimiter encode_open encode_close encode_A).
  Proof.
    repeat (eapply CorrectAlignedEncoderForThenC;
            [| unshelve instantiate (1:=_)]; eauto);
    eapply CorrectAlignedEncoderForProjection_Format; eauto.
  Qed.

  Open Scope AlignedDecodeM_scope.

  Variable decode_open : DecodeM (unit * ByteString) ByteString.
  Variable decode_close : DecodeM (unit * ByteString) ByteString.
  Variable decode_A : DecodeM (A * ByteString) ByteString.
  Variable decode_open_aligned : forall {m}, AlignedDecodeM unit m.
  Variable decode_close_aligned : forall {m}, AlignedDecodeM unit m.
  Variable decode_A_aligned : forall {m}, AlignedDecodeM A m.
  Variable decode_open_OK :
      DecodeMEquivAlignedDecodeM decode_open (@decode_open_aligned).
  Variable decode_close_OK :
      DecodeMEquivAlignedDecodeM decode_close (@decode_close_aligned).
  Variable decode_A_OK :
      DecodeMEquivAlignedDecodeM decode_A (@decode_A_aligned).

  Definition AlignedDecodeDelimiter
    (decode_with_term_aligned : forall {m}, AlignedDecodeM A m)
    {m}
    : AlignedDecodeM A m :=
    _ <- decode_open_aligned; decode_with_term_aligned.

  Lemma AlignedDecodeDelimiterM {C : Type}
        (decode_with_term : DecodeM (A * _) ByteString)
        (decode_with_term_aligned : forall {m}, AlignedDecodeM A m)
    : forall (t : A -> DecodeM (C * _) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      DecodeMEquivAlignedDecodeM decode_with_term (@decode_with_term_aligned) ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, bs, cd') <- decode_delimiter decode_open
                                         decode_with_term v cd;
                          t a bs cd')
           (fun numBytes => a <- AlignedDecodeDelimiter
                                 (@decode_with_term_aligned);
                            t' a).
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
  Qed.

  Definition AlignedDecodeWithTermSimple {m}
    : AlignedDecodeM A m :=
    a <- decode_A_aligned; _ <- decode_close_aligned; return a.

  Theorem AlignedDecodeWithTermSimpleM'
    : DecodeMEquivAlignedDecodeM
        (decode_with_term_simple decode_close decode_A)
        (fun numBytes => AlignedDecodeWithTermSimple).
  Proof.
    intros; eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    intros; eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    intros. eapply Return_DecodeMEquivAlignedDecodeM.
  Qed.

  Theorem AlignedDecodeWithTermSimpleM {C : Type}
    : forall (t : A -> DecodeM (C * _) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b)) ->
      DecodeMEquivAlignedDecodeM
        (fun v cd => `(a, bs, cd') <- decode_with_term_simple
                                      decode_close decode_A v cd;
                       t a bs cd')
        (fun numBytes => a <- AlignedDecodeWithTermSimple;
                         t' a).
  Proof.
    eauto using Bind_DecodeMEquivAlignedDecodeM, AlignedDecodeWithTermSimpleM'.
  Qed.

  Definition AlignedDecodeDelimiterSimple {m}
    : AlignedDecodeM A m :=
    AlignedDecodeDelimiter (@AlignedDecodeWithTermSimple).

  Theorem AlignedDecodeDelimiterSimpleM {C : Type}
    : forall (t : A -> DecodeM (C * _) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, bs, cd') <- decode_delimiter_simple
                                         decode_open decode_close decode_A v cd;
                          t a bs cd')
           (fun numBytes => a <- AlignedDecodeDelimiterSimple;
                            t' a).
  Proof.
    eauto using AlignedDecodeDelimiterM, AlignedDecodeWithTermSimpleM'.
  Qed.

End AlignedDelimter.
