Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.AsciiOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Lexeme
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedString.

Require Import
        Coq.Strings.Ascii
        Coq.Strings.String.

Require Import
        Bedrock.Word.

Section AlignedLexeme.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Definition AlignedEncodeLexeme {A}
             (encode_A : forall sz, AlignedEncodeM (S := A) sz)
             sz
    : AlignedEncodeM (S := A) sz := encode_A sz.

  Arguments mempty : simpl never.
  Arguments mappend : simpl never.

  Lemma CorrectAlignedEncoderForFormatLexeme {A}
        format_A
        encode_A
        (encode_A_OK : CorrectAlignedEncoder format_A encode_A)
    : CorrectAlignedEncoder (format_lexeme (A:=A) format_A)
                            encode_A.
  Proof.
    eapply refine_CorrectAlignedEncoder; eauto.
    unfold format_lexeme.
    split.
    - intros [] ?.
      computes_to_econstructor.
      instantiate (1:=(mempty, env)).
      unfold format_space, Compose_Format.
      apply unfold_computes. repeat esplit.
      instantiate (1:=""%string).
      computes_to_econstructor.
      apply unfold_computes. simpl. econstructor.
      computes_to_econstructor; eauto.
      simpl. rewrite mempty_left.
      computes_to_econstructor; eauto.
    - intros H [].
      unfold Bind2.
      intro.
      computes_to_inv. destruct_conjs. simpl in *. injections.
      eapply H. eauto.
  Qed.

  Definition AlignedDecodeSpace {m}
    : AlignedDecodeM unit m :=
    fun v idx cd =>
      Nat.iter (m - idx)
               (fun rec v idx cd =>
                  match AlignedDecodeAscii v idx cd with
                  | Some (a, idx', cd') =>
                      if is_space a
                      then rec v idx' cd'
                      else Some (tt, idx, cd)
                  | None => Some (tt, idx, cd)
                  end)
               (ReturnAlignedDecodeM tt)
               v idx cd.

  (* This definition can be optimized. For example, [AlignedDecodeSpace] always
  returns [Some]. But this version is convenient for proof because we can use
  the combinator lemmas. We may implement a faster version later and show
  equivalence. *)
  Definition AlignedDecodeLexeme {A}
             (decode_A : forall {n}, AlignedDecodeM A n)
             {n}
    : AlignedDecodeM A n :=
    fun v idx cd =>
      match AlignedDecodeSpace v idx cd with
      | Some (_, idx', _) => decode_A v idx' cd
      | None => None
      end.

  Lemma AlignedDecodeSpaceM' :
    DecodeMEquivAlignedDecodeM decode_space
                               (fun numBytes => AlignedDecodeSpace).
  Proof.
    unfold decode_space, AlignedDecodeSpace.
    eapply AlignedDecode_iter; eauto using Return_DecodeMEquivAlignedDecodeM.
    intros * H.
    eapply DecodeMEquivAlignedDecodeM'_trans; intros.
    - eapply Seq_DecodeMEquivAlignedDecodeM_S with
        (reset := fun a => if is_space a then false else true)
        (fcd := fun a cd cd' => if is_space a then cd' else cd)
        (A_decode := decode_ascii)
        (A_decode_aligned := fun _ => AlignedDecodeAscii)
        (t := fun a b cd => if is_space a
                          then rec b cd
                          else Some (tt, b, cd))
        (t' := fun a _ v idx cd => if is_space a
                                 then aligned_rec _ v idx cd
                                 else Some (tt, idx, cd))
        (u := fun b cd => Some (tt, b, cd))
        (u' := fun _ => ReturnAlignedDecodeM tt);
        simpl; intros;
        eauto using Return_DecodeMEquivAlignedDecodeM', AlignedDecodeAscii_S.
      + DecodeMEquivAlignedDecodeM_conv. eapply AlignedDecodeAsciiM'.
      + destruct is_space; intros; injections;
          eauto using Return_DecodeMEquivAlignedDecodeM'.
    - simpl.
      destruct decode_ascii as [[[]] |]; eauto.
      destruct is_space; eauto.
    - simpl; hnf; intros.
      destruct AlignedDecodeAscii as [[[]] |]; eauto.
      destruct is_space; eauto.
  Qed.

  Lemma AlignedDecodeLexemeM' {A}
        (decode_A : DecodeM (A * _) ByteString)
        (decode_A_aligned : forall {n}, AlignedDecodeM A n)
    : DecodeMEquivAlignedDecodeM decode_A (@decode_A_aligned) ->
      DecodeMEquivAlignedDecodeM (decode_lexeme decode_A)
                                 (fun numBytes =>
                                    AlignedDecodeLexeme (@decode_A_aligned)).
  Proof.
    intros Ha.
    unfold decode_lexeme, AlignedDecodeLexeme.
    eapply Seq_DecodeMEquivAlignedDecodeM with
      (reset := fun _ => false)
      (fcd := fun _ cd _ => cd)
      (u := fun _ _ => None)
      (u' := fun _ => ThrowAlignedDecodeM);
      eauto using AlignedDecodeSpaceM', AlignedDecode_Throw.
  Qed.

  Lemma AlignedDecodeLexemeM {A C}
        (decode_A : DecodeM (A * _) ByteString)
        (decode_A_aligned : forall {n}, AlignedDecodeM A n)
    : forall (t : A -> DecodeM (C * _) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      DecodeMEquivAlignedDecodeM decode_A (@decode_A_aligned) ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b)) ->
      DecodeMEquivAlignedDecodeM
        (fun v cd => `(l, bs, cd') <- decode_lexeme decode_A v cd;
         t l bs cd')
        (fun numBytes => l <- AlignedDecodeLexeme (@decode_A_aligned);
         t' l)%AlignedDecodeM%list.
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM;
      eauto using AlignedDecodeLexemeM'.
  Qed.

End AlignedLexeme.
