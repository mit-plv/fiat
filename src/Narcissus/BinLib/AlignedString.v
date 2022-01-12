Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Coq.ZArith.ZArith
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.AsciiOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Bedrock.Word.

Section AlignedString.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Variable addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).
  Variable addE_0 :
    forall (ce : CacheFormat), addE ce 0 = ce.

  (* Definition asciiToWord (a : ascii) : word 8 := *)
  (*   match a with *)
  (*   | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))) *)
  (*   end. *)

  (* Lemma asciiToWord_eq : *)
  (*   forall a, *)
  (*     (NToWord 8 (N_of_ascii a)) = asciiToWord a. *)
  (* Proof. *)
  (*   destruct a; simpl. *)
  (*   destruct b; destruct b0; destruct b1; destruct b2; *)
  (*     destruct b3; destruct b4; destruct b5; destruct b6; *)
  (*     simpl; eauto. *)
  (* Qed. *)

  (* Fixpoint AlignedEncodeString' *)
  (*          (sz : nat) *)
  (*          v *)
  (*          idx *)
  (*          (s : string) *)
  (*          env *)
  (*   : option (ByteBuffer.t sz * nat * CacheFormat) := *)
  (*     match s with *)
  (*     | EmptyString => if Coq.Init.Nat.ltb idx (S sz) then @ReturnAlignedEncodeM _ string sz v idx EmptyString env else None *)
  (*     | String a s' => Ifopt (SetCurrentBytes (sz := 1) v idx (asciiToWord a) env) as a' Then *)
  (*                                                               AlignedEncodeString' sz (fst (fst a')) *)
  (*                                                             (snd (fst a')) *)
  (*                                                             s' (snd a') *)
  (*                                                             Else None *)
  (*   end. *)

  (* Definition AlignedEncodeString *)
  (*   : forall sz, AlignedEncodeM (S := string) sz := AlignedEncodeString'. *)

  (* TODO: the aligned encoder and decoder for string reduce to those for list
  at the moment. We can (and should) write a more optimized (fused) version
  later and show they are equivalent. *)
  Definition list_word_of_string (s : string) : list (word 8) :=
    map (fun a => NToWord 8 (N_of_ascii a)) (list_ascii_of_string s).

  Definition string_of_list_word (l : list (word 8)) : string :=
    string_of_list_ascii (map (fun w => ascii_of_N (wordToN w)) l).

  Definition AlignedEncodeString'
             (sz : nat) v idx (s : string) env
    : option (ByteBuffer.t sz * nat * CacheFormat) :=
    AlignedEncodeList (fun _ => SetCurrentBytes (sz:=1)) sz v idx
                      (list_word_of_string s) env.

  Definition AlignedEncodeString
    : forall sz, AlignedEncodeM (S := string) sz := AlignedEncodeString'.

  Definition AlignedDecodeString {m}
             (n : nat)
    : AlignedDecodeM string m :=
    (l <- ListAlignedDecodeM (fun _ => GetCurrentByte) n;
     return (string_of_list_word l))%AlignedDecodeM.

  Lemma CorrectAlignedEncoderForFormatString
    : CorrectAlignedEncoder format_string AlignedEncodeString.
  Proof.
    eapply CorrectAlignedEncoder_morphism; cycle 1. reflexivity.
    - unfold AlignedEncodeString, AlignedEncodeString'.
      eapply CorrectAlignedEncoderForProjection_Format.
      eapply CorrectAlignedEncoderForFormatList.
      unshelve instantiate (2:=_).
      eapply CorrectAlignedEncoderForFormatNChar; eauto.
      intros; eapply encoder_format_eq_cache_OK; eauto.
      simpl. intros ?????? H1 _ H2.
      unfold format_word in H1. computes_to_inv.
      inversion H1. inversion H2.
      reflexivity.
    - unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format.
      intros s env; split.
      + intros v [?[??]]. subst.
        revert dependent v. revert dependent env.
        induction s; simpl; unfold Bind2; intros; eauto.
        computes_to_inv.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto using eq_ret_compute.
      + intros v ?. rewrite unfold_computes.
        revert dependent v. revert dependent env.
        induction s; simpl; unfold Bind2; intros; eauto.
        repeat esplit; eauto.
        computes_to_inv.
        apply IHs in H'. destruct_conjs.
        inversion H''. subst.
        repeat esplit.
        simpl.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
  Defined.

  Lemma AlignedDecodeStringM'
        (n : nat)
      : DecodeMEquivAlignedDecodeM
          (decode_string n)
          (fun numBytes => AlignedDecodeString n).
  Proof.
    intros.
    unfold AlignedDecodeString.
    eapply DecodeMEquivAlignedDecodeM_trans.
    3: intros; apply AlignedDecodeMEquiv_refl.
    - eapply AlignedDecodeListM.
      apply AlignedDecodeCharM.
      intros; eapply Return_DecodeMEquivAlignedDecodeM.
    - simpl. clear.
      induction n; intros; simpl; eauto.
      unfold decode_ascii.
      rewrite !DecodeBindOpt2_assoc.
      eapply DecodeBindOpt2_under_bind; intros; simpl.
      rewrite <- IHn.
      rewrite !DecodeBindOpt2_assoc.
      eapply DecodeBindOpt2_under_bind; intros; simpl.
      reflexivity.
  Qed.

  Lemma AlignedDecodeStringM {C : Type}
        (n : nat)
    : forall (t : string -> DecodeM (C * _) ByteString)
             (t' : string -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(l, bs, cd') <- decode_string n v cd;
                          t l bs cd')
           (fun numBytes => l <- AlignedDecodeString n;
                            t' l)%AlignedDecodeM.
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto using AlignedDecodeStringM'.
  Qed.


  Lemma CorrectAlignedEncoderForFormatStringTerm
        term_char
    : CorrectAlignedEncoderFor (format_string_with_term_char term_char).
  Proof.
    eexists.
    eapply refine_CorrectAlignedEncoder with (format' := FMapFormat.Projection_Format format_string  (fun s => s ++ String term_char "")%string).
    - split; intros.
      + unfold format_string_with_term_char, FMapFormat.Projection_Format, FMapFormat.Compose_Format.
        intros [? ?] ?.
        rewrite unfold_computes in H; destruct H; intuition; subst; eauto.
      + intros.
        intros ?; eapply H.
        unfold format_string_with_term_char in H0;
          unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format.
        apply unfold_computes; eexists _; eauto.
    - eapply CorrectAlignedEncoderProjection.
      eapply CorrectAlignedEncoderForFormatString.
  Defined.

  Definition AlignedEncoderForFormatStringTerm
             term_char
    :=
      Eval simpl in projT1 (CorrectAlignedEncoderForFormatStringTerm term_char).

  Lemma CorrectAlignedEncoderFormatStringTerm
        term_char
    : CorrectAlignedEncoder (format_string_with_term_char term_char)
                            (AlignedEncoderForFormatStringTerm term_char).
  Proof.
    apply (projT2 (CorrectAlignedEncoderForFormatStringTerm _)).
  Qed.

  Fixpoint StringTermAlignedDecodeM {m}
           (term_char : word 8)
           (n : nat)
    : AlignedDecodeM string m :=
    match n with
    | 0 => ThrowAlignedDecodeM
    | S n' => BindAlignedDecodeM GetCurrentByte
                                 (fun c => if (weqb c term_char)
                                           then ReturnAlignedDecodeM EmptyString
                                           else BindAlignedDecodeM (StringTermAlignedDecodeM term_char n')
                                                                   (fun s => ReturnAlignedDecodeM (String (ascii_of_N (wordToN c)) s)))
    end%AlignedDecodeM%list.

  Lemma AlignedDecodeStringTermCharM {C : Type}
        (term_word : word 8)
        (term_char : ascii)
    : forall (t : string -> DecodeM (C * _) ByteString)
             (t' : string -> forall {numBytes}, AlignedDecodeM C numBytes),
      ascii_of_N (wordToN term_word) = term_char ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(l, bs, cd') <- decode_string_with_term_char term_char v cd;
                          t l bs cd')
           (fun numBytes => l <- @StringTermAlignedDecodeM numBytes term_word numBytes;
           t' l)%AlignedDecodeM%list.
  Proof.
    intros.
    (* unfold DecodeMEquivAlignedDecodeM; intuition.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply ReturnAlignedDecodeM_LeftUnit;
                                                      reflexivity | reflexivity ].
    eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: set_evars; erewrite !DecodeBindOpt2_assoc; subst_evars; higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply BindAlignedDecodeM_assoc;
                                                      reflexivity | higher_order_reflexivity ].
    simpl.
    eapply Bind_DecodeMEquivAlignedDecodeM; intros.
    eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: set_evars; erewrite !DecodeBindOpt2_assoc; subst_evars; higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply BindAlignedDecodeM_assoc;
                                                      reflexivity | higher_order_reflexivity ].
    simpl.
    eapply IHn; eauto.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [eapply ReturnAlignedDecodeM_LeftUnit | higher_order_reflexivity].
    eapply H0. *)
  Admitted.

End AlignedString.
