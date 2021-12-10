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
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Bedrock.Word.

Section AlignedList.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Variable addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).

  Definition asciiToWord (a : ascii) : word 8 :=
    match a with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO)))))))
    end.

  Fixpoint AlignedEncodeString'
           (sz : nat)
           v
           idx
           (s : string)
           env
    : option (ByteBuffer.t sz * nat * CacheFormat) :=
      match s with
      | EmptyString => if Coq.Init.Nat.ltb idx (S sz) then @ReturnAlignedEncodeM _ string sz v idx EmptyString env else None
      | String a s' => Ifopt (SetCurrentBytes (sz := 1) v idx (asciiToWord a) env) as a' Then
                                                                AlignedEncodeString' sz (fst (fst a'))
                                                              (snd (fst a'))
                                                              s' (snd a')
                                                              Else None
    end.

  Lemma asciiToWord_eq :
    forall a,
      (NToWord 8 (N_of_ascii a)) = asciiToWord a.
  Proof.
    destruct a; simpl.
    destruct b; destruct b0; destruct b1; destruct b2;
      destruct b3; destruct b4; destruct b5; destruct b6;
      simpl; eauto.
  Qed.

  Definition AlignedEncodeString
    : forall sz, AlignedEncodeM (S := string) sz := AlignedEncodeString'.

  Lemma CorrectAlignedEncoderForFormatString
    : CorrectAlignedEncoder format_string AlignedEncodeString.
  Proof.
    unfold CorrectAlignedEncoder; intros.
    eexists (fix EncodeString (s : string) env :=
               match s with
               | EmptyString => Some (mempty, env)
               | String a s' => `(t1, env') <- Some (WordOpt.encode_word (asciiToWord a) env);
                             `(t2, env'') <- EncodeString s' env';
                             Some (mappend t1 t2, env'')
               end); split; [ split | split ].
    - revert env; induction s; intros; simpl; eauto.
      + injections; reflexivity.
      + simpl in H.
        unfold Bind2.
        unfold format_ascii.
        unfold WordOpt.format_word; simpl.
        destruct ((fix EncodeString (s : string) (env : CacheFormat) {struct s} :
                            option (ByteString * CacheFormat) :=
                          match s with
                          | ""%string => Some (ByteString_id, env)
                          | String a s' =>
                              `(t2, env'') <- EncodeString s' (addE env 8);
                              Some
                                (ByteString_enqueue_ByteString
                                   (WordOpt.encode_word' 8 (asciiToWord a) ByteString_id) t2, env'')
                          end)) eqn: ?; simpl in H; try discriminate.
        destruct p; injections.
        rewrite refineEquiv_bind_unit, IHs, refineEquiv_bind_unit; eauto.
        simpl; rewrite asciiToWord_eq.
        reflexivity.
    - revert env; induction s; intros; simpl; eauto; try discriminate.
      simpl in H.
      destruct ((fix EncodeString (s : string) (env : CacheFormat) {struct s} :
                            option (ByteString * CacheFormat) :=
                          match s with
                          | ""%string => Some (ByteString_id, env)
                          | String a s' =>
                              `(t2, env'') <- EncodeString s' (addE env 8);
                              Some
                                (ByteString_enqueue_ByteString
                                   (WordOpt.encode_word' 8 (asciiToWord a) ByteString_id) t2, env'')
                          end)) eqn: ?; simpl in H; try discriminate.
      destruct p; injections; try discriminate.
      unfold Bind2.
      unfold format_ascii.
      intro; computes_to_inv.
      unfold WordOpt.format_word in H0; computes_to_inv; subst.
      eapply IHs; eauto.
    - induction s; intros; simpl; eauto.
      + injections; reflexivity.
      + simpl in *.
        destruct ((fix EncodeString (s : string) (env : CacheFormat) {struct s} :
                     option (ByteString * CacheFormat) :=
                     match s with
                     | ""%string => Some (ByteString_id, env)
                     | String a s' =>
                       `(t2, env'') <- EncodeString s' (addE env 8);
                       Some
                         (ByteString_enqueue_ByteString
                            (WordOpt.encode_word' 8 (asciiToWord a) ByteString_id) t2, env'')
                     end)) eqn: ?; simpl in H; try discriminate.
        destruct p; injections; try discriminate.
        eapply IHs in Heqo.
        erewrite padding_ByteString_enqueue_ByteString, Heqo.
        destruct a; reflexivity.
    - unfold EncodeMEquivAlignedEncodeM; intros.
      generalize (le_refl (String.length s)); remember (String.length s) eqn: s_eq; rewrite s_eq at 1; clear s_eq.
      revert s env idx. induction n; intros ? ? ? le_s.
      + destruct s; simpl in le_s; try solve [inversion le_s].
        repeat apply conj; intros.
        * injections; simpl in v; pattern v; apply case0; simpl.
          setoid_rewrite (proj2 (PeanoNat.Nat.ltb_lt idx (S idx + m))); try lia.
          eexists _; split.
          revert v1; rewrite <- (plus_n_O idx); intro; reflexivity.
          pose proof mempty_left as H'; simpl in H'; rewrite H', build_aligned_ByteString_append;
            reflexivity.
        * injections; rewrite length_ByteString_ByteString_id in H0.
          unfold AlignedEncodeString; simpl.
          destruct (NPeano.Nat.ltb idx (S numBytes')) eqn: ?; eauto.
          apply PeanoNat.Nat.ltb_lt in Heqb; lia.
        * injections; simpl in H0; congruence.
        * discriminate.
      + destruct s; simpl in le_s; try solve [inversion le_s].
        * repeat apply conj; intros.
          -- injections; simpl in v; pattern v; apply case0; simpl.
             setoid_rewrite (proj2 (PeanoNat.Nat.ltb_lt idx (S idx + m))); try Lia.lia.
             eexists _; split.
             revert v1; rewrite <- (plus_n_O idx); intro; reflexivity.
             pose proof mempty_left as H'; simpl in H'; rewrite H', build_aligned_ByteString_append;
               reflexivity.
          -- injections; rewrite length_ByteString_ByteString_id in H0.
             unfold AlignedEncodeString; simpl.
             destruct (NPeano.Nat.ltb idx (S numBytes')) eqn: ?; eauto.
             apply PeanoNat.Nat.ltb_lt in Heqb; lia.
          -- injections; simpl in H0; congruence.
          -- discriminate.
        * apply le_S_n in le_s.
          intuition.
          simpl in H.
          -- destruct ((fix EncodeString (s : string) (env : CacheFormat) {struct s} :
                          option (ByteString * CacheFormat) :=
                          match s with
                          | ""%string => Some (ByteString_id, env)
                          | String a s' =>
                            `(t2, env'') <- EncodeString s' (addE env 8);
                            Some
                              (ByteString_enqueue_ByteString
                                 (WordOpt.encode_word' 8 (asciiToWord a) ByteString_id) t2, env'')
                          end)) eqn: ?; simpl in H; try discriminate.
             destruct p; injections; try discriminate.
             simpl in *.
             eapply IHn in le_s.
             intuition.
             eapply H in Heqo.
             destruct Heqo; intuition.
             eexists _.
             intuition.
             (*unfold SetCurrentByte; simpl.
             simpl.


             simpl in H2.
          eapply H.
          assert ((forall (s : A * {As : list A & le (length As) n} ) (env : CacheFormat) (t : ByteString) (env' : CacheFormat),
                      (projT1 X ∘ fst) s env = Some (t, env') -> padding t = 0)) as H'.
          { destruct X; clear IHn; simpl in *; intuition eauto. }
          assert (EncodeMEquivAlignedEncodeM (projT1 X ∘ fst)
                                             (fun (sz : nat) (t : ByteBuffer.t sz) (idx : nat)
                                                  (s : A * {As : list A & le (length As) n})
                                                  (env : CacheFormat) => encode_A sz t idx (fst s) env)) as H''.
          { destruct X; clear IHn; simpl in *; intuition eauto.
            unfold EncodeMEquivAlignedEncodeM; intros ? [? ?] ?; unfold Basics.compose; simpl.
            apply H2; eauto. }
          assert (EncodeMEquivAlignedEncodeM (S := A * {As : list A & le (length As) n})
                    ((fix AlignedEncodeList (As : list A)
                          (env : CacheFormat) {struct As} : option (ByteString * CacheFormat) :=
                        match As with
                        | [] => Some (mempty, env)
                        | a :: As' => `(t1, env') <- projT1 X a env;
                                      `(t2, env'') <- AlignedEncodeList As' env';
                                      Some (mappend t1 t2, env'')
                        end) ∘ (@projT1 _ _) ∘ snd )
                    (fun (sz : nat) (t : ByteBuffer.t sz) (idx : nat)
                         (s : A * {As : list A & le (length As) n}) (env : CacheFormat) =>
                       AlignedEncodeList encode_A sz t idx (projT1 (snd s)) env)) as H'''.
          { unfold EncodeMEquivAlignedEncodeM; intros ? [? [? ?] ] ?; simpl; eauto. }
          apply le_S_n in le_s.
        pose proof (Append_EncodeMEquivAlignedEncodeM _
                                                      _
                                                      _
                                                      _
                                                      H' H'' H''' env (a, existT _ s le_s) idx); clear H' H'' H'''.
        intuition.
  Qed. *)
  Admitted.

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

  Fixpoint StringAlignedDecodeM {m}
           (term_char : word 8)
           (n : nat)
    : AlignedDecodeM string m :=
    match n with
    | 0 => ThrowAlignedDecodeM
    | S n' => BindAlignedDecodeM GetCurrentByte
                                 (fun c => if (weqb c term_char)
                                           then ReturnAlignedDecodeM EmptyString
                                           else BindAlignedDecodeM (StringAlignedDecodeM term_char n')
                                                                   (fun s => ReturnAlignedDecodeM (String (ascii_of_N (wordToN c)) s)))
    end%AlignedDecodeM%list.

  Lemma AlignedDecodeStringM {C : Type}
        (term_word : word 8)
        (term_char : ascii)
    : forall (t : string -> DecodeM (C * _) ByteString)
             (t' : string -> forall {numBytes}, AlignedDecodeM C numBytes),
      ascii_of_N (wordToN term_word) = term_char ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(l, bs, cd') <- decode_string_with_term_char term_char v cd;
                          t l bs cd')
           (fun numBytes => l <- @StringAlignedDecodeM numBytes term_word numBytes;
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

End AlignedList.
