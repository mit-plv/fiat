Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.NormalizeFormats
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
Open Scope format_scope.
Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

(* Start Example Derivation. *)
Section EthernetPacketDecoder.

  Record EthernetHeader :=
    {Destination : Vector.t (word 8) 6;
     Source : Vector.t (word 8) 6;
     EthType : EnumType ["ARP"; "IP"; "IPV6"; "RARP"]}.

  Definition EtherTypeCodes : Vector.t (word 16) 4 :=
    [WO~0~0~0~0~1~0~0~0~0~0~0~0~0~1~1~0;
     WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0;
     WO~1~0~0~0~0~1~1~0~1~1~0~1~1~1~0~1;
     WO~0~0~0~0~1~0~0~0~0~0~1~1~0~1~0~1
    ].

  Variable packet_len : nat. (* The length of the ethernet packet, *)
  (* which is a parameter to the format and decoder. *)
  Variable packet_len_OK : lt packet_len 1501.

  Definition EthernetHeader_Format
    : FormatM EthernetHeader ByteString :=
    format_Vector format_word ◦ Destination
   ++ format_Vector format_word ◦ Source
   ++ Either
   format_nat 16 ◦ constant packet_len
   ++ format_word ◦ constant WO~0~1~0~1~0~1~0~1
   ++ format_word ◦ constant WO~0~1~0~1~0~1~0~1
   ++ format_word ◦ constant WO~1~1~0~0~0~0~0~0
   ++ format_word ◦ constant wzero 24
   ++ format_enum EtherTypeCodes ◦ EthType
   Or format_enum EtherTypeCodes ◦ EthType.

  Definition EthernetHeader_encoder :
    CorrectAlignedEncoderFor EthernetHeader_Format.
  Proof.
    synthesize_aligned_encoder.
  Defined.

  (* Step Two: Extract the encoder function, and have it start encoding
     at the start of the provided ByteString [v]. *)
  Definition EthernetHeader_encoder_impl r {sz} v :=
    Eval simpl in (projT1 EthernetHeader_encoder sz v 0 r tt).

  Definition ethernet_Header_OK (e : EthernetHeader) := True.

  Lemma derive_distinguishing_word v0 v1
    : forall
      P (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
      CorrectRefinedDecoder ByteStringQueueMonoid
       (fun s : EthernetHeader => (ethernet_Header_OK s /\ IsProj Destination v1 s) /\ IsProj Source v0 s)
    (constant True) (constant (constant True))
    (Either format_nat 16 ◦ constant packet_len ++
            format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
            format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
            format_word ◦ constant WO~1~1~0~0~0~0~0~0 ++
            format_word ◦ constant wzero 24 ++ format_enum EtherTypeCodes ◦ EthType ++ empty_Format
            Or format_enum EtherTypeCodes ◦ EthType ++ empty_Format)
    (format_unused_word 16)
    (fun t env =>
    `(w, t', env') <- decode_word t env;
      if (wlt_dec w (natToWord 16 1501) : bool) then
         Some (true, t', env') else Some (false, t', env')) P
    (fun (bs : bool) (env : CacheFormat) (t : ByteString * CacheFormat) =>
     forall (s : EthernetHeader) (t' : ByteString) (env' : CacheFormat),
     ((format_nat 16 ◦ constant packet_len ++
       format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
       format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
       format_word ◦ constant WO~1~1~0~0~0~0~0~0 ++
       format_word ◦ constant wzero 24 ++ format_enum EtherTypeCodes ◦ EthType ++ empty_Format) s env
        (mappend (fst t) t', env') -> bs = true) /\
     ((format_enum EtherTypeCodes ◦ EthType ++ empty_Format) s env (mappend (fst t) t', env') -> bs = false)).
  Proof.
    intros.
    - econstructor; intros.
      + unfold format_unused_word, Compose_Format in H1.
        rewrite unfold_computes in H1; destruct_ex; split_and.
        eapply @Word_decode_correct with (P := P) in H2; eauto.
        destruct_ex; split_and.
        rewrite H2; simpl; subst.
        destruct (wlt_dec x0 (natToWord 16 1501)); simpl.
        * eexists _, _; intuition eauto.
          apply unfold_computes; intuition eauto.
          unfold sequence_Format, Projection_Format, empty_Format,
          Compose_Format, ComposeOpt.compose, Bind2 in H1.
          apply unfold_computes in H1; computes_to_inv.
          rewrite unfold_computes in H1; destruct_ex; split_and;
            injections; destruct v; subst.
          pose proof mempty_right as H'; simpl in H'; rewrite H' in H11;
            subst; clear H'.
          simpl in H11; subst.
          eapply @Enum_decode_correct with (P := P) in H8; try eassumption.
          eapply @Word_decode_correct with (P := P) in H6; try eassumption.
          destruct_ex; split_and.
          unfold decode_enum in H8.
          instantiate (1 := mempty) in H8.
          pose proof mempty_right as H'; simpl in H'; rewrite H' in H8;
            subst; clear H'.
          rewrite H12 in H8; simpl in H8.
          destruct (word_indexed x3 EtherTypeCodes) eqn: ?; try discriminate;
            simpl in H8.
          injections.
          unfold word_indexed in Heqo; simpl in Heqo.
          repeat match type of Heqo with
                   context[weqb ?a ?b] =>
                   let H := fresh in destruct (weqb a b) eqn : H;
                                       try apply weqb_sound in H; subst
                 end.
          injections.
          Local Transparent natToWord.
          unfold natToWord in w; compute in w; discriminate.
          unfold natToWord in w; compute in w; discriminate.
          unfold natToWord in w; compute in w; discriminate.
          unfold natToWord in w; compute in w; discriminate.
          discriminate.
          Discharge_NoDupVector.
        * eexists _, _; intuition eauto.
          apply unfold_computes; intuition eauto.
          unfold sequence_Format at 1, Projection_Format, empty_Format,
          Compose_Format, ComposeOpt.compose, Bind2 in H1.
          apply unfold_computes in H1; computes_to_inv.
          rewrite unfold_computes in H1; destruct_ex; split_and;
            injections; destruct v; subst.
          clear H1'.
          simpl in H11.
          eapply @Nat_decode_correct with (P := P) in H8; try eassumption.
          eapply @Word_decode_correct with (P := P) in H6; try eassumption.
          simpl in H8; rewrite H11 in H8.
          destruct_ex; split_and.
          unfold decode_nat in H8.
          rewrite H13 in H8; simpl in H8.
          injections; subst.
          destruct n.
          unfold wlt.
          rewrite !wordToN_nat, wordToNat_natToWord_idempotent.
          eapply Nomega.Nlt_in.
          rewrite !Nnat.Nat2N.id.
          eauto.
          reflexivity.
          etransitivity; try eassumption.
          rewrite <- Nnat.Nat2N.id.
          rewrite <- (Nnat.Nat2N.id 1501).
          apply Nomega.Nlt_out.
          admit. (* reflexivity works in later versions. *)
          
      + destruct (decode_word t env') as [ [ [? ?] ?] | ] eqn: ? ; simpl in H1;
          try discriminate.
        generalize Heqo; intros.
        eapply @Word_decode_correct with (P := P) in Heqo; try eassumption.
        destruct (wlt_dec w (natToWord 16 1501)) eqn: ?; simpl in H1;
          try discriminate; injections; intuition eauto;
            destruct_ex; split_and;
              subst; eexists _, _; intuition eauto.
        * apply unfold_computes; intros; intros; split; eauto.
          split; simpl; intros; eauto.
          unfold sequence_Format, Projection_Format, Compose_Format,
          ComposeOpt.compose, Bind2 in H2.
          apply unfold_computes in H2; computes_to_inv; subst.
          rewrite unfold_computes in H2; destruct_ex; split_and; subst.
          destruct v; destruct v2; injections.
          eapply @Word_decode_correct with (P := P) in H3; try eassumption.
          eapply @Enum_decode_correct with (P := P) in H5; try eassumption.
          destruct_ex; split_and.
          unfold decode_enum in H10.
          rewrite <- H7 in H5.
          rewrite H5 in H10; simpl in H10.
          unfold word_indexed in H10; simpl in H10.
          repeat match type of H10 with
                   context[weqb ?a ?b] =>
                   let H := fresh in destruct (weqb a b) eqn : H;
                                       try apply weqb_sound in H; subst
                 end; simpl in H10; try discriminate.
          Discharge_NoDupVector.
        * apply unfold_computes; intros; intros; split; eauto.
          split; simpl; intros.
          unfold sequence_Format at 1, Projection_Format, Compose_Format,
          ComposeOpt.compose, Bind2 in H2.
          apply unfold_computes in H2; computes_to_inv; subst.
          clear H2'.
          rewrite unfold_computes in H2; destruct_ex; split_and; subst.
          destruct v; destruct v2; injections.
          eapply @Word_decode_correct with (P := P) in H3; try eassumption.
          eapply @Nat_decode_correct with (P := P) in H5; try eassumption.
          destruct_ex; split_and.
          unfold decode_nat in H10.
          rewrite <- H7 in H5.
          rewrite H5 in H10; simpl in H10; injections.
          destruct n.
          unfold wlt.
          rewrite !wordToN_nat, wordToNat_natToWord_idempotent.
          eapply Nomega.Nlt_in.
          rewrite !Nnat.Nat2N.id.
          eauto.
          reflexivity.
          etransitivity; try eassumption.
          rewrite <- Nnat.Nat2N.id.
          rewrite <- (Nnat.Nat2N.id 1501).
          apply Nomega.Nlt_out.
          admit. (* reflexivity works in later versions. *)
          reflexivity.
        Grab Existential Variables.
        eauto.
        eauto.
  Qed.

  Lemma distinguishing_word_prefix
    : Prefix_Format _
    (Either format_nat 16 ◦ constant packet_len ++
            format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
            format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
            format_word ◦ constant WO~1~1~0~0~0~0~0~0 ++
            format_word ◦ constant wzero 24 ++ format_enum EtherTypeCodes ◦ EthType ++ empty_Format
            Or format_enum EtherTypeCodes ◦ EthType ++ empty_Format)
    (format_unused_word 16).
    Proof.
      unfold Prefix_Format, composeIf, Union_Format; intros.
      rewrite unfold_computes in H.
      destruct_ex; revert H; pattern x;
        apply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv; simpl;
          econstructor; [intros | econstructor; intros; eauto].
      Opaque natToWord.
      + unfold Vector.nth in H; simpl in H.
        unfold sequence_Format at 1 in H.
        unfold Projection_Format, empty_Format,
        Compose_Format, ComposeOpt.compose, Bind2 in H.
        computes_to_inv.
        rewrite unfold_computes in H; destruct_ex; split_and;
          subst; eauto.
        unfold format_nat, format_word in H0; computes_to_inv; subst.
        injections; eexists _, _, _; intuition eauto.
        unfold format_unused_word, Compose_Format.
        apply unfold_computes; eexists _; intuition eauto;
          try computes_to_econstructor.
        apply unfold_computes; eauto.
      + unfold Vector.nth in H; simpl in H.
        unfold sequence_Format at 1 in H.
        unfold Projection_Format, empty_Format,
        Compose_Format, ComposeOpt.compose, Bind2 in H.
        computes_to_inv.
        rewrite unfold_computes in H; destruct_ex; split_and;
          subst; eauto.
        unfold format_enum, format_word in H0; computes_to_inv; subst.
        injections; eexists _, _, _; intuition eauto.
        unfold format_unused_word, Compose_Format.
        apply unfold_computes; eexists _; intuition eauto;
          try computes_to_econstructor.
        apply unfold_computes; eauto.
    Qed.

    Lemma valid_packet_len_OK_good_Len
      : lt packet_len (pow2 16).
    Proof.
    intros.
    etransitivity; eauto.
    rewrite <- (wordToNat_natToWord_idempotent 16 1501).
    eapply wordToNat_bound.
    simpl; eapply BinNat.N.ltb_lt; reflexivity.
  Qed.

  Hint Extern 4 => eapply valid_packet_len_OK_good_Len : data_inv_hints.

  Ltac apply_new_combinator_rule ::=
    match goal with
    | H : cache_inv_Property ?mnd _
      |- context[CorrectRefinedDecoder] =>
      split;
      [ eapply (@derive_distinguishing_word _ _ _ H); eauto
      | eapply distinguishing_word_prefix ]
  end.

  Definition EthernetHeader_decoder
    : CorrectAlignedDecoderFor ethernet_Header_OK EthernetHeader_Format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  (* Step Four: Extract the decoder function, and have /it/ start decoding
     at the start of the provided ByteString [v]. *)

  Definition Ethernet_decoder_impl {sz} v :=
    Eval simpl in (projT1 EthernetHeader_decoder sz v 0 ()).

End EthernetPacketDecoder.

Print Ethernet_decoder_impl.
