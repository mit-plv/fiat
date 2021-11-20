Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.ZArith.ZArith.

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
       (fun s : EthernetHeader => (ethernet_Header_OK s /\ IsProj Destination v1 s) /\ IsProj Source v0 s) s ->
     ((format_nat 16 ◦ constant packet_len ++
       format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
       format_word ◦ constant WO~0~1~0~1~0~1~0~1 ++
       format_word ◦ constant WO~1~1~0~0~0~0~0~0 ++
       format_word ◦ constant wzero 24 ++ format_enum EtherTypeCodes ◦ EthType ++ empty_Format) s env
        (mappend (fst t) t', env') -> bs = true) /\
     ((format_enum EtherTypeCodes ◦ EthType ++ empty_Format) s env (mappend (fst t) t', env') -> bs = false)).
  Proof.
    intros. apply composeIf_subformat_correct_low; intros.
    - unfold format_unused_word, Compose_Format in H2.
      rewrite unfold_computes in H2; destruct_conjs.
      eapply @Word_decode_correct with (P := P) in H5; eauto. destruct_conjs.
      rewrite H8; simpl; subst.
      destruct wlt_dec; simpl; eauto.
    - destruct decode_word as [ [ [? ?] ?] | ] eqn: ? ; simpl in H1;
        try discriminate.
      generalize Heqo; intros.
      eapply @Word_decode_correct with (P := P) in Heqo; try eassumption.
      destruct wlt_dec eqn: ?; simpl in H1;
        try discriminate; injections; intuition eauto 1;
          destruct_conjs; subst; eexists _, _; intuition eauto 1.
      + unfold sequence_Format, Projection_Format, Compose_Format,
        ComposeOpt.compose, Bind2 in H8. computes_to_inv; subst.
        rewrite unfold_computes in H8; destruct_conjs; subst; injections.
        eapply @Word_decode_correct with (P := P) in H4; try eassumption.
        eapply @Enum_decode_correct with (P := P) in H11; try eassumption.
        destruct_conjs; subst.
        unfold decode_enum in H19. simpl in *.
        rewrite <- H12 in H13.
        rewrite H13 in H19; simpl in H19.
        unfold word_indexed in H19; simpl in H19.
        repeat match type of H19 with
                 context[weqb ?a ?b] =>
                 let H := fresh in destruct (weqb a b) eqn : H;
                                     try apply weqb_sound in H; subst
               end; simpl in H10; try discriminate.
        Discharge_NoDupVector.
      + unfold sequence_Format at 1, Projection_Format, Compose_Format,
        ComposeOpt.compose, Bind2 in H8. computes_to_inv; subst.
        clear H8'.
        rewrite unfold_computes in H8; destruct_conjs; subst; injections.
        eapply @Word_decode_correct with (P := P) in H4; try eassumption.
        eapply @Nat_decode_correct with (P := P) in H11; try eassumption.
        destruct_conjs; subst; simpl in *.
        unfold decode_nat in H20.
        rewrite <- H13 in H14.
        rewrite H14 in H20; simpl in H20; injections.
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
        reflexivity.
        Unshelve.
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
