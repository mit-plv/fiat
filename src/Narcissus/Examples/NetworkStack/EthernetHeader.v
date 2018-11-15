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
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
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
  (* which is a parameter to the formatr and decoder. *)
  Variable packet_len_OK : lt packet_len 1501.

  Definition EthernetHeader_Format
    : FormatM EthernetHeader ByteString :=
    format_Vector format_word ◦ Destination
   ++ format_Vector format_word ◦ Source
   ++ Either
   format_nat 16 ◦ (fun _ => packet_len)
   ++ format_word ◦ (fun _ => WO~0~1~0~1~0~1~0~1)
   ++ format_word ◦ (fun _ => WO~0~1~0~1~0~1~0~1)
   ++ format_word ◦ (fun _ => WO~1~1~0~0~0~0~0~0)
   ++ format_word ◦ (fun _ => wzero 24)
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

  Definition v1042_test (b : ByteString) : bool :=
    match monoid_get_word 16 b with
    | Some w => if wlt_dec w (natToWord 16 1501) then true else false
    | _ => false
    end.

  Opaque natToWord.

  Lemma v1042_OKT
    : forall (data : EthernetHeader) (bin : ByteString) (env xenv : CacheFormat) (ext : ByteString),
      ((   format_nat 16 ◦ (fun _ => packet_len)
        ++ format_word ◦ (fun _ => WO~0~1~0~1~0~1~0~1)
        ++ format_word ◦ (fun _ => WO~0~1~0~1~0~1~0~1)
        ++ format_word ◦ (fun _ => WO~1~1~0~0~0~0~0~0)
        ++ format_word ◦ (fun _ => wzero 24)
        ++ format_enum EtherTypeCodes ◦ EthType
        ++ empty_Format ) data env) ↝ (bin, xenv)
      -> v1042_test (mappend bin ext) = true.
  Proof.
    intros.
    unfold sequence_Format, compose at 1, Bind2 in H;
      computes_to_inv; destruct v; destruct v0.
        injections.
    pose proof mappend_assoc as H'''; simpl in H'''; rewrite <- H'''.
    unfold v1042_test.
    pose proof (monoid_get_encode_word' 16 (natToWord 16 packet_len)) as H''''.
    apply EquivFormat_Projection_Format in H.
    unfold format_nat, format_word in H; computes_to_inv.
    apply (f_equal fst) in H; simpl in H.
    rewrite <- H.
    simpl mappend in *.
    rewrite H''''.
    find_if_inside; eauto.
    destruct n.
    eapply natToWord_wlt; eauto; try reflexivity.
    etransitivity.
    unfold BinNat.N.lt; rewrite <- Nnat.Nat2N.inj_compare.
    eapply Compare_dec.nat_compare_lt; eassumption.
    reflexivity.
  Qed.

  Hint Resolve v1042_OKT : bin_split_hints.

    Lemma v1042_OKE
    : forall (data : EthernetHeader) (bin : ByteString) (env xenv : CacheFormat) (ext : ByteString),
      (   format_enum EtherTypeCodes ◦ EthType
       ++ empty_Format) data env ↝ (bin, xenv)
      -> v1042_test (mappend bin ext) = false.
  Proof.
    intros.
    apply EquivFormat_Projection_Format_Empty_Format in H.
    apply EquivFormat_Projection_Format in H.
    unfold compose, Bind2, format_enum, format_word in H; computes_to_inv; subst.
    injections.
    (*pose proof (f_equal fst H'') as H'; unfold fst in H'; rewrite <- H'. *)
    unfold v1042_test.
    pose monoid_get_encode_word' as H'''; rewrite H'''; find_if_inside; eauto.
    revert w; clear.
    match goal with
      |- context [Vector.nth (m := ?n) ?w ?idx] => remember idx; clear
    end.
    eapply forall_Vector_P; repeat econstructor;
      unfold wlt; compute; intros; discriminate.
  Qed.

  Hint Resolve v1042_OKE : bin_split_hints.

  Lemma valid_packet_len_OK_good_Len
    : lt packet_len (pow2 16).
  Proof.
    intros.
    etransitivity; eauto.
    rewrite <- (wordToNat_natToWord_idempotent 16 1501).
    eapply wordToNat_bound.
    simpl; eapply BinNat.N.ltb_lt; reflexivity.
  Qed.

  Hint Resolve valid_packet_len_OK_good_Len : data_inv_hints.

  Definition aligned_v1042_test
        {sz : nat}
        (v : t Core.char sz)
        (idx : nat)
    : bool :=
    match nth_opt v idx, nth_opt v (S idx) with
    | Some w1, Some w2 =>
      if wlt_dec (combine w2 w1) (natToWord 16 1501) then true else false
    | _, _ => false
    end.

  Lemma aligned_v1042_test_OK {sz}
    : forall (v : t Core.char sz),
      v1042_test (build_aligned_ByteString v) =
      aligned_v1042_test v 0.
  Proof.
    destruct v.
    reflexivity.
    destruct v.
    reflexivity.
    unfold v1042_test.
    replace (monoid_get_word 16 (build_aligned_ByteString (h :: h0 :: v)))
      with
        (Some (combine h0 h)).
    reflexivity.
    replace (build_aligned_ByteString (h :: h0 :: v))
      with (mappend (build_aligned_ByteString (h :: h0 :: Vector.nil _)) (build_aligned_ByteString v)).
    rewrite <- (monoid_get_encode_word' _ (combine h0 h) (build_aligned_ByteString v)).
    f_equal.
    f_equal.
    simpl.
    unfold Core.char in *.
    shatter_word h.
    shatter_word h0.
    simpl.
    rewrite build_aligned_ByteString_cons; simpl.
    unfold ByteString_enqueue_ByteString; simpl.
    unfold ByteString_enqueue_char.
    simpl.
    repeat f_equal.
    unfold build_aligned_ByteString; simpl.
    erewrite (ByteString_enqueue_simpl x6); simpl.
    erewrite (ByteString_enqueue_simpl x5); simpl.
    erewrite (ByteString_enqueue_simpl x4); simpl.
    erewrite (ByteString_enqueue_simpl x3); simpl.
    erewrite (ByteString_enqueue_simpl x2); simpl.
    erewrite (ByteString_enqueue_simpl x1); simpl.
    erewrite (ByteString_enqueue_simpl x0); simpl.
    unfold ByteString_enqueue; simpl.
    f_equal.
    eapply Core.le_uniqueness_proof.
    simpl.
    rewrite <- build_aligned_ByteString_append.
    reflexivity.
    Grab Existential Variables.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
  Qed.

  Definition EthernetHeader_decoder
    : CorrectAlignedDecoderFor ethernet_Header_OK EthernetHeader_Format.
  Proof.
    start_synthesizing_decoder.
    normalize_format.


    Ltac solve_side_condition :=
    (* Try to discharge a side condition of one of the base rules *)
      match goal with
      | |- NoDupVector _ => Discharge_NoDupVector
      | |- context[Vector_predicate_rest (fun _ _ => True) _ _ _ _] =>
        intros; apply Vector_predicate_rest_True
      | |- context[FixList_predicate_rest (fun _ _ => True) _ _ _] =>
        intros; eapply FixedList_predicate_rest_True
      | |- context[fun st b' => ith _ (SumType.SumType_index _ st) (SumType.SumType_proj _ st) b'] =>
        let a'' := fresh in
        intro a''; intros; repeat instantiate (1 := fun _ _ => True);
        repeat destruct a'' as [ ? | a''] ; auto
      | _ => solve [solve_data_inv]
      | _ => solve [intros; instantiate (1 := fun _ _ => True); exact I]
    end.

    Ltac FinishDecoder :=
      solve [simpl; intros;
             eapply CorrectDecoderinish;
             [ build_fully_determined_type idtac
             | decide_data_invariant ] ].

Ltac apply_rules :=
  (* Processes the goal by either: *)
  (* Unfolding an identifier *)
  match goal with
  | |- CorrectDecoder _ _ _ ?H _ _ =>
    progress unfold H
  | |- context [CorrectDecoder _ _ _ empty_Format _ _] => FinishDecoder
  | H : cache_inv_Property ?P ?P_inv
    |- CorrectDecoder ?mnd _ _ (_ ◦ _ ++ _) _ _ =>
    first [
        eapply (format_const_sequence_correct H) with (monoid := mnd);
        clear H;
        [ intros; solve [repeat apply_rules]
        | solve [ solve_side_condition ]
        | intros ]
      | eapply (format_sequence_correct H) with (monoid := mnd);
        clear H;
        [ intros; solve [repeat apply_rules]
        | solve [ solve_side_condition ]
        | intros ]
      ]
  | H : cache_inv_Property ?P ?P_inv |- CorrectDecoder ?mnd _ _ (Either _ Or _)%format _ _ =>
    eapply (composeIf_format_correct H); clear H;
    [ intros
    | intros
    | solve [intros; intuition (eauto with bin_split_hints) ]
    | solve [intros; intuition (eauto with bin_split_hints) ] ]
  | |- context [CorrectDecoder ?mnd _ _ (format_Vector _) _ _] =>
    intros; eapply (@Vector_decode_correct _ _ _ mnd)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ format_word _ _] =>
    intros; revert H; eapply Word_decode_correct
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ (format_nat _) _ _] =>
    intros; revert H; eapply Nat_decode_correct
  | |- context [CorrectDecoder _ _ _ (format_list _) _ _] => intros; apply FixList_decode_correct

  | |- context [CorrectDecoder _ _ _ (format_bool) _ _] =>
    eapply bool_decode_correct

  | |- context [CorrectDecoder _ _ _ (Option.format_option _ _) _ _] =>
    intros; eapply Option.option_format_correct;
    [ match goal with
        H : cache_inv_Property _ _ |- _ => eexact H
      end | .. ]

| H : cache_inv_Property _ _
  |- context [CorrectDecoder _ _ _ (format_enum ?tb) _ _] =>
  eapply (fun NoDup => @Enum_decode_correct _ _ _ _ _ _ _ tb NoDup _ H);
    solve_side_condition

  | |- context[CorrectDecoder _ _ _ StringOpt.format_string _ _ ] =>
    eapply StringOpt.String_decode_correct
  | |- context [CorrectDecoder _ _ _ (format_SumType (B := ?B) (cache := ?cache) (m := ?n) ?types _) _ _] =>
    let cache_inv_H := fresh in
    intros cache_inv_H;
    first
      [let types' := (eval unfold types in types) in
       ilist_of_evar
         (fun T : Type => T -> @CacheFormat cache -> Comp (B * @CacheFormat cache))
         types'
         ltac:(fun formatrs' =>
                 ilist_of_evar
                   (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache))
                   types'
                   ltac:(fun decoders' =>
                           ilist_of_evar
                             (fun T : Type => Ensembles.Ensemble T)
                             types'
                             ltac:(fun invariants' =>
                                     ilist_of_evar
                                       (fun T : Type => T -> B -> Prop)
                                       types'
                                       ltac:(fun invariants_rest' =>
                                               Vector_of_evar
                                                 n
                                                 (Ensembles.Ensemble (CacheDecode -> Prop))
                                                 ltac:(fun cache_invariants' =>
                                                         eapply (SumType_decode_correct (m := n) types) with
                                                         (formatrs := formatrs')
                                                           (decoders := decoders')
                                                           (invariants := invariants')
                                                           (invariants_rest := invariants_rest')
                                                           (cache_invariants :=  cache_invariants')
              )))))
      |          ilist_of_evar
                   (fun T : Type => T -> @CacheFormat cache -> Comp (B * @CacheFormat cache))
                   types
                   ltac:(fun formatrs' =>
                           ilist_of_evar
                             (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache))
                             types
                             ltac:(fun decoders' =>
                                     ilist_of_evar
                                       (fun T : Type => Ensembles.Ensemble T)
                                       types
                                       ltac:(fun invariants' =>
                                               ilist_of_evar
                                                 (fun T : Type => T -> B -> Prop)
                                                 types
                                                 ltac:(fun invariants_rest' =>
                                                         Vector_of_evar
                                                           n
                                                           (Ensembles.Ensemble (CacheDecode -> Prop))
                                                           ltac:(fun cache_invariants' =>
                                                                   eapply (SumType_decode_correct (m := n) types) with
                                                                   (formatrs := formatrs')
                                                                     (decoders := decoders')
                                                                     (invariants := invariants')
                                                                     (invariants_rest := invariants_rest')
                                                                     (cache_invariants :=  cache_invariants'))))))
      ];
    [ simpl; repeat (apply IterateBoundedIndex.Build_prim_and; intros); try exact I
    | apply cache_inv_H ]
  end.

repeat apply_rules.
  cbv beta; synthesize_cache_invariant.
  (* Perform algebraic simplification of the decoder implementation. *)
  unfold sequence_Decode.
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  cbv beta; align_decoders.
  eapply @AlignedDecode_ifb_dep.
  intros; rewrite aligned_v1042_test_OK; higher_order_reflexivity.
  simpl; intros; pattern sz, v; eapply Vector.caseS; reflexivity.
  repeat align_decoders_step.
  repeat align_decoders_step.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)

Definition Ethernet_decoder_impl {sz} v :=
  Eval simpl in (projT1 EthernetHeader_decoder sz v 0 ()).

End EthernetPacketDecoder.

Print Ethernet_decoder_impl.
