Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

Definition transformer : Transformer ByteString := ByteStringQueueTransformer.

(* Start Example Derivation. *)
Section EthernetPacketDecoder.

  Definition EthernetHeader :=
    @Tuple <"Destination" :: Vector.t char 6,
    "Source" :: Vector.t char 6,
    "Type" :: EnumType ["ARP"; "IP"; "RARP"]>.

  Definition EtherTypeCodes : Vector.t (word 16) 3 :=
    [WO~0~0~0~0~1~0~0~0~0~0~0~0~0~1~1~0;
     WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0;
     WO~0~0~0~0~1~0~0~0~0~0~1~1~0~1~0~1
    ].

  Variable packet_len : nat. (* The length of the ethernet packet, *)
  (* which is a parameter to the encoder and decoder. *)
  Variable packet_len_OK : lt packet_len 1501.

  Definition encode_EthernetHeader_Spec (eth : EthernetHeader) :=
    encode_Vector_Spec encode_word_Spec eth!"Destination"
                       ThenC (encode_Vector_Spec encode_word_Spec eth!"Source")
                       ThenC Either
                       encode_nat_Spec 16 packet_len
                       ThenC encode_word_Spec (WO~0~1~0~1~0~1~0~1)
                       ThenC encode_word_Spec (WO~0~1~0~1~0~1~0~1)
                       ThenC encode_word_Spec (WO~1~1~0~0~0~0~0~0)
                       ThenC encode_word_Spec (wzero 24)
                       ThenC encode_enum_Spec EtherTypeCodes eth!"Type"
                       DoneC
                       Or encode_enum_Spec EtherTypeCodes eth!"Type"
                       DoneC.

  Definition ethernet_Header_OK (e : EthernetHeader) := True.

  Definition v1042_test (b : ByteString) : bool :=
    match transformer_get_word 16 b with
    | Some w => if wlt_dec w (natToWord 16 1501) then true else false
    | _ => false
    end.

  Lemma v1042_OKT
    : forall (data : EthernetHeader) (bin : ByteString) (env xenv : CacheEncode) (ext : ByteString),
      (encode_nat_Spec 16 packet_len
                       ThenC encode_word_Spec WO~0~1~0~1~0~1~0~1
                       ThenC encode_word_Spec WO~0~1~0~1~0~1~0~1
                       ThenC encode_word_Spec WO~1~1~0~0~0~0~0~0
                       ThenC encode_word_Spec (wzero 24) ThenC encode_enum_Spec EtherTypeCodes data!"Type" DoneC) env
                                                                                                                  ↝ (bin, xenv) -> v1042_test (transform bin ext) = true.
  Proof.
    intros.
    unfold compose at 1 in H; unfold Bind2 in H;
      computes_to_inv; destruct v; destruct v0; simpl in *;
        injections.
    unfold encode_nat_Spec, encode_word_Spec in H; computes_to_inv.
    pose proof (f_equal fst H) as H''; simpl in H''; rewrite <- H''.
    pose proof transform_assoc as H'''; simpl in H'''; rewrite <- H'''.
    unfold v1042_test.
    pose transformer_get_encode_word' as H''''; rewrite H''''; find_if_inside; eauto.
    destruct n.
    eapply natToWord_wlt; eauto; try reflexivity.
    etransitivity.
    unfold BinNat.N.lt; rewrite <- Nnat.Nat2N.inj_compare.
    eapply Compare_dec.nat_compare_lt; eassumption.
    reflexivity.
  Qed.

  Hint Resolve v1042_OKT : bin_split_hints.

  Lemma v1042_OKE
    : forall (data : EthernetHeader) (bin : ByteString) (env xenv : CacheEncode) (ext : ByteString),
      (encode_enum_Spec EtherTypeCodes data!"Type" DoneC) env ↝ (bin, xenv)
      -> v1042_test (transform bin ext) = false.
  Proof.
    intros; unfold compose at 1 in H; unfold Bind2 in H;
      computes_to_inv; destruct v; destruct v0; simpl in *;
        injections.
    unfold encode_enum_Spec, encode_word_Spec in H; computes_to_inv.
    pose proof (f_equal fst H) as H'; unfold fst in H'; rewrite <- H'.
    pose proof transform_assoc as H''; simpl in H''; rewrite <- H''.
    unfold v1042_test.
    pose transformer_get_encode_word' as H'''; rewrite H'''; find_if_inside; eauto.
    revert w; clear.
    match goal with
      |- context [Vector.nth (m := ?n) ?w ?idx] => remember idx; clear
    end.
    Local Transparent natToWord.
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

  Definition EthernetHeader_decoder
    : CorrectDecoderFor ethernet_Header_OK encode_EthernetHeader_Spec.
  Proof.
    synthesize_decoder.
  Defined.

  Definition frame_decoder := Eval simpl in proj1_sig EthernetHeader_decoder.

End EthernetPacketDecoder.

Print frame_decoder.
