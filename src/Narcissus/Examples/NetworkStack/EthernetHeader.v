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
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

Definition monoid : Monoid ByteString := ByteStringQueueMonoid.

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
  (* which is a parameter to the formatr and decoder. *)
  Variable packet_len_OK : lt packet_len 1501.

  Definition format_EthernetHeader_Spec (eth : EthernetHeader) :=
    format_Vector format_word eth!"Destination"
                       ThenC (format_Vector format_word eth!"Source")
                       ThenC Either
                       format_nat 16 packet_len
                       ThenC format_word (WO~0~1~0~1~0~1~0~1)
                       ThenC format_word (WO~0~1~0~1~0~1~0~1)
                       ThenC format_word (WO~1~1~0~0~0~0~0~0)
                       ThenC format_word (wzero 24)
                       ThenC format_enum EtherTypeCodes eth!"Type"
                       DoneC
                       Or format_enum EtherTypeCodes eth!"Type"
                       DoneC.

  Definition ethernet_Header_OK (e : EthernetHeader) := True.

  Definition v1042_test (b : ByteString) : bool :=
    match monoid_get_word 16 b with
    | Some w => if wlt_dec w (natToWord 16 1501) then true else false
    | _ => false
    end.

  Lemma v1042_OKT
    : forall (data : EthernetHeader) (bin : ByteString) (env xenv : CacheFormat) (ext : ByteString),
      (format_nat 16 packet_len
                       ThenC format_word WO~0~1~0~1~0~1~0~1
                       ThenC format_word WO~0~1~0~1~0~1~0~1
                       ThenC format_word WO~1~1~0~0~0~0~0~0
                       ThenC format_word (wzero 24) ThenC format_enum EtherTypeCodes data!"Type" DoneC) env
                                                                                                                  ↝ (bin, xenv) -> v1042_test (mappend bin ext) = true.
  Proof.
    intros.
    unfold compose at 1 in H; unfold Bind2 in H;
      computes_to_inv; destruct v; destruct v0; simpl in *;
        injections.
    unfold format_nat, format_word in H; computes_to_inv.
    pose proof (f_equal fst H) as H''; simpl in H''; rewrite <- H''.
    pose proof mappend_assoc as H'''; simpl in H'''; rewrite <- H'''.
    unfold v1042_test.
    pose monoid_get_encode_word' as H''''; rewrite H''''; find_if_inside; eauto.
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
      (format_enum EtherTypeCodes data!"Type" DoneC) env ↝ (bin, xenv)
      -> v1042_test (mappend bin ext) = false.
  Proof.
    intros; unfold compose at 1 in H; unfold Bind2 in H;
      computes_to_inv; destruct v; destruct v0; simpl in *;
        injections.
    unfold format_enum, format_word in H; computes_to_inv.
    pose proof (f_equal fst H) as H'; unfold fst in H'; rewrite <- H'.
    pose proof mappend_assoc as H''; simpl in H''; rewrite <- H''.
    unfold v1042_test.
    pose monoid_get_encode_word' as H'''; rewrite H'''; find_if_inside; eauto.
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
    : CorrectDecoderFor ethernet_Header_OK format_EthernetHeader_Spec.
  Proof.
    synthesize_decoder.
  Defined.

  Definition frame_decoder := Eval simpl in proj1_sig EthernetHeader_decoder.

End EthernetPacketDecoder.

Print frame_decoder.
