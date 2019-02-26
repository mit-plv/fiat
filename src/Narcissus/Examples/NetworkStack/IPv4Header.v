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
Open Scope string_scope.
Open Scope Tuple_scope.

(* Our source data type for IP packets. *)
Record IPv4_Packet :=
  { TotalLength : word 16;
    ID : word 16;
    DF : bool; (* Don't fragment flag *)
    MF : bool; (*  Multiple fragments flag *)
    FragmentOffset : word 13;
    TTL : word 8;
    Protocol : EnumType ["ICMP"; "TCP"; "UDP"];
    SourceAddress : word 32;
    DestAddress : word 32;
    Options : list (word 32) }.

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
     WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
     WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Format : FormatM IPv4_Packet ByteString :=
  (format_nat 4 ◦ (constant 4)
               ++ format_nat 4 ◦ (plus 5) ◦ @length _ ◦ Options
               ++ format_unused_word 8 (* TOS Field! *)
               ++ format_word ◦ TotalLength
               ++ format_word ◦ ID
               ++ format_unused_word 1 (* Unused flag! *)
               ++ format_bool ◦ DF
               ++ format_bool ◦ MF
               ++ format_word ◦ FragmentOffset
               ++ format_word ◦ TTL
               ++ format_enum ProtocolTypeCodes ◦ Protocol)%format
ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn (format_word ◦ SourceAddress
               ++ format_word ◦ DestAddress
               ++ format_list format_word ◦ Options)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4.(Options)|) 11 /\
  lt (20 + 4 * |ipv4.(Options)|) (wordToNat ipv4.(TotalLength)).

(* Step One: Synthesize an encoder and a proof that it is correct. *)

Ltac new_encoder_rules ::=
  match goal with
    |- CorrectAlignedEncoder (_ ThenChecksum _ OfSize _ ThenCarryOn _) _ =>
    eapply @CorrectAlignedEncoderForIPChecksumThenC
  end.

Definition IPv4_encoder :
  CorrectAlignedEncoderFor IPv4_Packet_Format.
Proof.
  synthesize_aligned_encoder.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition IPv4_encoder_impl {sz} v r :=
  Eval simpl in (projT1 IPv4_encoder sz v 0 r tt).
Print IPv4_encoder_impl.

(*Lemma sequence_Compose_format_refined_decode_correct
      {cache : Cache}
      {S V1 V2 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view1 : S -> V1)
      (view2 : S -> V2 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1 : V1 -> Prop)
      (View_Predicate2 : V2 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (subformat : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate1_OK : forall (s : S), Source_Predicate s -> View_Predicate1 (view1 s))

      (view_format : FormatM V2 T)
      (decode2 : DecodeM (V2 * T) T)
      (decode_2_OK :
           cache_inv_Property P P_inv2 ->
         CorrectRefinedDecoder monoid Source_Predicate
                               View_Predicate2
                               view2 format2 subformat decode2 P view_format)
  : CorrectRefinedDecoder
      monoid
      Source_Predicate
      View_Predicate2
      view2
      (Projection_Format format1 view1 ++ format2)%format
      (Projection_Format format1 view1 ++ subformat)%format
      (Compose_Decode (sequence_Decode' decode1 (fun _ => decode2))
                      (fun vt => ((snd (fst vt), snd vt))))
      P (Compose_Format format1 (fun _ _ => True) ++ view_format)%format.
Proof.
  specialize (decode_1_OK (proj1 P_inv_pf)).
  specialize (decode_2_OK (proj2 P_inv_pf)).
  destruct decode_2_OK as [decode_2_OK ?].
  split.
  - eapply injection_decode_correct.
    + eapply Sequence_decode_correct.
      * eassumption.
      * intros; eapply Compose_decode_correct; eauto.
        intros; subst; eauto.
      * simpl; intros; instantiate (1 := fun v1 s => view1 s = v1);
          simpl; eauto.
      * intros. simpl.
        instantiate (3 := fun _ => View_Predicate2).
        instantiate (2 := fun _ => view2).
        instantiate (1 := fun _ => view_format).
        eapply weaken_source_pred; eauto.
        unfold flip, impl, pointwise_relation; intuition.
      * intros.
        instantiate (1 := (Projection_Format format1 fst ++ Projection_Format view_format snd)%format).
        unfold sequence_Format, ComposeOpt.compose, Bind2;
          apply unfold_computes; computes_to_econstructor.
        unfold Projection_Format, Compose_Format; apply unfold_computes.
        eexists _; simpl; intuition eauto.
        apply unfold_computes; eauto.
        computes_to_econstructor.
        unfold Projection_Format, Compose_Format; apply unfold_computes.
        eexists _; simpl; intuition eauto.
        apply unfold_computes; eauto.
        reflexivity.
    + simpl; intros; intuition.
    + simpl; intros; intuition.
    + simpl; intros.
      unfold sequence_Format, ComposeOpt.compose, Bind2,
      Projection_Format, Compose_Format in *; computes_to_inv.
      rewrite -> unfold_computes in H0'; destruct_ex; split_and;
        subst.
      rewrite -> unfold_computes in H0; destruct_ex; split_and;
        subst.
      destruct v1; destruct v0; simpl in *; computes_to_econstructor.
      apply unfold_computes.
      eexists; eauto.
      computes_to_econstructor; eauto.
  - intros.
    unfold sequence_Format, ComposeOpt.compose, Bind2,
      Projection_Format, Compose_Format in *; computes_to_inv.
    rewrite -> unfold_computes in H0; destruct_ex; split_and;
      subst; injections; destruct v0; destruct v; simpl in *.
    eapply H in H0'; destruct_ex; split_and; subst.
    setoid_rewrite mappend_assoc.
    eexists _, _, _; split; eauto.
    computes_to_econstructor.
    apply unfold_computes; eexists; eauto.
    computes_to_econstructor; eauto.
Qed.

Lemma sequence_Compose_format_decode_correct''
      {cache : Cache}
      {S V1 V2 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view1 : S -> V1)
      (view : S -> V2 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (View_Predicate2  : V2 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (view_format : FormatM V2 T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s v, Source_Predicate s ->
                                       IsProj view1 v s  ->
                                       View_Predicate1 v)
      (decode2 : V1 -> DecodeM (V2 * T) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectDecoder monoid (fun s => Source_Predicate s
                                          /\ IsProj view1 v1 s)
                         View_Predicate2
                         view format2 (decode2 v1) P view_format)
  : CorrectDecoder
      monoid
      Source_Predicate
      View_Predicate2
      view
      (Projection_Format format1 view1 ++ format2)%format
      (sequence_Decode decode1 decode2)
      P (Compose_Format format1 (fun _ _ => True) ++ view_format)%format.
Proof.
  Opaque CorrectDecoder.
  eapply Sequence_decode_correct. with (view1 := view)
                                      (view2 := fun _ => eq)
                                      (View_Predicate2 := fun v1 v2 => Source_Predicate v2 /\
                                                                       view v2 v1)
                                      (consistency_predicate := fun v1 s => view s v1);
    try eassumption; eauto.
  - intros; eapply Compose_decode_correct; try eassumption;
    intros; eauto.
  - instantiate (1 := fun _ => format2); eauto.
  - simpl; intros.
    unfold sequence_Format, ComposeOpt.compose, Bind2,
    Projection_Format, Compose_Format.
    apply unfold_computes.
    apply unfold_computes in H.
    apply unfold_computes in H0.
    eauto.
Qed.

Lemma sequence_Compose_format_refined_decode_correct_finish
      {cache : Cache}
      {S V1 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view1 : S -> V1)
      (view : S -> V1 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1 : V1 -> Prop)
      (View_Predicate' : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (view_format : FormatM V1 T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (view_OK : forall v s, IsProj view1 s v -> view v s)
      (View_Predicate1_OK : forall (s : S), Source_Predicate s -> View_Predicate1 (view1 s))
      (*view_format_OK : forall v t env,
          format1 v env t ->
          View_Predicate' v ->
          view_format v env t*)
      (View_Predicate'_OK :
         forall s v, Source_Predicate s -> view s v -> View_Predicate' v)
      (View_Predicate'_OK_2 :
         forall v, View_Predicate1 v -> View_Predicate' v)
  : CorrectRefinedDecoder
      monoid
      Source_Predicate
      View_Predicate'
      view
      (Projection_Format format1 view1 ++ format2)%format
      (Projection_Format format1 view1)%format
      decode1
      P view_format%format.
Proof.
  specialize (decode_1_OK (proj1 P_inv_pf)).
  split.
  - eapply weaken_view_pred.
    unfold pointwise_relation, impl; intros.
    eauto.
    eapply format_decode_correct_alt'.
    7: { eapply projection_decode_correct.
         eapply decode_1_OK.
         intros.
         eapply View_Predicate1_OK.
         apply H. }
    all: unfold flip, pointwise_relation, impl; intuition eauto.
    unfold Projection_Format; eapply EquivFormat_reflexive.
    unfold Projection_Format; eapply EquivFormat_reflexive.
  - intros.
    unfold sequence_Format, ComposeOpt.compose, Bind2,
      Projection_Format, Compose_Format in *; computes_to_inv.
    rewrite -> unfold_computes in H; destruct_ex; split_and;
      subst; injections; destruct v0; destruct v; simpl in *.
    eexists _, _, _; split; eauto.
    apply unfold_computes.
    eexists _; intuition eauto.
Qed.

Lemma IPv4_Packet_measure_decode_OK
  : forall P,
    {decode : _ & {subformat : _ &
                 {P_inv : _ &
                          { view_format : _ &
                 cache_inv_Property P P_inv ->
                 CorrectRefinedDecoder monoid IPv4_Packet_OK (constant True) (constant (constant True))
    ((format_nat 4 ◦ constant 4 ++
                 format_nat 4 ◦ Init.Nat.add 5 ◦ Datatypes.length (A:=word 32) ◦ Options ++
      format_unused_word 8 ++
      format_word ◦ TotalLength ++
      format_word ◦ ID ++
      format_unused_word 1 ++
      format_bool ◦ DF ++
      format_bool ◦ MF ++ format_word ◦ FragmentOffset ++ format_word ◦ TTL ++ format_enum ProtocolTypeCodes ◦ Protocol) ++
                                                                                                                         format_unused_word 16 ++ format_word ◦ SourceAddress ++ format_word ◦ DestAddress ++ format_list format_word ◦ Options)%format
    subformat
    (*(format_word ◦ constant natToWord 4 4
                      ++
                      ((format_nat 4 ◦ Init.Nat.add 5) ◦ Datatypes.length (A:=word 32)) ◦ Options)%format *)
    decode
    (*fun t env =>
       `(_, t', env') <- decode_nat 4 t env;
         `(n, _, _) <- decode_nat 4 t' env';
         Some (n * 32, t, env)*) P
    view_format /\
                 (forall n env t,
                     view_format n env t ->
                     forall (a : IPv4_Packet) (t1 t2 : ByteString * CacheFormat),
               word 16 ->
               IPv4_Packet_OK a ->
               (format_nat 4 ◦ constant 4 ++
                format_nat 4 ◦ Init.Nat.add 5 ◦ Datatypes.length (A:=word 32) ◦ Options ++
                format_unused_word 8 ++
                format_word ◦ TotalLength ++
                format_word ◦ ID ++
                format_unused_word 1 ++
                format_bool ◦ DF ++
                format_bool ◦ MF ++ format_word ◦ FragmentOffset ++ format_word ◦ TTL ++ format_enum ProtocolTypeCodes ◦ Protocol)%format
                 a env t1 ->
               (format_word ◦ SourceAddress ++ format_word ◦ DestAddress ++ format_list format_word ◦ Options)%format a
                 (addE (snd t1) 16) t2 ->
               (constant (4 + (4 + (8 + (16 + (16 + (1 + (1 + (1 + (13 + (8 + 8))))))))))) a + 16 +
               (fun a0 : IPv4_Packet => 32 + (32 + (| Options a0 |) * 32)) a = n * 8)}}}}.
Proof.
  intros; eexists _, _, _, _; intros.
  split.
  match goal with
         | |- CorrectRefinedDecoder ?monoid _ _ _ _ _ _ _ _ =>
           intros; eapply format_decode_refined_correct_refineEquiv; unfold flip;
             repeat (normalize_step monoid)
         end.
  eapply (sequence_Compose_format_refined_decode_correct H);
    [ intros; apply_rules
      | solve_data_inv
      | intros ].
  match goal with
  | |- CorrectRefinedDecoder ?monoid _ _ _ _ _ _ _ _ =>
    intros; eapply format_decode_refined_correct_refineEquiv; unfold flip
  end.
  eapply EquivFormat_UnderSequence'.
  eapply EquivFormat_trans.
  eapply EquivFormat_compose_map.
  apply EquivFormat_reflexive.
  apply EquivFormat_reflexive.
  eapply (sequence_Compose_format_refined_decode_correct_finish H0).
  intros. apply_rules.
  solve_data_inv.
  solve_data_inv.
  intros; eapply H1.
  solve_data_inv.
  solve_data_inv.
  admit.
  intros.
  unfold sequence_Format at 1 2, ComposeOpt.compose, Bind2 in H3;
    apply unfold_computes in H3; computes_to_inv; subst.



  [ intros; apply_rules
    | try solve_data_inv
      | intros ].
  instantiate (1 := fun n env t =>

                     forall (a : IPv4_Packet) (t1 t2 : ByteString * CacheFormat),
               word 16 ->
               IPv4_Packet_OK a ->
               (format_nat 4 ◦ constant 4 ++
                format_nat 4 ◦ Init.Nat.add 5 ◦ Datatypes.length (A:=word 32) ◦ Options ++
                format_unused_word 8 ++
                format_word ◦ TotalLength ++
                format_word ◦ ID ++
                format_unused_word 1 ++
                format_bool ◦ DF ++
                format_bool ◦ MF ++ format_word ◦ FragmentOffset ++ format_word ◦ TTL ++ format_enum ProtocolTypeCodes ◦ Protocol)%format
                 a env t1 ->
               (format_word ◦ SourceAddress ++ format_word ◦ DestAddress ++ format_list format_word ◦ Options)%format a
                 (addE (snd t1) 16) t2 ->
               (constant (4 + (4 + (8 + (16 + (16 + (1 + (1 + (1 + (13 + (8 + 8))))))))))) a + 16 +
               (fun a0 : IPv4_Packet => 32 + (32 + (| Options a0 |) * 32)) a = n * 8).
  eapply ExtractViewFromRefined; eauto.
  intros.
  apply unfold_computes; intros.



  2: {
       eapply (sequence_Compose_format_refined_decode_correct H).


    (format_nat 4 ◦ constant 4
               ++
               ((format_nat 4 ◦ Init.Nat.add 5) ◦ Datatypes.length (A:=word 32)) ◦ Options)%format.
  admit.
Defined. *)

Arguments andb : simpl never.

(*Hint Extern 4 => eapply aligned_IPv4_Packet_encoded_measure_OK_1.
Hint Extern 4 => eapply aligned_IPv4_Packet_encoded_measure_OK_2. *)

Ltac apply_new_combinator_rule ::=
  match goal with
  | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ _ =>
    eapply compose_IPChecksum_format_correct' with (format1 := fmt1);
    [ exact H
    | repeat calculate_length_ByteString
    | repeat calculate_length_ByteString
    | solve_mod_8
    | solve_mod_8
    |
    | intros; NormalizeFormats.normalize_format; apply_rules ]
  end.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition IPv4_Packet_Header_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.
  synthesize_aligned_decoder.
Defined.

Print Assumptions IPv4_Packet_Header_decoder.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Arguments GetCurrentBytes : simpl never.
Definition IPv4_decoder_impl {sz} v :=
  Eval simpl in (projT1 IPv4_Packet_Header_decoder sz v 0 ()).

Section BP.
  Local Opaque ByteBuffer.of_vector.
  Local Transparent weqb.
  Local Transparent natToWord.
  (* Some example uses of the encoder and decoder functions. *)
  (* A binary version of a packet, sourced directly from the web. *)
  Definition bin_pkt : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0]).

  Definition bin_pkt' : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;0;0;192;168;222;10;192;168;222;1;0;0;0;0]).
End BP.

(* An source version of a packet, different from binary packet above. *)
Definition pkt :=
  {| TotalLength := WO~0~1~1~1~0~1~0~0~0~0~0~0~0~0~0~0;
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Definition bad_pkt :=
  {| TotalLength := wzero _; (* length is too short *)
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Eval vm_compute in (IPv4_decoder_impl bin_pkt).

Local Transparent natToWord.
Local Transparent weqb.
(* This should succeed, *)
Eval compute in
    Ifopt (IPv4_encoder_impl (initialize_Aligned_ByteString 100) pkt)
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* This should fail because the total length field is too short, *)
Eval compute in
    Ifopt (IPv4_encoder_impl (initialize_Aligned_ByteString 100) bad_pkt)
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* Some addition checksum sanity checks. *)
Compute
  match IPv4_decoder_impl bin_pkt with
  | Some (p, _, _) => Some ((wordToN p.(SourceAddress)), wordToN p.(DestAddress))
  | None => None
  end.

Goal match AlignedIPChecksum.calculate_IPChecksum bin_pkt' 0 ()()  with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  reflexivity.
Qed.

Definition pkt' := {|
                    TotalLength := WO~0~1~1~0~0~1~0~0~0~0~0~0~0~0~0~0;
                    ID := WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    DF := false;
                    MF := false;
                    FragmentOffset := WO~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    TTL := WO~0~0~1~0~0~1~1~0;
                    Protocol := Fin.F1;
                    SourceAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~1~0~1~0;
                    DestAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~0~0~0~1;
                    Options := [] |}.

Goal match IPv4_encoder_impl (initialize_Aligned_ByteString 24) pkt'  with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  compute.
  reflexivity.
Qed.
