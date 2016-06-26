Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
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

Ltac apply_compose :=
  intros;
  match goal with
    H : cache_inv_Property ?P ?P_inv |- _ =>
    first [eapply (compose_encode_correct_no_dep H); clear H
          | eapply (compose_encode_correct H); clear H
          | eapply (composeIf_encode_correct H); clear H;
            [ |
              | solve [intros; intuition (eauto with bin_split_hints) ]
              | solve [intros; intuition (eauto with bin_split_hints) ] ]
          ]
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac shelve_inv :=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat destruct H';
  match goal with
  | H : ?P data |- ?P_inv' =>
    is_evar P;
    let P_inv' := (eval pattern data in P_inv') in
    let P_inv := match P_inv' with ?P_inv data => P_inv end in
    let new_P_T := type of P in
    makeEvar new_P_T
             ltac:(fun new_P =>
                     unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
  end.

Ltac solve_data_inv :=
    first [ simpl; intros; exact I
| shelve_inv ].

Definition transformer : Transformer ByteString := ByteStringTransformer.

(* Start Example Derivation. *)

Definition ARPPacket :=
  @Tuple <"HardType" :: EnumType ["Ethernet"; "802"; "Chaos"],
          "ProtType" :: EnumType ["IPv4"; "IPv6"], (* Overlaps with etherType. *)
          "Operation" :: EnumType ["Request";
                                   "Reply";
                                   "RARP Request";
                                   "RARP Reply"],
          "SenderHardAddress" :: list char,
          "SenderProtAddress" :: list char,
          "TargetHardAddress" :: list char,
          "TargetProtAddress" :: list char >.

Definition HardTypeCodes : Vector.t (word 16) 3 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1
  ].

Definition EtherTypeCodes : Vector.t (word 16) 2 :=
  [WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0;
   WO~1~0~0~0~0~1~1~0~1~1~0~1~1~1~0~1
  ].

Definition HardSizeCodes : Vector.t char 3 :=
  [WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~1~0
  ].

Definition ProtSizeCodes : Vector.t char 2 :=
  [WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~1~0~0~0~0 ].

Definition OperationCodes : Vector.t (word 16) 4 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
  ].

Definition encode_ARPPacket_Spec (arp : ARPPacket) :=
          encode_enum_Spec HardTypeCodes arp!"HardType"
    ThenC encode_enum_Spec EtherTypeCodes arp!"ProtType"
    ThenC encode_word_Spec HardSizeCodes[@arp!"HardType"]
    ThenC encode_word_Spec ProtSizeCodes[@arp!"ProtType"]
    ThenC encode_enum_Spec OperationCodes arp!"Operation"
    ThenC encode_list_Spec encode_word_Spec arp!"SenderHardAddress"
    ThenC encode_list_Spec encode_word_Spec arp!"SenderProtAddress"
    ThenC encode_list_Spec encode_word_Spec arp!"TargetHardAddress"
    ThenC encode_list_Spec encode_word_Spec arp!"TargetProtAddress"
    DoneC.

Definition ARP_Packet_OK (arp : ARPPacket) :=
  (|arp!"SenderHardAddress"|) = wordToNat HardSizeCodes[@arp!"HardType"]
  /\ (|arp!"SenderProtAddress"|) = wordToNat ProtSizeCodes[@arp!"ProtType"]
  /\ (|arp!"TargetHardAddress"|) = wordToNat HardSizeCodes[@arp!"HardType"]
  /\ (|arp!"TargetProtAddress"|) = wordToNat ProtSizeCodes[@arp!"ProtType"].

Definition ARPPacket_decoder
  : { decodePlusCacheInv |
      exists P_inv,
      (cache_inv_Property (snd decodePlusCacheInv) P_inv
       -> encode_decode_correct_f _ transformer ARP_Packet_OK (fun _ b => True)
                                  encode_ARPPacket_Spec
                                  (fst decodePlusCacheInv) (snd decodePlusCacheInv))
      /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  eexists (_, _); eexists _; split; simpl.
  intros.
  apply_compose; pose_string_ids.
  eapply Enum_decode_correct.
  Discharge_NoDupVector.
  solve_data_inv.
  simpl; intros; exact I.
  apply_compose.
  eapply Enum_decode_correct.
  Discharge_NoDupVector.
  solve_data_inv.
  simpl; intros; exact I.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  simpl; intros; exact I.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  simpl; intros; exact I.
  apply_compose.
  eapply Enum_decode_correct.
  Discharge_NoDupVector.
  solve_data_inv.
  simpl; intros; exact I.
  apply_compose.
  intro; eapply FixList_decode_correct.
  revert H4; eapply Word_decode_correct.
  unfold ARP_Packet_OK; intros; intuition.
  pose_string_ids.
  rewrite H8 in H4; eauto.
  simpl; intros; eapply FixedList_predicate_rest_True.
  apply_compose.
  intro; eapply FixList_decode_correct.
  revert H5; eapply Word_decode_correct.
  unfold ARP_Packet_OK; intros; intuition.
  pose_string_ids.
  rewrite H9 in H5; eauto.
  simpl; intros; eapply FixedList_predicate_rest_True.
  apply_compose.
  intro; eapply FixList_decode_correct.
  revert H6; eapply Word_decode_correct.
  unfold ARP_Packet_OK; intros; intuition.
  pose_string_ids.
  rewrite H12 in H15; eauto.
  simpl; intros; eapply FixedList_predicate_rest_True.
  apply_compose.
  intro; eapply FixList_decode_correct.
  revert H7; eapply Word_decode_correct.
  unfold ARP_Packet_OK; intros; intuition.
  pose_string_ids.
  rewrite H13 in H19; eauto.
  simpl; intros; eapply FixedList_predicate_rest_True.
  Opaque Vector.nth.
  simpl; intros.
  unfold encode_decode_correct_f; intuition eauto.
  instantiate
    (1 := fun p b env => if weq (proj1) (HardSizeCodes[@proj]) then _ p b env else None).
  destruct (weq proj1 HardSizeCodes[@proj]);
    try congruence.
  instantiate
    (1 := fun p b env => if weq (proj2) (ProtSizeCodes[@proj0]) then _ p b env else None).
  destruct (weq proj2 ProtSizeCodes[@proj0]);
    try congruence.
  destruct data as [? [? [? [? [? [? [? [ ] ] ] ] ] ] ] ];
    unfold GetAttribute, GetAttributeRaw in *;
    simpl in *.
  computes_to_inv; injections; subst; simpl.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  eexists env'; simpl; intuition eauto.
  match goal with
    |- ?f ?a ?b ?c = ?P =>
    let P' := (eval pattern a, b, c in P) in
    let f' := match P' with ?f a b c => f end in
    try unify f f'; try reflexivity
  end.
  simpl in H12; repeat find_if_inside; injections;
    try discriminate; injections.
  eassumption.
  simpl in H12; repeat find_if_inside; try discriminate.
  eexists _; eexists tt;
    intuition eauto; injections; eauto using idx_ibound_eq;
      try match goal with
            |-  ?data => destruct data;
                           simpl in *; eauto
          end.
  destruct env; computes_to_econstructor.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  reflexivity.
  unfold ARP_Packet_OK, GetAttribute, GetAttributeRaw; simpl;
    intuition eauto.
  repeat (instantiate (1 := fun _ => True)).
  unfold cache_inv_Property; intuition.
Defined.

Definition ARP_Packet_decoder :=
  Eval simpl in projT1 ARPPacket_decoder.
Print ARP_Packet_decoder.
