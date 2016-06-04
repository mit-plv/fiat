Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Examples.DnsServer.Packet
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt.

Require Import
        Bedrock.Word.

Import Coq.Vectors.VectorDef.VectorNotations.

Section DnsPacket.

  Open Scope Tuple_scope.

  Variable cache : Cache.
  Variable cacheAddNat : CacheAdd cache nat.
  Variable cacheAddDNPointer : CacheAdd cache (string * pointerT).
  Variable cacheGetDNPointer : CacheGet cache string pointerT.
  Variable cachePeekDNPointer : CachePeek cache pointerT.

  Definition transformer : Transformer bin := btransformer.
  Variable transformerUnit : TransformerUnitOpt transformer bool.

  Variable QType_Ws : t (word 16) 66.
  Variable QType_Ws_OK : NoDupVector QType_Ws.
  Variable QClass_Ws : t (word 16) 4.
  Variable QClass_Ws_OK : NoDupVector QClass_Ws.
  Variable RRecordType_Ws : t (word 16) 59.
  Variable RRecordType_Ws_OK : NoDupVector  RRecordType_Ws.
  Variable RRecordClass_Ws : t (word 16) 3.
  Variable RRecordClass_Ws_OK : NoDupVector  RRecordClass_Ws.
  Variable Opcode_Ws : t (word 4) 4.
  Variable Opcode_Ws_OK : NoDupVector  Opcode_Ws.
  Variable RCODE_Ws : t (word 4) 12.
  Variable RCODE_Ws_OK : NoDupVector  RCODE_Ws.

  Definition encode_question_Spec (q : question) :=
       encode_DomainName_Spec q!"qname"
  Then encode_enum_Spec QType_Ws q!"qtype"
  Then encode_enum_Spec QClass_Ws q!"qclass"
  Done.

  Definition encode_SOA_RDATA_Spec (soa : SOA_RDATA) :=
       encode_DomainName_Spec soa!"sourcehost"
  Then encode_DomainName_Spec soa!"contact_email"
  Then encode_word_Spec soa!"serial"
  Then encode_word_Spec soa!"refresh"
  Then encode_word_Spec soa!"retry"
  Then encode_word_Spec soa!"expire"
  Then encode_word_Spec soa!"minTTL"
  Done.

  Definition encode_WKS_RDATA_Spec (wks : WKS_RDATA) :=
       encode_word_Spec wks!"Address"
  Then encode_word_Spec wks!"Protocol"
  Then (encode_list_Spec encode_word_Spec wks!"Bit-Map")
  Done.

  Definition encode_HINFO_RDATA_Spec (hinfo : HINFO_RDATA) :=
       encode_DomainName_Spec hinfo!"CPU" (* Should be character string!*)
  Then encode_DomainName_Spec hinfo!"OS" (* Should be character string!*)
  Done.

  Definition encode_MX_RDATA_Spec (mx : MX_RDATA) :=
       encode_word_Spec mx!"Preference"
  Then encode_DomainName_Spec mx!"Exchange"
  Done.

  Definition encode_rdata_Spec :=
  encode_SumType_Spec ResourceRecordTypeTypes
  (icons encode_word_Spec
  (icons (encode_string_Spec)
  (icons (encode_string_Spec)
  (icons encode_SOA_RDATA_Spec
  (icons encode_WKS_RDATA_Spec
  (icons (encode_string_Spec)
  (icons encode_HINFO_RDATA_Spec
  (icons (encode_string_Spec)
  (icons encode_MX_RDATA_Spec (icons encode_string_Spec inil)))))))))).

  Definition encode_resource_Spec(r : resourceRecord) :=
       encode_DomainName_Spec r!sNAME
  Then encode_enum_Spec RRecordType_Ws r!sTYPE
  Then encode_enum_Spec RRecordClass_Ws r!sCLASS
  Then encode_word_Spec r!sTTL
  Then encode_rdata_Spec r!sRDATA
  Done.

  Definition encode_packet_Spec (p : packet) :=
       encode_word_Spec p!"id"
  Then encode_word_Spec (WS p!"QR" WO)
  Then encode_enum_Spec Opcode_Ws p!"Opcode"
  Then encode_word_Spec (WS p!"AA" WO)
  Then encode_word_Spec (WS p!"TC" WO)
  Then encode_word_Spec (WS p!"RD" WO)
  Then encode_word_Spec (WS p!"RA" WO)
  Then encode_word_Spec (WS false (WS false (WS false WO))) (* 3 bits reserved for future use *)
  Then encode_enum_Spec RCODE_Ws p!"RCODE"
  Then encode_nat_Spec 16 1 (* length of question field *)
  Then encode_nat_Spec 16 (|p!"answers"|)
  Then encode_nat_Spec 16 (|p!"authority"|)
  Then encode_nat_Spec 16 (|p!"additional"|)
  Then encode_question_Spec p!"question"
  Then (encode_list_Spec encode_resource_Spec p!"answers")
  Then (encode_list_Spec encode_resource_Spec p!"additional")
  Then (encode_list_Spec encode_resource_Spec p!"authority")
  Done.

  Ltac normalize_compose :=
    eapply encode_decode_correct_refineEquiv;
    [ intros ? ?; symmetry;
      repeat first [ etransitivity; [apply refineEquiv_compose_compose | ]
                   | etransitivity; [apply refineEquiv_compose_Done | ]
                   | apply refineEquiv_under_compose ];
      intros; higher_order_reflexivity
        | ].

  Definition packet_decoder
    : { decodePlusCacheInv |
        exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
        -> encode_decode_correct_f cache transformer (fun _ => True) encode_packet_Spec (fst decodePlusCacheInv) (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
  Proof.
    eexists (_, _); eexists _; split; simpl.
    intros; normalize_compose.

    Ltac apply_compose :=
      intros;
      match goal with
        H : cache_inv_Property ?P ?P_inv |- _ =>
        eapply (compose_encode_correct H); clear H
      end.
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | apply_compose].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].

    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | apply_compose ].
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | apply_compose ].
    Ltac foo' := first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | intros;
            match goal with
              |- encode_decode_correct_f
                   _ _ _
                   (encode_list_Spec _) _ _ =>
              apply FixList_decode_correct end
          | apply_compose ].
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    eapply SumType_decode_correct.
    instantiate (2 := (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))).
    Require Import Fiat.Common.IterateBoundedIndex.
    instantiate (13 := @Iterate_Dep_Type_equiv' 10 _
                                               (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))

                ).
    instantiate (12 := @Iterate_Dep_Type_equiv' 10 _
                                               (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))

                ).
    intro; pattern idx.
    eapply Iterate_Ensemble_equiv' with (idx := idx); simpl.
    apply Build_prim_and.
    foo'.
    apply Build_prim_and.
    apply String_decode_correct.
    apply Build_prim_and.
    apply String_decode_correct.
    apply Build_prim_and.
    {foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    intros.
    unfold encode_decode_correct_f; intuition eauto.
    destruct data as [? [? [? [? [? [? [? [ ] ] ] ] ] ] ] ].
    unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
    eexists; intuition eauto; simpl.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    injections.
    instantiate (1 := fun data => ((fun domain : string => ValidDomainName domain /\ (String.length domain > 0)%nat)
                                     data!"contact_email")
                                  /\ ((fun domain : string => ValidDomainName domain /\ (String.length domain > 0)%nat)
                                       data!"sourcehost")
                ).
    simpl.
    solve_predicate.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    intros; intuition.
    simpl; intros; intuition.
    }
    apply Build_prim_and.
    {foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    foo'.
    revert H21; foo'.
    intros.
    unfold encode_decode_correct_f; intuition eauto.
    destruct data as [? [? [? [ ] ] ] ].
    unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
    eexists; intuition eauto; simpl.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    injections.
    solve_predicate.

    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    simpl; intros; intuition eauto.
    instantiate (1 := 0); admit.
    (* Need to find proper values for this field from RFC 1010*)
    injections; eauto.
    injections; eauto.
    }
    apply Build_prim_and.
    apply String_decode_correct.
    apply Build_prim_and.
    {foo'.
     foo'.
     foo'.
     foo'.
     intros.
     unfold encode_decode_correct_f; intuition eauto.
     destruct data as [? [? [ ] ] ].
     unfold GetAttribute, GetAttributeRaw in *.
     subst; simpl.
      computes_to_inv; injections.
    eexists; intuition eauto; simpl.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    injections.
    instantiate (1 := fun data => ((fun domain : string => ValidDomainName domain /\ (String.length domain > 0)%nat)
                                     data!"OS")
                                  /\ ((fun domain : string => ValidDomainName domain /\ (String.length domain > 0)%nat)
                                     data!"CPU")
                )
    .
    solve_predicate.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    simpl; intros; intuition eauto.
    simpl; intros; intuition eauto.
    }
    apply Build_prim_and.
    apply String_decode_correct.
    apply Build_prim_and.
    { foo'.
      foo'.
      foo'.
      foo'.
     unfold encode_decode_correct_f; intuition eauto.
     destruct data as [? [? [ ] ] ].
     unfold GetAttribute, GetAttributeRaw in *.
     subst; simpl.
      computes_to_inv; injections.
    eexists; intuition eauto; simpl.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    instantiate (1 := fun data => ((fun domain : string => ValidDomainName domain /\ (String.length domain > 0)%nat)
                                     data!"Exchange")).
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    simpl; intros; intuition eauto.
    simpl; intros; intuition eauto.
    }
    apply Build_prim_and.
    apply String_decode_correct.
    eauto.
    intros.
    { unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [? [? [? [ ] ] ] ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    solve_predicate.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    }
    simpl; intros; intuition eauto.
    subst.
    reflexivity.
    simpl.

    admit. (* Contact Emails should be character strings. *)
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.

    apply H.
    eapply String_decode_correct.
    eapply compose_encode_correct.
    revert H; apply_compose.

    unfold Iterate_Dep_Type_equiv'; simpl.
    simpl.
    foo'.

    foo'.


    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].



    intros; intuition; subst.
    unfold encode_decode_correct_f; intuition eauto.
    destruct data as [? [? [? [ ] ] ] ]; simpl in *.
    unfold GetAttribute, GetAttributeRaw in *; simpl in *;
      subst.
    computes_to_inv; injections.
    eexists; intuition eauto; simpl.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    solve_predicate.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.

    simpl; eauto.
    instantiate (1 := fun _ => False); admit.
    admit.
    simpl; eauto.
    admit.
    simpl; intros; eauto.

    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | apply_compose ].








    apply_compose.
    eapply Word_decode_correct.
    apply_compose.
    eapply Word_decode_correct.
    apply_compose.
    eapply Enum_decode_correct; eauto.
    apply_compose.

    intros; eapply compose_encode_correct; simpl.
    eapply Word_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Word_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Word_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Word_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Word_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Enum_decode_correct.
    Focus 3.
    intros; eapply compose_encode_correct; simpl.
    eapply Nat_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Nat_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Nat_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Nat_decode_correct.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    intros; eapply compose_encode_correct; simpl.
    intros; eapply String_decode_correct; simpl.
    Focus 2.
    intros; eapply compose_encode_correct; simpl.
    eapply Enum_decode_correct; eauto.
    Focus 2.
    intros.
    intros; eapply compose_encode_correct; simpl.
    eapply Enum_decode_correct; eauto.
    Focus 2.
    intros; intuition; subst.
    unfold encode_decode_correct_f; intuition eauto.
    destruct data as [? [? [? [ ] ] ] ]; simpl in *.
    unfold GetAttribute, GetAttributeRaw in *; simpl in *;
      subst.
    computes_to_inv; injections.
    eexists; intuition eauto; simpl.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
    end.
    injections; eauto.
    eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    injections; eauto.
    solve_predicate.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    instantiate (1 := fun _ => False); admit.
    simpl; eauto.
    instantiate (1 := fun _ => False); admit.
    admit.
    simpl; eauto.
    admit.
    simpl; intros; eauto.


    Show Existentials.
    instantiate (1 := fun a b c => Some ().
    unfold transform; simpl.

    Show Existentials.
    eapply eapply encode_decode_enum

    destruct data; simpl in *.

    computes_to_inv; subst.
    eexists; intuition.


    repeat destruct data; simpl in *
    intros; eapply Enum_decode_correct; simpl.
    intros; repeat split; intros.
    intuition; subst.





    intros; eapply compose_encode_correct; simpl.


    simpl.
    eapply Nat_decode_correct.





    eapply Enum_decode_correct.



    intros.
    eapply compose_encode_correct.
    eapply Word_decode_correct.

  Admitted.
End DnsPacket.
    (*
    eexists.

    eapply compose_encode_correct.
      eapply Word_decode_correct.
      solve_predicate. intro.

      eapply compose_encode_correct.
      eapply Word_decode_correct.
      solve_predicate. intro.

      eapply compose_encode_correct.
      eapply encode_decode_enum.
      eapply Word_decode_correct.
      solve_predicate. intro.

    eapply compose_encode_correct.
    eapply Word_decode_correct.
      solve_predicate. intro.

      eapply compose_encode_correct.
      eapply Word_decode_correct.
      solve_predicate. intro.

    eapply compose_encode_correct.
    eapply Word_decode_correct.
      solve_predicate. intro.

    eapply compose_encode_correct.
    eapply Word_decode_correct.
      solve_predicate. intro.

    eapply compose_encode_correct.
    eapply Word_decode_correct.
      solve_predicate. intro.

    eapply compose_encode_correct.
    eapply encode_decode_enum.
    eapply Word_decode_correct.
      solve_predicate. intro.

    eapply compose_encode_correct.
      eapply Nat_decode_correct.
      admit. intro.

    eapply compose_encode_correct.
      eapply Nat_decode_correct.
      admit. intro.

    eapply compose_encode_correct.
      eapply Nat_decode_correct.
      admit. intro.

    eapply compose_encode_correct.
    eapply Nat_decode_correct.
    admit. intro.

    eapply compose_encode_correct.
  Abort.
  { unfold encode_question.
      eapply compose_encode_correct.

      eapply FixList_decode_correct.
      eapply String_decode_correct.
      simpl.
      solve_predicate.
    eapply Nat_decode_correct.
    admit. intro.

    solve_predicate. intro.

    eapply compose_encode_correct.
      eapply encode_decode_nat.
      solve_predicate. intro.

    eapply compose_encode_correct.
      instantiate (2:=fun _ => True).
      eapply compose_encode_correct.
        eapply encode_decode_list. eapply encode_decode_string.
        solve_predicate. intro.

      eapply compose_encode_correct.
        eapply encode_decode_enum. eapply encode_decode_word.
        solve_predicate. intro.

      eapply compose_encode_correct.
        eapply encode_decode_enum. eapply encode_decode_word.
        solve_predicate. intro.

      intros ? ? ? ? data ? ? ? ?.
      instantiate (1:=fun l b e => (_ l, b, e)).
      repeat destruct data as [? data].
      intros. simpl in *.
      cbv in H0.
      repeat match goal with
             | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
             | H : _ /\ _ |- _ => inversion H; subst; clear H
             end.
      intuition eauto. symmetry. eauto.
      solve_predicate. intro.

    eapply compose_encode_correct.
      instantiate (2:=fun _ => True).
      eapply encode_decode_list.
      eapply compose_encode_correct.
        eapply encode_decode_list. eapply encode_decode_string.
        solve_predicate. intro.

      eapply compose_encode_correct.
        eapply encode_decode_enum. eapply encode_decode_word.
        solve_predicate. intro.

      eapply compose_encode_correct.
        eapply encode_decode_enum. eapply encode_decode_word.
        solve_predicate. intro.

      eapply compose_encode_correct.
        eapply encode_decode_word.
        solve_predicate. intro.

      intros ? ? ? ? data ? ? ? ?. Show Existentials.
      instantiate (1:=fun l b e => (<"Name" :: proj13,
                                     sTYPE :: proj14,
                                     sCLASS :: proj15,
                                     sTTL :: l>, b, e)).
      simpl. intros. repeat match goal with
                            | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
                            | H : _ /\ _ |- _ => inversion H; subst; clear H
                            end. admit.
      solve_predicate. intro. *)
