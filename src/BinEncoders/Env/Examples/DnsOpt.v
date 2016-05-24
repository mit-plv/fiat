Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Examples.DnsServer.Packet
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
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
        Fiat.BinEncoders.Env.Lib2.SteppingListOpt.

Require Import
        Bedrock.Word.

Import Coq.Vectors.VectorDef.VectorNotations.

Section DnsPacket.

  Open Scope Tuple_scope.

  Variable bin : Type.
  Variable cache : Cache.
  Variable cacheAddNat : CacheAdd cache nat.

  Variable transformer : Transformer bin.
  Variable transformerUnit : TransformerUnitOpt transformer bool.

  Variable QType_Ws : t (word 16) 66.
  Variable QClass_Ws : t (word 16) 4.
  Variable RRecordType_Ws : t (word 16) 59.
  Variable RRecordClass_Ws : t (word 16) 3.
  Variable Opcode_Ws : t (word 4) 4.
  Variable RCODE_Ws : t (word 4) 12.

  Definition encode_question (q : question) :=
       encode_string q!"qname"
  Then encode_enum QType_Ws q!"qtype"
  Then encode_enum QClass_Ws q!"qclass"
  Done.

  Definition encode_SOA_RDATA (soa : SOA_RDATA) :=
       encode_string soa!"sourcehost"
  Then encode_string soa!"contact_email"
  Then encode_word soa!"serial"
  Then encode_word soa!"refresh"
  Then encode_word soa!"retry"
  Then encode_word soa!"expire"
  Then encode_word soa!"minTTL"
  Done.

  Definition encode_WKS_RDATA (wks : WKS_RDATA) :=
       encode_word wks!"Address"
  Then encode_word wks!"Protocol"
  Then encode_list encode_word wks!"Bit-Map"
  Done.

  Definition encode_HINFO_RDATA (hinfo : HINFO_RDATA) :=
       encode_string hinfo!"CPU"
  Then encode_string hinfo!"OS"
  Done.

  Definition encode_MX_RDATA (mx : MX_RDATA) :=
       encode_word mx!"Preference"
  Then encode_string mx!"Exchange"
  Done.

  Definition encode_rdata :=
  encode_SumType ResourceRecordTypeTypes
  (icons encode_word
  (icons (encode_string)
  (icons (encode_string)
  (icons encode_SOA_RDATA
  (icons encode_WKS_RDATA
  (icons (encode_string)
  (icons encode_HINFO_RDATA
  (icons (encode_string)
  (icons encode_MX_RDATA (icons encode_string inil)))))))))).

  Definition encode_resource (r : resourceRecord) :=
       encode_string r!sNAME
  Then encode_enum RRecordType_Ws r!sTYPE
  Then encode_enum RRecordClass_Ws r!sCLASS
  Then encode_word r!sTTL
  Then encode_rdata r!sRDATA
  Done.

  Definition encode_packet (p : packet) :=
       encode_word p!"id"
  Then encode_word (WS p!"QR" WO)
  Then encode_enum Opcode_Ws p!"Opcode"
  Then encode_word (WS p!"AA" WO)
  Then encode_word (WS p!"TC" WO)
  Then encode_word (WS p!"RD" WO)
  Then encode_word (WS p!"RA" WO)
  Then encode_word (WS false (WS false (WS false WO))) (* 3 bits reserved for future use *)
  Then encode_enum RCODE_Ws p!"RCODE"
  Then encode_nat 16 1 (* length of question field *)
  Then encode_nat 16 (|p!"answers"|)
  Then encode_nat 16 (|p!"authority"|)
  Then encode_nat 16 (|p!"additional"|)
  Then encode_question p!"question"
  Then encode_list encode_resource p!"answers"
  Then encode_list encode_resource p!"additional"
  Then encode_list encode_resource p!"authority"
  Done.

  Definition packet_decoder
  : { decode | encode_decode_correct_f cache transformer (fun _ => True) encode_packet decode }.
  Proof.
    unfold encode_decode_correct_f.
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
