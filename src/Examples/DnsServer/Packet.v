Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List
        Bedrock.Word
        Bedrock.Memory
        Fiat.QueryStructure.Automation.AutoDB.

Require Export Fiat.Examples.DnsServer.RRecordTypes.

Section QTypes.

  (* DNS packet Query Types are a superset of RR Types. *)
  Definition QTypes :=
    ["TKEY"; (* Transaction Key 	[RFC2930] *)
       "TSIG"; (* Transaction Signature 	[RFC2845] *)
       "IXFR"; (* incremental transfer 	[RFC1995] *)
       "AXFR"; (* transfer of an entire zone 	[RFC1035][RFC5936] *)
       "MAILB"; (* mailbox-related RRs (MB, MG or MR) 	[RFC1035] *)
       "MAILA"; (* mail agent RRs (OBSOLETE - see MX) 	[RFC1035] *)
       "STAR" (*A request for all records the server/cache has available 	[RFC1035][RFC6895] *)
    ]%vector.

  Definition QType := BoundedString (Vector.append RRecordTypes QTypes)%vector.

  Definition QType_inj (rr : RRecordType) : QType :=
    BoundedIndex_injR rr.

  Definition beq_QType (a b : QType) : bool :=
    BoundedIndex_beq a b.

  Definition QType_dec (a b : QType) :=
    BoundedIndex_eq_dec a b.

  Lemma beq_QType_sym :
    forall rrT rrT', beq_QType rrT rrT' = beq_QType rrT' rrT.
  Proof.
    intros; eapply BoundedIndex_beq_sym.
  Qed.

  Lemma beq_QType_dec :
    forall a b, ?[QType_dec a b] = beq_QType a b.
  Proof.
    intros; find_if_inside; subst.
    eauto using BoundedIndex_beq_refl.
    symmetry; eapply BoundedIndex_beq_neq_dec; eauto.
  Qed.

  Coercion QType_inj : RRecordType >-> QType.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_QType :
    Query_eq QType := {| A_eq_dec := QType_dec |}.

  Definition QType_match (rtype : RRecordType) (qtype : QType) :=
    qtype = ``"STAR" \/ qtype = rtype.

End QTypes.

Section RRecordClass.

  Definition RRecordClasses :=
    [ "Internet"; (* (IN) 	[RFC1035] *)
        "Chaos"; (* (CH) 	[D. Moon, "Chaosnet", A.I. Memo 628, Massachusetts Institute of Technology Artificial Intelligence Laboratory, June 1981.] *)
        "Hesiod" (* (HS) 	[Dyer, S., and F. Hsu, "Hesiod", Project Athena Technical Plan - Name Service, April 1987.] *)
    ]%vector.

  Definition RRecordClass := BoundedString RRecordClasses.

  Definition beq_RRecordClass (a b : RRecordClass) : bool
    := BoundedIndex_beq a b.

  Definition RRecordClass_dec (a b : RRecordClass) :=
    BoundedIndex_eq_dec a b.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordClass :
    Query_eq RRecordClass := {| A_eq_dec := RRecordClass_dec |}.

  (* DNS Packet Question Classes *)
  Definition QClass :=
    BoundedString (Vector.append RRecordClasses ["Any"]%vector).

  Definition QClass_inj (qclass : RRecordClass) : QClass :=
    BoundedIndex_injR qclass.

  Definition beq_QClass (a b : QClass) : bool
    := BoundedIndex_beq a b.

  Definition QClass_dec (a b : QClass) :=
    BoundedIndex_eq_dec a b.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_QClass :
    Query_eq QClass := {| A_eq_dec := QClass_dec |}.

End RRecordClass.

Section ResponseCode.

  Definition ResponseCodes :=
    ["NoError";  (* No Error [RFC1035] *)
       "FormErr";  (* Format Error [RFC1035] *)
       "ServFail"; (* Server Failure [RFC1035] *)
       "NXDomain"; (* Non-Existent  Domain 	[RFC1035] *)
       "NotImp";   (* Not Implemented [RFC1035] *)
       "Refused";  (* Query Refused [RFC1035] *)
       "YXDomain"; (* Name Exists when it should not [RFC2136][RFC6672] *)
       "YXRRSet";  (* RR Set Exists when it should not 	[RFC2136] *)
       "NXRRSet";  (* RR Set that should exist does not 	[RFC2136] *)
       "NotAuth";  (* Server Not Authoritative for zone 	[RFC2136] *)
       "NotAuth";  (* Not Authorized [RFC2845] *)
       "NotZone" 	 (* Name not  contained in zone 	[RFC2136] *)
    ]%vector.

  Definition ResponseCode := BoundedString ResponseCodes.

  Definition beq_ResponseCode (a b : ResponseCode) : bool
    := BoundedIndex_beq a b.

  Definition ResponseCode_dec (a b : ResponseCode) :=
    BoundedIndex_eq_dec a b.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_ResponseCode :
    Query_eq ResponseCode := {| A_eq_dec := ResponseCode_dec |}.
End ResponseCode.

Section OpCode.

  Definition OpCodes :=
    ["Query";    (* RFC1035] *)
       "IQuery"; (* Inverse Query  OBSOLETE) [RFC3425] *)
       "Status"; (* [RFC1035] *)
       "Notify"  (* [RFC1996] [RFC2136] *)
    ]%vector.

  Definition OpCode := BoundedString OpCodes.

  Definition beq_OpCode (a b : OpCode) : bool
    := BoundedIndex_beq a b.

  Definition OpCode_dec (a b : OpCode) :=
    BoundedIndex_eq_dec a b.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_OpCode :
    Query_eq OpCode := {| A_eq_dec := OpCode_dec |}.
End OpCode.

Section Packet.

  (* The question section of a DNS packet. *)
  Definition question :=
    @Tuple <
    "qname" :: DomainName,
    "qtype" :: QType,
    "qclass" :: QClass >%Heading.
  (* ["google", "com"] *)

  (* DNS Resource Records. *)
  Definition sRRecords := "ResourceRecords".
  Definition sNAME := "Name".
  Definition sTTL := "TTL".
  Definition sCLASS := "Class".
  Definition sTYPE := "Type".
  Definition sRDATA := "rdata".
  Definition sRLENGTH := "rlength".

  Definition resourceRecordHeading :=
    < sNAME :: DomainName,
    sTTL :: timeT,
    sCLASS :: RRecordClass,
    sTYPE :: RRecordType,
    sRDATA :: DomainName>%Heading.

  (* Binary Format of DNS Header:
                              1  1  1  1  1  1
0  1  2  3  4  5  6  7  8  9  0  1  2  3  4  5
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|                      ID                       |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|QR|   Opcode  |AA|TC|RD|RA|   Z    |   RCODE   |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|                    QDCOUNT                    |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|                    ANCOUNT                    |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|                    NSCOUNT                    |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
|                    ARCOUNT                    |
+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
   *)

  (* DNS Packet Layout:
+---------------------+
|        Header       |
+---------------------+
|       Question      |
+---------------------+
|        Answer       |
+---------------------+
|      Authority      |
+---------------------+
|      Additional     |
+---------------------+
   *)

  Definition resourceRecord := @Tuple resourceRecordHeading.

  Arguments Tuple [_%Heading] .

  Definition packet :=
    @Tuple < "id" :: word 16, (* 16 bit Word. *)
    "QR" :: word 1, (* is packet a query (0), or a response (1) *)
    "Opcode" :: OpCode, (* kind of query in packet *)
    "AA" :: word 1, (* is responding server authorative *)
    "TC" :: word 1, (* is packet truncated *)
    "RD" :: word 1, (* are recursive queries desired *)
    "RA" :: word 1, (* are recursive queries supported by responding server *)
    "RCODE" :: ResponseCode, (* response code *)
    "questions" :: question, (* `list question` in case we can have multiple questions? *)
    "answers" :: list resourceRecord,
    "authority" :: list resourceRecord,
    "additional" :: list resourceRecord >.

  Definition buildempty (is_authority : bool)
             (rcode : ResponseCode)
             (p : packet) :=
    p ○ [ "AA" ::= WS is_authority WO; (* Update Authority field *)
            "QR" ::= WS true WO; (* Set response flag to true *)
            "RCODE" ::= rcode;
            "answers" ::= [ ];
            "authority"  ::= [ ];
            "additional" ::= [ ] ].

  (* add a resource record to a packet's answers *)
  Definition add_answer (p : packet) (t : resourceRecord) :=
    p ○ [o !! "answers" / t :: o].

  (* add a resource record authority to a packet's authorities
   (ns = name server). *)
  Definition add_ns (p : packet) (t : resourceRecord) :=
    p ○ [o !! "authority" / t :: o].

  (* combine with above? *)
  Definition add_additional (p : packet) (t : resourceRecord) :=
    p ○ [o !! "additional" / t :: o].

  Definition updateRecords (p : packet) answers' authority' additional' :=
    p ○ ["answers" ::= answers';
           "authority" ::= authority';
           "additional" ::= additional'].

  Definition get_name (r : resourceRecord) := r!sNAME.
  Definition name_length (r : resourceRecord) := List.length (get_name r).

  Definition isQuestion (p : packet) :=
    match p!"answers", p!"authority", p!"additional" with
    | nil, nil, nil => true
    | _, _, _ => false
    end.

  Definition isAnswer (p : packet) := negb (is_empty (p!"answers")).

  Definition isReferral (p : packet) :=
    is_empty (p!"answers")
             && (negb (is_empty (p!"authority")))
             && (negb (is_empty (p!"additional"))).

  Definition add_answers := List.fold_left add_answer.
  Definition add_nses := List.fold_left add_ns.
  Definition add_additionals := List.fold_left add_additional.

End Packet.
