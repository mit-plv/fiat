Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List
        Bedrock.Word
        Bedrock.Memory
        Fiat.QueryStructure.Automation.AutoDB.

Section RRecordTypes.
  (* Enumeration of the Resource Record Types. *)
  Definition RRecordTypes :=
    ["A"; 	(* host address 	[RFC1035] *)
       "NS"; (*  authoritative name server 	[RFC1035] *)
       "MD"; (* mail destination (OBSOLETE - use MX) 	[RFC1035] *)
       "MF"; (* mail forwarder (OBSOLETE - use MX) 	[RFC1035] *)
       "CNAME"; (* e canonical name for an alias 	[RFC1035] *)
       "SOA"; (* rks the start of a zone of authority 	[RFC1035] *)
       "MB"; (* mailbox domain name (EXPERIMENTAL) 	[RFC1035] *)
       "MG"; (* mail group member (EXPERIMENTAL) 	[RFC1035] *)
       "MR"; (* mail rename domain name (EXPERIMENTAL) 	[RFC1035] *)
       "NULL"; (* null RR (EXPERIMENTAL) 	[RFC1035] *)
       "WKS"; (* well known service description 	[RFC1035] *)
       "PTR"; (* domain name pointer 	[RFC1035] *)
       "HINFO"; (* host information 	[RFC1035] *)
       "MINFO"; (* mailbox or mail list information 	[RFC1035] *)
       "MX"; (* mail exchange 	[RFC1035] *)
       "TXT"; (* text strings 	[RFC1035] *)
       "RP"; (* for Responsible Person 	[RFC1183] *)
       "AFSDB"; (* for AFS Data Base location 	[RFC1183][RFC5864] *)
       "X25"; (* for X.25 PSDN address 	[RFC1183] *)
       "ISDN"; (* for ISDN address 	[RFC1183] *)
       "RT"; (* for Route Through 	[RFC1183] *)
       "NSAP"; (* for NSAP address, NSAP style A record 	[RFC1706] *)
       "NSAPPTR"; (* for domain name pointer, NSAP style 	[RFC1348][RFC1637][RFC1706] *)
       "SIG"; (* for security signature 	[RFC4034][RFC3755][RFC2535][RFC2536][RFC2537][RFC2931][RFC3110][RFC3008] *)
       "KEY"; (* for security key 	[RFC4034][RFC3755][RFC2535][RFC2536][RFC2537][RFC2539][RFC3008][RFC3110] *)
       "PX"; (* X.400 mail mapping information 	[RFC2163] *)
       "GPOS"; (* Geographical Position 	[RFC1712] *)
       "AAAA"; (* IP6 Address 	[RFC3596] *)
       "LOC"; (* Location Information 	[RFC1876] *)
       "NXT"; (* Next Domain (OBSOLETE) 	[RFC3755][RFC2535] *)
       "EID"; (* Endpoint Identifier 	[Michael_Patton][http://ana-3.lcs.mit.edu/~jnc/nimrod/dns.txt] 		1995-06 *)
       "NIMLOC"; (* Nimrod Locator 	[1][Michael_Patton][http://ana-3.lcs.mit.edu/~jnc/nimrod/dns.txt] 		1995-06 *)
       "SRV"; (* Server Selection 	[1][RFC2782] *)
       "ATMA"; (* ATM Address 	[ ATM Forum Technical Committee, "ATM Name System, V2.0", Doc ID: AF-DANS-0152.000, July 2000. Available from and held in escrow by IANA.] *)
       "NAPTR"; (* Naming Authority Pointer 	[RFC2915][RFC2168][RFC3403] *)
       "KX"; (* Key Exchanger 	[RFC2230] *)
       "CERT"; (* CERT 	[RFC4398] *)
       "A6"; (* A6 (OBSOLETE - use AAAA) 	[RFC3226][RFC2874][RFC6563] *)
       "DNAME"; (* DNAME 	[RFC6672] *)
       "SINK" 	; (* OPT 	[RFC6891][RFC3225] *)
       "APL"; (* APL 	[RFC3123] *)
       "DS"; (* Delegation Signer 	[RFC4034][RFC3658] *)
       "SSHFP"; (* SSH Key Fingerprint 	[RFC4255] *)
       "IPSECKEY"; (* IPSECKEY 	[RFC4025] *)
       "RRSIG"; (* RRSIG 	[RFC4034][RFC3755] *)
       "NSEC"; (* NSEC 	[RFC4034][RFC3755] *)
       "DNSKEY"; (* DNSKEY 	[RFC4034][RFC3755] *)
       "DHCID"; (* DHCID 	[RFC4701] *)
       "NSEC3"; (* NSEC3 	[RFC5155] *)
       "NSEC3PARAM"; (* NSEC3PARAM 	[RFC5155] *)
       "TLSA"; (* TLSA 	[RFC6698] *)
       "SMIMEA"; (* S/MIME cert association 	[draft-ietf-dane-smime] 	SMIMEA/smimea-completed-template 	2015-12-01 *)
       "Unassigned"; (* HIP 	55 	Host Identity Protocol 	[RFC5205] *)
       "NINFO"; (* NINFO 	[Jim_Reid] 	NINFO/ninfo-completed-template 	2008-01-21 *)
       "RKEY"; (* RKEY 	[Jim_Reid] 	RKEY/rkey-completed-template 	2008-01-21 *)
       "Trust"; (* Child DS 	[RFC7344] 	CDS/cds-completed-template 	2011-06-06 *)
       "CDNSKEY"; (* DNSKEY(s) the Child wants reflected in DS 	[RFC7344] 		2014-06-16 *)
       "OPENPGPKEY"; (* OpenPGP Key 	[draft-ietf-dane-openpgpkey] 	OPENPGPKEY/openpgpkey-completed-template 	2014-08-12 *)
       "CSYNC" (* Child-To-Parent Synchronization 	[RFC7477] 		2015-01-27 *)
    ]%vector.

  Definition RRecordType := BoundedString RRecordTypes.
  (* Aliases for common resource record types. *)
  Definition CNAME : RRecordType := ``"CNAME".
  Definition A : RRecordType := ``"A".
  Definition NS : RRecordType := ``"NS".
  Definition MX : RRecordType := ``"MX".

  Definition beq_RRecordType (a b : RRecordType) : bool :=
    BoundedIndex_beq a b.

  Definition RRecordType_dec (a b : RRecordType) :=
    BoundedIndex_eq_dec a b.

  Lemma beq_RRecordType_sym :
    forall rrT rrT', beq_RRecordType rrT rrT' = beq_RRecordType rrT' rrT.
  Proof.
    intros; eapply BoundedIndex_beq_sym.
  Qed.

  Lemma beq_RRecordType_dec :
    forall a b, ?[RRecordType_dec a b] = beq_RRecordType a b.
  Proof.
    intros; find_if_inside; subst.
    symmetry; apply (BoundedIndex_beq_refl b).
    symmetry; eapply BoundedIndex_beq_neq_dec; eauto.
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordType :
    Query_eq RRecordType := {| A_eq_dec := RRecordType_dec |}.

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

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_QType :
    Query_eq QType := {| A_eq_dec := QType_dec |}.

End RRecordTypes.

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

  Definition QClass_in (qclass : RRecordClass) : QClass :=
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

Section SOA.
  (* The start of authority record stores information about *)
  (* the zone that the DNS server is responsible for. *)

  (* Time Values used in SOA*)

  (* A domain is a list of ascii (string) *)
  Definition domain := string.

  (* A name is a list of domains. *)
  Definition name := list domain.

  Definition beq_name (a b : name) : bool :=
    if (list_eq_dec string_dec a b) then true else false.

  Lemma beq_name_dec
  : forall (a b : name), beq_name a b = true <-> a = b.
  Proof.
    unfold beq_name; intros; find_if_inside; intuition; intros; congruence.
  Qed.

  Global Instance Query_eq_name :
    Query_eq name := {| A_eq_dec := list_eq_dec string_dec |}.

  Definition timeT := W.

  (* https://support.microsoft.com/en-us/kb/163971 *)
  Definition SOAHeading :=                 (* Start of Authority *)
    < "sourcehost" :: name,
      "contact_email" :: name,
      "serial" :: timeT,             (* revision # of zone file; needs to be updates *)
      "refresh" :: timeT,
      "retry" :: timeT,              (* failed zone transfer *)
      "expire" :: timeT,           (* complete a zone transfer *)
      "minTTL" :: timeT >%Heading.           (* for negative queries *)

  Definition SOA :=                 (* Start of Authority *)
    @Tuple SOAHeading.           (* for negative queries *)
  (* should this be a tuple or a record? *)
End SOA.

Section Packet.

  (* The question section of a DNS packet. *)
  Definition question :=
    @Tuple <
    "qname" :: name,
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
    < sNAME :: name,
      sTTL :: timeT,
      sCLASS :: RRecordClass,
      sTYPE :: RRecordType,
      sRDATA :: name>%Heading.

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

Definition buildempty (is_authority : bool) (p : packet) :=
  p ○ [ "AA" ::= WS is_authority WO; (* Update Authority field *)
        "QR" ::= WS true WO; (* Set response flag to true *)
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

End Packet.
