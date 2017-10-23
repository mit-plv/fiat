Require Import
        Coq.Vectors.Vector
        Coq.omega.Omega
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Vectors.VectorDef
        Coq.Lists.List.

Require Import
        Fiat.Common.BoundedLookup
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple.

Require Import
        Bedrock.Word
        Bedrock.Memory.

Import Vectors.VectorDef.VectorNotations.
Local Open Scope vector_scope.
Local Open Scope string_scope.

(* Resource record type and data definitions. *)

Section RRecordTypes.

  (* Enumeration of the Resource Record Types that we support. *)
  Definition OurRRecordTypes :=
    [ "CNAME"; (* e canonical name for an alias 	[RFC1035] *)
      "A"; 	(* host address 	[RFC1035] *)
      "NS"; (*  authoritative name server 	[RFC1035] *)
      "SOA"; (* rks the start of a zone of authority 	[RFC1035] *)
      "WKS"; (* well known service description 	[RFC1035] *)
      "PTR"; (* domain name pointer 	[RFC1035] *)
      "HINFO"; (* host information 	[RFC1035] *)
      "MINFO"; (* mailbox or mail list information 	[RFC1035] *)
      "MX"; (* mail exchange 	[RFC1035] *)
      "TXT" (* text strings 	[RFC1035] *)
    ].

  Definition OurRRecordType := EnumType OurRRecordTypes.

  (* Aliases for common resource record types. *)
  Definition OurCNAME : OurRRecordType := ```"CNAME".
  Definition OurA : OurRRecordType := ```"A".
  Definition OurNS : OurRRecordType := ```"NS".
  Definition OurMX : OurRRecordType := ```"MX".
  Definition OurSOA : OurRRecordType := ```"SOA".

  Definition beq_OurRRecordType (rr rr' : OurRRecordType) : bool :=
    fin_beq rr rr'.

  Definition OurRRecordType_dec (rr rr' : OurRRecordType) :=
    fin_eq_dec rr rr'.

  Lemma beq_OurRRecordType_sym :
    forall rr rr', beq_OurRRecordType rr rr' = beq_OurRRecordType rr' rr.
  Proof.
    intros; eapply fin_beq_sym.
  Qed.

  (* Enumeration of the full set of Resource Record Types. *)
  Definition ExtraRRecordTypes :=
    [ "MD"; (* mail destination (OBSOLETE - use MX) 	[RFC1035] *)
      "MF"; (* mail forwarder (OBSOLETE - use MX) 	[RFC1035] *)
       "MB"; (* mailbox domain name (EXPERIMENTAL) 	[RFC1035] *)
       "MG"; (* mail group member (EXPERIMENTAL) 	[RFC1035] *)
       "MR"; (* mail rename domain name (EXPERIMENTAL) 	[RFC1035] *)
       "NULL"; (* null RR (EXPERIMENTAL) 	[RFC1035] *)
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
    ].

  Definition RRecordType := EnumType (OurRRecordTypes) (* ++ ExtraRRecordTypes*).

  (* Aliases for common resource record types. *)
  Definition CNAME : RRecordType := ```"CNAME".
  Definition A : RRecordType := ```"A".
  Definition NS : RRecordType := ```"NS".
  Definition MX : RRecordType := ```"MX".
  Definition SOA : RRecordType := ```"SOA".

  Definition RRecordType_inj (rr : OurRRecordType) : RRecordType :=
    Fin.L _ rr.

  Definition beq_RRecordType (rr rr' : RRecordType) : bool :=
    fin_beq rr rr'.

  Definition RRecordType_dec (rr rr' : RRecordType) :=
    fin_eq_dec rr rr'.

  Lemma beq_RRecordType_sym :
    forall rr rr', beq_RRecordType rr rr' = beq_RRecordType rr' rr.
  Proof.
    intros; eapply fin_beq_sym.
  Qed.

End RRecordTypes.

Section RData.
  (* The RDATA field of a resource record depends on the type *)
  (* of the record. This field is a combination of primitive *)
  (* types, such as words, strings and domain names. We only define *)
  (* types here for non-obsolete record types from RFC 1035. *)

  (* A label is a non-empty list of ascii characters (string) *)
  Definition Label := string.
  Definition ValidLabel label := index 0 "." label = None /\ lt 0 (String.length label).

  (* A domain name is a sequence of labels separated by '.' *)
  Definition DomainName : Type := Label.

  (* A domain name is valid iff every substring not containing the '.' *)
  (* separator (and thus all labels) is less than 64 characters long. *)
  Definition ValidDomainName s :=
    (forall pre label post, s = pre ++ label ++ post
                            -> ValidLabel label
                            -> String.length label <= 63)%string%nat
    /\ (forall pre post,
           s = pre ++ "." ++ post
           -> post <> EmptyString
              /\ pre <> EmptyString
              /\ (~ exists s', post = String "." s')
              /\ (~ exists s', pre = s' ++ ".")).

  Definition beq_name (a b : DomainName) : bool :=
    if (string_dec a b) then true else false.

  Lemma beq_name_dec
    : forall (a b : DomainName), beq_name a b = true <-> a = b.
  Proof.
    unfold beq_name; intros;
      destruct (string_dec a b);
      intuition; intros; congruence.
  Qed.

  (* Start of Authority (SOA) Records *)
  (* The start of authority record stores information about *)
  (* the zone that the DNS server is responsible for. *)

  Definition timeT := W.

  Definition natTotimeT (n : nat) : timeT := natToWord _ n.
  Coercion natTotimeT : nat >-> timeT.

  Definition SOAHeading :=                 (* Start of Authority *)
    < "sourcehost" :: DomainName, (* Primary Master for the domain. *)
      "contact_email" :: DomainName, (* Administrator's email address. *)
      "serial" :: W,             (* revision # of zone file; needs to be updated *)
      "refresh" :: timeT,
      "retry" :: timeT,              (* failed zone transfer *)
      "expire" :: timeT,           (* complete a zone transfer *)
      "minTTL" :: timeT >%Heading.           (* for negative queries *)
  Definition SOA_RDATA := @Tuple SOAHeading.

  (* Host information (HINFO) Records *)
  Definition HInfoHeading :=
    < "CPU" :: string, "OS" :: string >%Heading.
  Definition HINFO_RDATA := @Tuple HInfoHeading.

  (* Mail Exchange (MX) Records *)
  Definition MXHeading :=
    < "Preference" :: word 16, "Exchange" :: DomainName>%Heading.
  Definition MX_RDATA := @Tuple MXHeading.

  (* Well-Known Services (WKS) Records *)
  Definition WKSHeading :=
    < "Address" :: W,
      "Protocol" :: word 8,
      "Bit-Map"  :: list (word 8)>%Heading.
  Definition WKS_RDATA : Type := @Tuple WKSHeading.

  (* Mailing List (MINFO) Records *)
  Definition MINFOHeading :=
    < "rMailBx" :: DomainName,
      "eMailBx" :: DomainName>%Heading.
  Definition MINFO_RDATA : Type := @Tuple MINFOHeading.

  Definition ResourceRecordTypeTypes :=
    [ DomainName; (* CNAME *)
      (W : Type); (* A *)
      DomainName; (* NS *)
      SOA_RDATA; (* SOA *)
      WKS_RDATA; (* WKS *)
      DomainName; (* PTR *)
      HINFO_RDATA; (* HINFO *)
      MINFO_RDATA; (* MINFO *)
      MX_RDATA; (* MX *)
      (string : Type) (* TXT *)
    ].

  (* The RDATA field is a variant type built from these building blocks. *)
  Definition RDataType := SumType ResourceRecordTypeTypes.

  Definition RRecordType_Ws : t (word 16) 10 :=
    Eval simpl in Vector.map (natToWord 16)
                             [
                               5; (* "CNAME" *)
                               1; (* "A" *)
                               2; (* "NS" *)
                               6; (* "SOA"*)
                               11; (* "WKS" *)
                               12; (* "PTR" *)
                               13; (* "HINFO" *)
                               14; (* "MINFO" *)
                               15; (* "MX" *)
                               16]. (* "TXT" *)


  Definition RDataTypeToRRecordType (r : RDataType) : RRecordType :=
    SumType_index _ r.

End RData.
