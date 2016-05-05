Require Import
        Coq.Vectors.Vector
        Coq.omega.Omega
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Vectors.VectorDef
        Coq.Lists.List
        Bedrock.Word
        Bedrock.Memory
        Fiat.QueryStructure.Automation.AutoDB.

Import Coq.Vectors.VectorDef.VectorNotations.
Local Open Scope vector.

(* Resource record type and data definitions. *)

Section RRecordTypes.

  (* Enumeration of the Resource Record Types that we support. *)
  Definition OurRRecordTypes :=
    ["A"; 	(* host address 	[RFC1035] *)
       "NS"; (*  authoritative name server 	[RFC1035] *)
       "CNAME"; (* e canonical name for an alias 	[RFC1035] *)
       "SOA"; (* rks the start of a zone of authority 	[RFC1035] *)
       "WKS"; (* well known service description 	[RFC1035] *)
       "PTR"; (* domain name pointer 	[RFC1035] *)
       "HINFO"; (* host information 	[RFC1035] *)
       "MINFO"; (* mailbox or mail list information 	[RFC1035] *)
       "MX"; (* mail exchange 	[RFC1035] *)
       "TXT" (* text strings 	[RFC1035] *)
    ].

  Definition OurRRecordType := BoundedString OurRRecordTypes.

  (* Aliases for common resource record types. *)
  Definition OurCNAME : OurRRecordType := ``"CNAME".
  Definition OurA : OurRRecordType := ``"A".
  Definition OurNS : OurRRecordType := ``"NS".
  Definition OurMX : OurRRecordType := ``"MX".
  Definition OurSOA : OurRRecordType := ``"SOA".

  Definition beq_OurRRecordType (rr rr' : OurRRecordType) : bool :=
    BoundedIndex_beq rr rr'.

  Definition OurRRecordType_dec (rr rr' : OurRRecordType) :=
    BoundedIndex_eq_dec rr rr'.

  Lemma beq_OurRRecordType_sym :
    forall rr rr', beq_OurRRecordType rr rr' = beq_OurRRecordType rr' rr.
  Proof.
    intros; eapply BoundedIndex_beq_sym.
  Qed.

  Lemma beq_OurRRecordType_dec :
    forall rr rr', ?[OurRRecordType_dec rr rr'] = beq_OurRRecordType rr rr'.
  Proof.
    intros; find_if_inside; subst.
    symmetry; apply (BoundedIndex_beq_refl rr').
    symmetry; eapply BoundedIndex_beq_neq_dec; eauto.
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_OurRRecordType :
    Query_eq OurRRecordType := {| A_eq_dec := OurRRecordType_dec |}.

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

  Definition RRecordType := BoundedString (OurRRecordTypes ++ ExtraRRecordTypes).

  (* Aliases for common resource record types. *)
  Definition CNAME : RRecordType := ``"CNAME".
  Definition A : RRecordType := ``"A".
  Definition NS : RRecordType := ``"NS".
  Definition MX : RRecordType := ``"MX".
  Definition SOA : RRecordType := ``"SOA".

  Definition RRecordType_inj (rr : OurRRecordType) : RRecordType :=
    BoundedIndex_injR rr.

  Definition beq_RRecordType (rr rr' : RRecordType) : bool :=
    BoundedIndex_beq rr rr'.

  Definition RRecordType_dec (rr rr' : RRecordType) :=
    BoundedIndex_eq_dec rr rr'.

  Lemma beq_RRecordType_sym :
    forall rr rr', beq_RRecordType rr rr' = beq_RRecordType rr' rr.
  Proof.
    intros; eapply BoundedIndex_beq_sym.
  Qed.

  Lemma beq_RRecordType_dec :
    forall rr rr', ?[RRecordType_dec rr rr'] = beq_RRecordType rr rr'.
  Proof.
    intros; find_if_inside; subst.
    symmetry; apply (BoundedIndex_beq_refl rr').
    symmetry; eapply BoundedIndex_beq_neq_dec; eauto.
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordType :
    Query_eq RRecordType := {| A_eq_dec := RRecordType_dec |}.

End RRecordTypes.

Section RData.
  (* The RDATA field of a resource record depends on the type *)
  (* of the record. This field is a combination of primitive *)
  (* types, such as words, strings and domain names. We only define *)
  (* types here for non-obsolete record types from RFC 1035. *)

  (* A label is a list of ascii characters (string) *)
  Definition Label := string.
  (* A domain name is a list of labels. *)
  Definition DomainName : Type := list Label.

  Definition beq_name (a b : DomainName) : bool :=
    if (list_eq_dec string_dec a b) then true else false.

  Lemma beq_name_dec
    : forall (a b : DomainName), beq_name a b = true <-> a = b.
  Proof.
    unfold beq_name; intros; find_if_inside; intuition; intros; congruence.
  Qed.

  Global Instance Query_eq_name :
    Query_eq DomainName := {| A_eq_dec := list_eq_dec string_dec |}.

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

  (* The RDATA field is a variant type built from these building blocks. *)

  Fixpoint SumType {n} (v : Vector.t Type n) {struct v} : Type :=
    match v with
    | Vector.nil => (False : Type)
    | Vector.cons T _ Vector.nil => T
    | Vector.cons T _ v' => T + (SumType v')
    end%type.

  Arguments SumType : simpl never.

  Fixpoint inj_SumType {n}
             (v : Vector.t Type n)
             (tag : Fin.t n)
             (el : Vector.nth v tag)
    {struct v} : SumType v.
    refine (match v in Vector.t _ n return
                  forall
                    (tag : Fin.t n)
                    (el : Vector.nth v tag),
                    SumType v
            with
            | Vector.nil => fun tag el => Fin.case0 _ tag
            | Vector.cons T n' v' => fun tag el => _
            end tag el).

    generalize v' (inj_SumType n' v') el0; clear; pattern n', tag0; apply Fin.caseS; simpl; intros.
    - destruct v'; simpl.
      + exact el0.
      + exact (inl el0).
    - destruct v'; simpl.
      + exact (Fin.case0 _ p).
      + exact (inr (X p el0)).
  Defined.

  Fixpoint SumType_index {n}
             (v : Vector.t Type n)
             (el : SumType v)
    {struct v} : Fin.t n.
    refine (match v in Vector.t _ n return
                  SumType v -> Fin.t n
            with
            | Vector.nil => fun el => match el with end
            | Vector.cons T _ v' => fun el => _
            end el).
    generalize (SumType_index _ v'); clear SumType_index; intros.
    destruct v'; simpl.
    - exact Fin.F1.
    - destruct el0.
      + exact Fin.F1.
      + exact (Fin.FS (X s)).
  Defined.

  Fixpoint SumType_proj {n}
           (v : Vector.t Type n)
           (el : SumType v)
           {struct v} : v[@SumType_index v el].
    refine (match v in Vector.t _ n return
                  forall el : SumType v, v[@SumType_index v el]
            with
            | Vector.nil => fun el => match el with end
            | Vector.cons T _ v' => fun el => _
            end el).
    generalize (SumType_proj _ v'); clear SumType_proj; intros.
    destruct v'; simpl.
    - exact el0.
    - destruct el0.
      + exact t.
      + exact (X s).
  Defined.

  Lemma inj_SumType_proj_inverse {n}
    : forall (v : Vector.t Type n)
             (el : SumType v),
      inj_SumType v _ (SumType_proj v el) = el.
  Proof.
    induction v; simpl; intros.
    - destruct el.
    - destruct v.
      + simpl; reflexivity.
      + destruct el; simpl; eauto.
        f_equal; apply IHv.
  Qed.

  Lemma index_SumType_inj_inverse {n}
    : forall  (tag : Fin.t n)
              (v : Vector.t Type n)
              (el : Vector.nth v tag),
      SumType_index v (inj_SumType v tag el) = tag.
  Proof.
    induction tag.
    - intro; pattern n, v; eapply Vector.caseS; simpl.
      clear; intros; destruct t; eauto.
    - intro; revert tag IHtag; pattern n, v; eapply Vector.caseS; simpl; intros.
      destruct t.
      + inversion tag.
      + f_equal.
        eapply IHtag.
  Qed.

  Definition IsComputedField
             {heading}
             (idx idx' : BoundedString (HeadingNames heading))
             (f : Domain heading (ibound (indexb idx))
                  -> Domain heading (ibound (indexb idx')))
             (tup : @Tuple heading)
    : Prop :=
    f (GetAttribute tup idx) = GetAttribute tup idx'.

  (* Could use above to prove dependent inversion lemma, but *)
  (* this is more of a sanity check than anything. *)
  (* Lemma proj_SumType_inj_inverse {n}
    : forall (v : Vector.t Type n)
             (tag : Fin.t n)
             (el : Vector.nth v tag),
      SumType_proj v (inj_SumType v tag el) = el. *)

  (* Goal: Convert from QueryStructure with a heading with a SumType *)
  (* attribute to one that has multiple tables. *)
  (* Is this a worthwhile refinement? We could just do this at data structure *)
  (* selection time. OTOH, nice high-level refinement step that makes sense to *)
  (* end-users and has applications in both DNS examples.  *)

  Definition EnumIDs := ["A"; "NS"; "CNAME"; "SOA" ].
  Definition EnumID := BoundedString EnumIDs.
  Definition EnumTypes := [nat : Type; string : Type; nat : Type; list nat : Type].
  Definition EnumType := SumType EnumTypes.

  Definition EESchema :=
      Query Structure Schema
        [ relation "foo" has
                   schema <"A" :: nat, "BID" :: EnumID, "B" :: EnumType>
                   where (fun t => ibound (indexb t!"BID") = SumType_index _ t!"B" ) and (fun t t' => True);
          relation "bar" has
                   schema <"C" :: nat, "D" :: list string>
        ]
        enforcing [ ].

  Definition EESpec : ADT _ :=
    Def ADT {
      rep := QueryStructure EESchema,

    Def Constructor "Init" : rep := empty,,

    Def Method1 "AddData" (this : rep) (t : _) : rep * bool :=
      Insert t into this!"foo",

    Def Method1 "Process" (this : rep) (p : EnumID) : rep * list _ :=
      results <- For (r in this!"foo")
                     Where (r!"BID" = p)
                     Return r;
    ret (this, results)}.

  Definition ResourceRecordTypeTypes :=
    [ (W : Type); (* A *)
       DomainName; (* NS *)
       DomainName; (* CNAME *)
       SOA_RDATA; (* SOA *)
       WKS_RDATA; (* WKS *)
       DomainName; (* PTR *)
       HINFO_RDATA; (* HINFO *)
       DomainName; (* MINFO *)
       MX_RDATA; (* MX *)
       (string : Type) (* TXT *)
    ].

  Definition RDataType := SumType ResourceRecordTypeTypes.

End RData.

Arguments SumType : simpl never.
