Require Import
        Coq.Vectors.Vector
        Coq.ZArith.ZArith
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Vectors.Vector
        Coq.Lists.List.

Require Import
        Fiat.Common.BoundedLookup
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.Formats.DomainNameOpt.

Require Import
        Bedrock.Word
        Bedrock.Memory.

Import Vectors.Vector.VectorNotations.
Local Open Scope vector_scope.
Local Open Scope string_scope.

(* (Smaller set of) resource record type and data definitions. *)

Section RRecordTypes.

  (* Enumeration of the Resource Record Types that we support. *)
  Definition OurRRecordTypes :=
    [ "CNAME"; (* e canonical name for an alias 	[RFC1035] *)
      "A"; 	(* host address 	[RFC1035] *)
      "NS"; (*  authoritative name server 	[RFC1035] *)
      "SOA" (* rks the start of a zone of authority 	[RFC1035] *)
    ].

  Definition OurRRecordType := EnumType OurRRecordTypes.

  (* Aliases for common resource record types. *)
  Definition OurCNAME : OurRRecordType := ```"CNAME".
  Definition OurA : OurRRecordType := ```"A".
  Definition OurNS : OurRRecordType := ```"NS".
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

  Definition RRecordType := EnumType (OurRRecordTypes) (* ++ ExtraRRecordTypes*).

  (* Aliases for common resource record types. *)
  Definition CNAME : RRecordType := ```"CNAME".
  Definition A : RRecordType := ```"A".
  Definition NS : RRecordType := ```"NS".
  Definition SOA : RRecordType := ```"SOA".

  Definition RRecordType_inj (rr : OurRRecordType) : RRecordType := rr.

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

  Definition ResourceRecordTypeTypes :=
    [ DomainName; (* CNAME *)
      (W : Type); (* A *)
      DomainName; (* NS *)
      SOA_RDATA (* SOA *)
    ].

  (* The RDATA field is a variant type built from these building blocks. *)
  Definition RDataType := SumType ResourceRecordTypeTypes.

  Definition RRecordType_Ws : t (word 16) 4 :=
    Eval simpl in Vector.map (natToWord 16)
                             [
                               5; (* "CNAME" *)
                               1; (* "A" *)
                               2; (* "NS" *)
                               6]. (* "SOA" *)


  Definition RDataTypeToRRecordType (r : RDataType) : RRecordType :=
    SumType_index _ r.

End RData.
