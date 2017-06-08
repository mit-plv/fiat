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
