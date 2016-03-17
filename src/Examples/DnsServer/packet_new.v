Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List
        Fiat.QueryStructure.Automation.AutoDB.

Section Packet.

  Definition name := list string.

  Definition beq_name (a b : name) : bool :=
    if (list_eq_dec string_dec a b) then true else false.

  Lemma beq_name_dec
  : forall (a b : name), beq_name a b = true <-> a = b.
  Proof.
    unfold beq_name; intros; find_if_inside; intuition; intros; congruence.
  Qed.

  Global Instance Query_eq_name :
    Query_eq name := {| A_eq_dec := list_eq_dec string_dec |}.

  Inductive RRecordType := A | CNAME | NS | MX.
  (* MX = message exchange (hostname must map directly to an A/address record and not point to any CNAME records)
     NS = name server *)

  Definition beq_RRecordType (a b : RRecordType) :=
    match a, b with
      | A, A => true
      | CNAME, CNAME => true
      | NS, NS => true
      | MX, MX => true
      | _, _ => false
    end.

  Lemma RRecordType_dec
  : forall (a b : RRecordType), {a = b} + {a <> b}.
  Proof.
    destruct a; destruct b; simpl; intuition; intros;
    try first [right; discriminate | left; reflexivity].
  Qed.

  Lemma beq_RRecordType_sym :
    forall rrT rrT', beq_RRecordType rrT rrT' = beq_RRecordType rrT' rrT.
  Proof.
    destruct rrT; destruct rrT'; simpl; congruence.
  Qed.

  Lemma beq_RRecordType_dec :
    forall a b, ?[RRecordType_dec a b] = beq_RRecordType a b.
  Proof.
    intros; find_if_inside; subst.
    destruct b; simpl; reflexivity.
    destruct a; destruct b; simpl; congruence.
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordType :
    Query_eq RRecordType := {| A_eq_dec := RRecordType_dec |}.

  Inductive RRecordClass := IN | CH | HS.
  (* internet / other two protocols *)

  Definition beq_RRecordClass (a b : RRecordClass) :=
    match a, b with
      | IN, IN => true
      | CH, CH => true
      | HS, HS => true
      | _, _ => false
    end.
  Lemma RRecordClass_dec
  : forall (a b : RRecordClass), {a = b} + {a <> b}.
  Proof.
    destruct a; destruct b; simpl; intuition; intros;
    try first [right; discriminate | left; reflexivity ].
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordClass :
    Query_eq RRecordClass := {| A_eq_dec := RRecordClass_dec |}.

  Open Scope Heading.

  (* do we currently use recordtype and recordclass? *)
  Definition question :=
    @Tuple <
    "qname" :: name,
    "qtype" :: RRecordType,
    "qclass" :: RRecordClass >%Heading.
  (* ["google", "com"] *)

Definition default_refresh_time := (*3600 *) 10. (* seconds *)
Definition default_retry_time := (*600 *) 10.
Definition default_expire_time := (* 86400 *) 10.
(* may cause stack overflow / segfault; use hours instead? *)
Definition default_minimum_TTL := 10 (* 3600 *).

  (* TODO: authoritative DNS server does not yet store or return this SOA *)
  (* https://support.microsoft.com/en-us/kb/163971 *)
  Definition SOA :=                 (* Start of Authority *)
    @Tuple < "sourcehost" :: name,
      "contact_email" :: name,
      "serial" :: nat,             (* revision # of zone file; needs to be updates *)
      "refresh" :: nat,
      "retry" :: nat,              (* failed zone transfer *)
      "expire" :: nat,           (* complete a zone transfer *)
      "minTTL" :: nat >.           (* for negative queries *)
  (* should this be a tuple or a record? *)

  (* DNS Resource Records. *)
  Definition resourceRecord :=
    @Tuple <
    "name" :: name,
    "ttl" :: nat,
    "class" :: RRecordClass,
    "type" :: RRecordType,
    "rlength" :: nat,
    "rdata" :: name + SOA>.
  (* [rdata] stores a hostname, IP, or an SOA, depeneding on the
   record type. *)

  Definition packet :=
    @Tuple < "id" :: Bvector 16,
      "flags" :: Bvector 16,
      "questions" :: question, (* `list question` in case we can have multiple questions? *)
      "answers" :: list resourceRecord,
      "authority" :: list resourceRecord,
      "additional" :: list resourceRecord >.
  (* add SOA TODO *)

Definition test_question : question :=
  < "qname" :: nil,
    "qtype" :: A,
     "qclass" :: CH >%Tuple.

Definition test_packet : packet :=
  <  "id" :: Bvect_true 16,
      "flags" :: Bvect_true 16,
     "questions" :: test_question,
     "answers" :: nil,
     "authority" :: nil,
     "additional" :: nil >%Tuple.

  Lemma zero_lt_sixteen : lt 0 16. omega. Qed.

  Definition buildempty (p : packet) :=
    p ○ [o !! "flags" / replace_order o zero_lt_sixteen true;
          (* 0 = query (changed by client); 1 = response (changed by server) *)
          (* set QR bit to true, meaning this is a response *)
          (* do we want an AA (authoritative answer) flag? *)
         "answers" ::= [ ]; "authority"  ::= [ ]; "additional" ::= [ ] ].

  Definition sCOLLECTIONS := "Collections".
  Definition sNAME := "Name".
  Definition sTTL := "TTL".
  Definition sCLASS := "Class".
  Definition sTYPE := "Type".
  Definition sDATA := "Data".

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
