(* Old packet design (not used in rec/cache). 
Differs only in that the rdata field of answer record has type string, not name *)

Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii Coq.Bool.Bool
        Coq.Bool.Bvector Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB.

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

  (* do we currently use recordtype and recordclass? *)
  Record question :=
    { qname : name;
      qtype : RRecordType;
      qclass : RRecordClass }.
  (* ["google", "com"] *)

  (* ["192", "0", "0", "1"] *)
  (* TODO ip vs name? *)
  Record answer :=
    { aname : name;
      atype : RRecordType;
      aclass : RRecordClass;
      ttl : nat;
      rdata : string }.           (* stores a hostname or an IP *)
  (* technically this should contain SOA info as well, but I made SOA a separate type *)

Definition default_refresh_time := 3600. (* seconds *)
Definition default_retry_time := 600.
Definition default_expire_time := 86400. 
(* may cause stack overflow / segfault; use hours instead? *)
Definition default_minimum_TTL := 3600.

  (* TODO: authoritative DNS server does not yet store or return this SOA *)
  (* https://support.microsoft.com/en-us/kb/163971 *)
  Record SOA :=                 (* Start of Authority *)
    { sourcehost : name;
      contact_email : name;
      serial : nat;             (* revision # of zone file; needs to be updates *)
      refresh : nat;
      retry : nat;              (* failed zone transfer *)
      expire : nat;             (* complete a zone transfer *)
      minTTL : nat }.           (* for negative queries *)
  (* should this be a tuple or a record? *)

  Record packet :=
    { id : Bvector 16;
      flags : Bvector 16;
      questions : question; (* `list question` in case we can have multiple questions? *)
      (* is question the same as domain? no, sometimes we want to throw out the QUESTION and replace it with the DOMAIN
e.g. our question could be "scholar.google.com" but our domain could be "google.com" (prefix)
so 
- should we cache "google.com" under "scholar.google.com"? yes, as a question
- should we cache "scholar.google.com" under "google.com"? no
should packets be generated anew??

for a wrapperresponse:
Question means that domain should be a strict prefix of name? what about server?
   for the [full question scholar.google.com] we know the server [192.168.1.1] for prefix [google.com] instead
   but should this redirect should work for ANY string for which google.com is a strict prefix?
   yes. so, in conclusion, when we get the result from the cache, we need to replace the question with the real question e.g. images.google.com; we'll already have that other packet info
Answer means that domain == name

 *)
      answers : list answer;
      authority : list answer;
      additional : list answer }.

Definition test_vec := Bvect_true 16.
Definition test_question :=
  {| qname := nil;
     qtype := A;
     qclass := CH |}.
Definition test_packet :=
  {| id := test_vec;
     flags := test_vec;
     questions := test_question;
     answers := nil;
     authority := nil;
     additional := nil |}.

Definition id' p := id p.       (* to get around shadowing *)

      (* is question the same as domain? no, sometimes we want to throw out the QUESTION and replace it with the DOMAIN
e.g. our question could be "scholar.google.com" but our domain could be "google.com" (prefix)
so 
- should we cache "google.com" under "scholar.google.com"? yes, as a question
- should we cache "scholar.google.com" under "google.com"? no
should packets be generated anew??

for a wrapperresponse:
Question means that domain should be a strict prefix of name? what about server?
   for the [full question scholar.google.com] we know the server [192.168.1.1] for prefix [google.com] instead
   but should this redirect should work for ANY string for which google.com is a strict prefix?
   yes. so, in conclusion, when we get the result from the cache, we need to replace the question with the real question e.g. images.google.com; we'll already have that other packet info
Answer means that domain == name *)

Print replace_order.
Locate replace_order.

  Lemma zero_lt_sixteen : lt 0 16. omega. Qed.
  Definition buildempty (p : packet) :=
    {| id := id p;
       (* for a particular request, all related packets should have the same id *)
       flags := replace_order (flags p) zero_lt_sixteen true; 
       (* 0 = query (changed by client); 1 = response (changed by server) *)
       (* set QR bit to true, meaning this is a response *)
       (* do we want an AA (authoritative answer) flag? *)
       questions := questions p;
       answers := [ ];
       authority := [ ];
       additional := [ ] |}.

  Definition sCOLLECTIONS := "Collections".
  Definition sNAME := "Name".
  Definition sTTL := "TTL".
  Definition sCLASS := "Class".
  Definition sTYPE := "Type".
  Definition sDATA := "Data".

  (* DNS Resource Records. *)
  Definition DNSRRecord :=
    @Tuple <sNAME :: name,
            sTYPE :: RRecordType,
            sCLASS :: RRecordClass,
            sTTL :: nat,
            sDATA :: string>%Heading.

  Definition toAnswer (t: DNSRRecord) :=
    {| aname := t!sNAME;
       atype := t!sTYPE;
       aclass := t!sCLASS;
       ttl := t!sTTL;
       rdata := t!sDATA |}.

  (* add a record to a packet's list of answers *)
  Definition addan (p : packet) (t : DNSRRecord) :=
    {| id := id p;
       flags := flags p;
       questions := questions p;
       answers := (toAnswer t) :: answers p;
       authority := authority p;
       additional := additional p |}.

  Definition addns (p : packet) (t : DNSRRecord) :=
    {| id := id p;
       flags := flags p;
       questions := questions p;
       answers := answers p;
       authority := (toAnswer t) :: (authority p);
       additional := additional p |}.

  (* combine with above? *)
  Definition addAdditional (p : packet) (t : DNSRRecord) :=
    {| id := id p;
       flags := flags p;
       questions := questions p;
       answers := answers p;
       authority := authority p;
       additional := (toAnswer t) :: additional p |}.

  Definition updateRecords (p : packet) answers' authority' additional' :=
    {| id := id p;
       flags := flags p;
       questions := questions p;
       answers := answers';
       authority := authority';
       additional := additional' |}.

End Packet.
