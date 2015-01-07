Require Import AutoDB BagADT.
Require Import Vector Ascii.
Definition vector A n := t A (N.to_nat n).

Record label :=
  { length : N;
    word : vector ascii length }.
Definition name := list label.
Inductive pname :=  fullname : name -> pname | pointername : N -> pname.

Record question :=
  { qname : name;
    qtype : N;
    qclass : N }.

Record answer :=
  { aname : pname;
    atype : N;
    aclass : N;
    ttl : N;
    rdlength : N;
    rdata : vector ascii rdlength }.
    
Record packet :=
  { id : N;
    flags : N;
    qdcount : N;
    ancount : N;
    nscount : N;
    arcount : N;
    questions : vector question qdcount;
    answers : vector answer ancount;
    authority : vector answer nscount;
    additional : vector answer nscount }.

Definition sCOLLECTIONS := "Collections".
Definition sNAME := "Name".
Definition sTTL := "TTL".
Definition sCLASS := "Class".
Definition sTYPE := "Type".
Definition sDLENGTH := "DLength".
Definition sDATA := "Data".

Definition DnsSchema :=
  Query Structure Schema
        [ relation sCOLLECTIONS has
                   schema <sNAME :: name,
                           sTTL :: N,
                           sCLASS :: N,
                           sTYPE :: N,
                           sDLENGTH :: N,
                           sDATA :: string >]
        enforcing [].

Definition DnsCache := TupleDef DnsSchema sCOLLECTIONS.
Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "Process" : rep x packet -> rep x packet
  }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsCacheSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,
    query "Process" (p : packet) : packet :=
      rs <- For (r in sDNSCACHE)
         Where ((qname (question p)) ?? r!sNAME)
         Return r
  }.