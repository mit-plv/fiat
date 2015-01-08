Require Import AutoDB BagADT.
Require Import Vector Ascii.

Definition vector A n := t A (N.to_nat n).

Record label :=
  { length : N;
    word : vector ascii length }.
Definition name := list label.

(* Name or pointer offset to a name *)
Inductive pname :=  fullname : name -> pname | pointername : N -> pname.

Record question :=
  { qname : name;
    qtype : N;
    qclass : N }.

Record answer :=
  { aname : name (* pname *);
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
    questions : question (*vector question qdcount*);
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
                           sDATA :: string> ]
        enforcing [].
(*
     + one CNAME record exists, optionally accompanied by SIG, NXT, and
       KEY RRs,
     + one or more records exist, none being CNAME records,
     + the name exists, but has no associated RRs of any type,
     + the name does not exist at all.
*)

Definition DnsCache := TupleDef DnsSchema sCOLLECTIONS.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "Process" : rep x packet -> rep x packet
  }.

Variable cprefix : name -> name -> Prop.
Variable lessthaneq : list DnsCache -> DnsCache -> Prop.
Variable CNAME : N.
Variable buildempty : packet.
Variable addns : packet -> DnsCache -> packet.
Variable addrr : packet -> DnsCache -> packet.
Variable rec : packet.
Variable EnsembleEq : forall A, Ensemble A -> list A -> Prop.

Print UnIndexedEnsembleListEquivalence.
Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,
    query "Process" (p : packet) : packet :=
      rs <- For (r in sCOLLECTIONS)
         Where (cprefix (qname (questions p)) r!sNAME)
         Return r;
      bfrs <- { bfrs | forall r, List.In r bfrs <-> List.In r rs /\ lessthaneq rs r };
      test <- { test | test = true <-> forall b, List.In b bfrs -> (qname (questions p)) = b!sNAME }; 
      if test
      then 
        test2 <- { test2 | test2 = true <-> exists b, List.In b bfrs -> b!sTYPE = CNAME };
        if andb test2 (N.eqb (qtype (questions p)) CNAME)
        then ret (List.fold_left addrr bfrs rec)
        else ret (List.fold_left addrr bfrs buildempty)
      else 
        ret (List.fold_left addns bfrs buildempty)
  }.