Require Import AutoDB BagADT.
Require Import Vector Ascii Bool Bvector List.

Record label :=
  { length : N;
    word : string }.
Definition name := list label.

(* Name or pointer offset to a name *)
Inductive pname :=  fullname : name -> pname | pointername : N -> pname.

Record question :=
  { qname : name;
    qtype : N;
    qclass : N }.

Record answer :=
  { aname : name; (* `pname` if we allow compression *)
    atype : N;
    aclass : N;
    ttl : N;
    rdlength : N;
    rdata : list ascii }.

Record packet :=
  { id : N;
    flags : Bvector 16; (* 16 bits of boolean *)
    qdcount : N;
    ancount : N;
    nscount : N;
    arcount : N;
    questions : question; (* `list question` in case we can have multiple questions? *)
    answers : list answer;
    authority : list answer;
    additional : list answer }.

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
        enforcing [ ].
(*
     + one CNAME record exists, optionally accompanied by SIG, NXT, and
       KEY RRs,
     + one or more records exist, none being CNAME records,
     + the name exists, but has no associated RRs of any type,
     + the name does not exist at all.
*)

Definition DnsTuple := TupleDef DnsSchema sCOLLECTIONS.
Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "Process" : rep x packet -> rep x packet
  }.

Definition prefix (p s : name) := exists ps, List.app p ps = s.

Definition upperbound (r : DnsTuple) (rs : list DnsTuple) :=
  forall r', List.In r' rs -> List.length r!sNAME >= List.length r'!sNAME.
 
Definition cname : N := 5 % N.

Lemma zero_lt_sixteen : lt 0 16. omega. Qed.
Definition buildempty (input : packet) : packet :=
  {| id := id input;
     flags := replace_order (flags input) zero_lt_sixteen true; (* set QR bit *)
     qdcount := qdcount input;
     ancount := 0;
     nscount := 0;
     arcount := 0;
     questions := questions input; (*list question*)
     answers := List.nil;
     authority := List.nil;
     additional := List.nil |}.

Variable addns : packet -> DnsTuple -> packet.
Variable addrr : packet -> DnsTuple -> packet.
Variable rec : packet.
Variable EnsembleEq : forall A, Ensemble A -> list A -> Prop.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,
    query "Process" (p : packet) : packet :=
      rs <- For (r in sCOLLECTIONS)
         Where (prefix r!sNAME (qname (questions p)))
         Return r;
      bfrs <- { bfrs | forall r, List.In r bfrs <-> List.In r rs /\ upperbound r rs };
      matched <- { matched | matched = true <-> forall b, List.In b bfrs -> (qname (questions p)) = b!sNAME }; 
      if matched
      then 
        is_cname <- { is_cname | is_cname = true <-> exists b, List.In b bfrs -> b!sTYPE = cname };
        if andb is_cname (negb (N.eqb (qtype (questions p)) cname))
        then ret (List.fold_left addrr bfrs rec)
        else ret (List.fold_left addrr bfrs (buildempty p))
      else 
        ret (List.fold_left addns bfrs (buildempty p))
  }.