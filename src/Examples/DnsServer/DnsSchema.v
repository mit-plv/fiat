Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii Coq.Bool.Bool
        Coq.Bool.Bvector Coq.Lists.List.

Require Import
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.packet.

Definition DnsSchema :=
  Query Structure Schema
        [ relation sCOLLECTIONS has
                   schema
                  <sNAME :: name,
                   sTYPE :: RRecordType,
                   sCLASS :: RRecordClass,
                   sTTL :: nat,
                   sDATA :: string>
          where (fun t t' => t!sNAME = t'!sNAME -> t!sTYPE <> CNAME) ]
        (* constraint on every pair of tuples: an ip address cannot have multiple aliases? *)
        enforcing [ ].

(*
Definition sCACHE := "Cache".
Definition sREQUESTS := "Requests".
Definition sSTAGE := "Stage".
Definition sID := "ID".
Definition IP := name.
Definition sIP := "IP".
Definition sRESULT := "Result".
Definition sDOMAIN := "Domain".
(* the # prefix it's on, from front? or back? *)
(* Definition sTIME := "Time". *)
(* everything added gets an unique ID already *)

Definition Stage := option nat.
Definition id : Type := nat.
Definition server := name.      (* both IP and server name *)

(* need this because there's no way to encode failure (no questions) in a packet *)
Inductive WrapperResponse : Type :=
(* TODO add SOL fields *)
| Question : server -> packet -> WrapperResponse
| Answer : packet -> WrapperResponse
| Failure : packet -> SOA -> WrapperResponse.

(* Which section of a packet a certain answer (DNSRRecord) is in. *)
Inductive PacketSection : Type :=
| PAnswer : PacketSection
| PAuthority : PacketSection
| PAdditional : PacketSection.

Definition sCACHE_QUESTIONS := "Cached questions".
Definition sCACHE_ANSWERS := "Cached answers".
Definition sCACHE_FAILURES := "Cached failures".
Definition sPACKET_SECTION := "Packet section".
Definition sSERVER := "Server". (* the server in a Question WrapperResponse *)
Definition sPID := "Packet id".
Definition sFLAGS := "Packet flags".
Definition sNAME := "Record name". (* record string redefined here for clarity *)
   (* this should be the IP (if not a reverse lookup) *)
Definition sTYPE := "Record type".
Definition sCLASS := "Record class".
Definition sTTL := "Record TTL".
Definition sRDATA := "Record RDATA".

(* SOA record fields *)
Definition sHOST := "Source host".
Definition sEMAIL := "Contact email".
Definition sSERIAL := "Serial number".
Definition sREFRESH := "Refresh time".
Definition sRETRY := "Retry time".
Definition sEXPIRE := "Expire time".
Definition sMinTTL := "Minimum TTL".
Definition sPACKET := "Packet".

Definition sREFERRALDOMAIN := "Referral domain".
Definition sRTYPE := "Referral domain type".
Definition sRCLASS := "Referral domain class".
Definition sRTTL := "Referral domain TTL".
Definition sSERVERDOMAIN := "Server domain".
Definition sSTYPE := "Server type".
Definition sSCLASS := "Server class".
Definition sSTTL := "Server TTL".
Definition sSIP := "Server IP".

(* The ideal schema would be domain and WrapperResponse, with some way to query the types nested in WrapperResponse. Flattening it here has the same effect. 

One (Domain => WrapperResponse) mapping is flattened into several rows that all have the same packet information, but store one answer (DNSRRecord) each. 

When removing a (Domain => WrapperResponse):
delete rows with the Domain in all cache tables.

When inserting/updating a new (Domain => WrapperResponse):
after checking that Domain doesn't exist in any of the cache tables (or just performing a delete), flatten it and insert each row. 

Invariants: (TODO)
- All rows for each domain should appear in exactly 1 of the cache relations (question, answer, or failure). We do not store multiple possibilities.
- All rows for each domain should have the same packet info. *)

Definition DnsRecSchema :=
  Query Structure Schema
        [ relation sCACHE_QUESTIONS has
                   schema
          (* R- = referral domain's, S- = server domain's *)
                  < sREFERRALDOMAIN :: name,
                    sRTYPE :: RRecordType,
                    sRCLASS :: RRecordClass,
                    sRTTL :: nat,
                    (* inline RDATA and additional record *)
                    sSERVERDOMAIN :: name,
                    sSTYPE :: RRecordType,
                    sSCLASS :: RRecordClass,
                    sSTTL :: nat,
                    sSIP :: name
                    (* IP in RDATA of additional record *)
                  > ;
          (* stores an answer (DNSRRecord) *)
          relation sCACHE_ANSWERS has
                   schema
                  < sDOMAIN :: name,
                    sPACKET_SECTION :: PacketSection,
                    sPID :: Bvector 16,
                    sFLAGS :: Bvector 16,
                    sNAME :: name,
                    sTYPE :: RRecordType,
                    sCLASS :: RRecordClass,
                    sTTL :: nat,
                    sRDATA :: string
                     > ;
          (* stores an SOA record according to RFC 2308 *)
          (* the SOA is technically supposed to go in the Authority section but the packet type doesn't include it *)
          relation sCACHE_FAILURES has
                   schema
                 < sDOMAIN :: name,
                   sPACKET_SECTION :: PacketSection,
                   sPID :: Bvector 16,
                   sFLAGS :: Bvector 16,
                   sHOST :: name,
                   sEMAIL :: name,
                   sSERIAL :: nat,
                   sREFRESH :: nat,
                   sRETRY :: nat,
                   sEXPIRE :: nat,
                   sMinTTL :: nat
                 > ;
          relation sREQUESTS has
                   schema
                  < sID :: id,
                    sNAME :: name,
                    sSTAGE :: Stage
                  > ]
          (* where (fun t t' => True) ] *)
        (* can i have an invariant that just works on one tuple?
         i want to encode that Stage <= length name *)
        (* use an attribute constraint TODO *)
        enforcing [ ]. *)