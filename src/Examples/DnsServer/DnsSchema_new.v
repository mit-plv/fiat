Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii Coq.Bool.Bool
        Coq.Bool.Bvector Coq.Lists.List.

Require Import
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.packet_new.

(* The schema, packet structure, and spec are based on the following four RFCs:

RFC 1034: high-level DNS outline
RFC 1035: implementation details
RFC 2308: negative caching -- for more information on failures and SOA records
RFC 1536: common implementation errors and fixes -- for efficiency/security problems *)

(* What subdomain we're on in a question, e.g. 
new requests get stage None
when working on a referral, the stage is set to the match count b/t the referral and question
e.g. question = s.g.com, referral = for g.com, stage = match count = 2
(excluding root) *)
Definition Stage := option nat.
(* for TTL *)
Definition time := nat.
(* unique ids for various things *)
Definition id : Type := nat.
(* position in SLIST *)
Definition position := nat.
(* e.g. ["192", "168", "1", "1"] *)
Definition IP := name.

(* Type of things that the outside world (the wrapper) can send to us, the recursive caching   server. Need this because there's no way to encode failure (no questions) in a packet.
  Packet is missing RCODE field that encodes success/kinds of failure (RFC 2308) *)
Definition FromOutside : Type := (id * packet * option SOA)%type.

(* Type of the things that we (the server) can send to the wrapper, including various error codes and responses. *)
Inductive ToOutside : Type :=
(* Errors *)
| InvalidQuestion : id -> ToOutside
| InvalidResponse : id -> ToOutside
| InvalidPacket : id -> packet -> ToOutside
| MissingSOA : id -> packet -> ToOutside
| InternalCacheError : id -> packet -> ToOutside
| NoReferralsLeft : id -> packet -> ToOutside
| InvalidId : id -> packet -> ToOutside
(* Responses *)
(* We were referred to the server with ip IP, and ask it the same question. Request is pending *)
| ServerQuestion : id -> IP -> packet -> ToOutside
(* Request is finished *)
| ClientAnswer : id -> packet -> ToOutside
| ClientFailure : id -> packet -> SOA -> ToOutside.

(* Type of things we store for a finished request. (Note no referrals) *)
Inductive ToStore : Type :=
| Answer : name -> packet -> ToStore
| Failure : name -> packet -> SOA -> ToStore.

(* The section of a packet that a certain answer (DNSRRecord) is in, used to tag the flattened rows from a packet. Needed because they're all of type answer so there's no other way to distinguish them *)
Inductive PacketSection : Type :=
| PAnswer : PacketSection
| PAuthority : PacketSection
| PAdditional : PacketSection.

(* String definitions *)
Definition sREQUESTS := "Requests".
Definition sSTAGE := "Stage".
Definition sID := "ID".
Definition sIP := "IP".
Definition sRESULT := "Result".
Definition sDOMAIN := "Domain".

Definition sCACHE_POINTERS := "Cache pointers to tables".
Definition sCACHE_REFERRALS := "Cached referrals".
Definition sCACHE_ANSWERS := "Cached answers".
Definition sCACHE_FAILURES := "Cached failures".
Definition sPACKET_SECTION := "Packet section".
Definition sSERVER := "Server".
Definition sPID := "Packet id".
Definition sFLAGS := "Packet flags".
Definition sNAME := "Record name".
Definition sTYPE := "Record type".
Definition sCLASS := "Record class".
Definition sTTL := "Record TTL".
Definition sRDATA := "Record RDATA".

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

Definition sQNAME := "Question name".
Definition sQTYPE := "Question type".
Definition sQCLASS := "Question class".
Definition sCACHETABLE := "Cache table".

Definition sREQID := "Request ID".
Definition sREFERRALID := "Referral ID".
Definition sMATCHCOUNT := "# labels matched". 
Definition sQUERYCOUNT := "# times queried".

Definition sORDER := "SLIST order". (* using referral IDs *)
Definition sSLIST := "SLIST".
Definition sSLIST_ORDERS := "SLIST orders".

Definition sTIME_LAST_CALCULATED := "Time the TTL was last calculated".
(* initialized with the time the record arrives *)

(* ------------------ Schema headings *)

(* The ideal schema would be domain and WrapperResponse, with some way to query the types nested in WrapperResponse. Flattening it here has the same effect. 

One (Domain => WrapperResponse) mapping is flattened into several rows that all have the same packet information, but store one answer (DNSRRecord) each. 

When removing a (Domain => ToStore):
delete rows with the Domain in all cache tables.

When inserting/updating a new (Domain => ToStore):
after checking that Domain doesn't exist in any of the cache tables (or just performing a delete), flatten it and insert each row. 

Invariants: (TODO)
- All rows for each domain should appear in exactly 1 of the cache relations (question, answer, or failure). We do not store multiple possibilities.
- All rows for each domain should have the same packet info. *)

(* For referrals: 
 for domain "brl.mil", referral to suffix "mil": 
 go to server "a.isi.edu" with IP 1.0.0.1 (and ask it the same question). 
 We discard the original question "brl.mil." 
 See  RFC 1034 6.2.6, 6.3.1 *)
Definition SLIST_ReferralHeading :=
  (* R- = referral domain's, S- = server domain's *)
         <sREQID :: nat,        (* tuple of (reqid, refid) should be unique for each row *)
          sREFERRALID :: nat,

          sREFERRALDOMAIN :: name,
          sRTYPE :: RRecordType,
          sRCLASS :: RRecordClass,
          sRTTL :: nat,
          (* inline RDATA and additional record *)
          sSERVERDOMAIN :: name,
          sSTYPE :: RRecordType,
          sSCLASS :: RRecordClass,
          sSTTL :: nat,
          sSIP :: name,
          (* IP in RDATA of additional record *)
          sTIME_LAST_CALCULATED :: nat,

          sMATCHCOUNT :: nat,
          sQUERYCOUNT :: nat
         >%Heading.

(* Heading for cached referrals. Same as above but without the "live" information (ids, match and query count) and with cache info (TTL and time the TTL was last calculated) *)
Definition ReferralHeading :=
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
          sSIP :: name,
          (* IP in RDATA of additional record *)
          sTIME_LAST_CALCULATED :: nat
         >%Heading.

(* Stores a cached answer (DNSRRecord). Might have appeared in the answer, authority, or additional section of a packet. *)
(* sDOMAIN and sNAME may differ in the case of CNAME, where 
sDOMAIN is an alias for sNAME. See RFC 1034, 6.2.7 *)
Definition AnswerHeading :=
         <sDOMAIN :: name,
          sPACKET_SECTION :: PacketSection,
          sNAME :: name, 
          sTYPE :: RRecordType,
          sCLASS :: RRecordClass,
          sTTL :: nat,
          sRDATA :: name,
          sTIME_LAST_CALCULATED :: nat
         >%Heading.

(* Stores an SOA (Start of Authority) record for cached failures, according to RFC 2308. The SOA's TTL is used as the length of time to assume a name failure *)
(* TODO the SOA is technically supposed to go in the Authority section but the packet type doesn't include it *)
Definition FailureHeading :=
          <sDOMAIN :: name,
           sHOST :: name,
           sEMAIL :: name,
           sSERIAL :: nat,
           sREFRESH :: nat,
           sRETRY :: nat,
           sEXPIRE :: nat,
           sMinTTL :: nat,
           sTIME_LAST_CALCULATED :: nat
          >%Heading.

(* Heading for a pending request. 
   Q*, pid, and flags are packet info. Need to store packet info so we can filter the results we get by record type and class. *)
Definition RequestHeading :=
         <sID :: id,  (* unique, ascending *)
          sQNAME :: name,
          sSTAGE :: Stage,      
          sQTYPE :: RRecordType,
          sQCLASS :: RRecordClass,
          sPID :: Bvector 16,
          sFLAGS :: Bvector 16
          (* not storing authority or additional -- needed? *)
         >%Heading.

Definition ReferralRow := @Tuple ReferralHeading.
Definition SLIST_ReferralRow := @Tuple SLIST_ReferralHeading.
Definition AnswerRow := @Tuple AnswerHeading.
Definition FailureRow := @Tuple FailureHeading.
Definition RequestRow := @Tuple RequestHeading.

(* Type of things that a cache query can return. 
Process gets ALL the rows that match; we don't do any filtering. 
Process deals with re-hierarchizing, choosing the best result, etc. *)
Inductive CacheResult :=
| Nope : CacheResult
(* Nonempty lists *)
| Ref : list ReferralRow -> CacheResult
| Ans : list AnswerRow -> CacheResult
(* A failure stores exactly one result (the SOA) *)
| Fail : option FailureRow -> CacheResult.

(* Type used in the cache pointer table, which maps names that exist in the cache
somewhere to the table that they're in.
We need to cache referrals, but never in relation to a specific name, which is why 
they're not in this type. (For a particular request with a name, it will always end in Answer or Failure) *)
Inductive CacheTable :=
| CAnswers
| CFailures.

(* Type for SLIST order. See RFC 1034, page 32 for a more detailed description of the SLIST.

SLIST: a structure which describes the name servers and the
                zone which the resolver is currently trying to query.
                This structure keeps track of the resolver's current
                best guess about which name servers hold the desired
                information; it is updated when arriving information
                changes the guess. 

Here, an SLIST is a list of current referrals we have, sorted by descending match count (so the first one to be used should have the highest match count). (TODO: should also incorporate query count) We store the referrals in one table and their positions in another table. Each request's SLIST is a list of (refId, position).

The SLIST is deleted after a request finishes (ends in an answer or failure). Individual referrals may be cleared when their TTL runs out. *)
Record refPosition :=
  { refId : id;
    refPos : nat }.

Definition DnsRecSchema :=
  Query Structure Schema
        [ relation sREQUESTS has
                   schema
                   RequestHeading;
          
          (* Described above *)
          (* caching optimization opportunity!!!! (ACTION ITEM) *)
          relation sSLIST_ORDERS has schema
                   < sREQID :: id,
                     sORDER :: list refPosition
                            (* id instead + func *)
                   >;
                   (* reqid, refid, refpos *)
          relation sSLIST has
                   schema
                   SLIST_ReferralHeading;

          relation sCACHE_POINTERS has schema
                   < sDOMAIN :: name,
                     sCACHETABLE :: CacheTable 
                     (* would like to have a variant type in the schema *)
                   > ;
          relation sCACHE_ANSWERS has
                   schema
                   AnswerHeading;
          relation sCACHE_REFERRALS has
                   schema
                   ReferralHeading;
          relation sCACHE_FAILURES has
                   schema
                   FailureHeading
        ]
        enforcing [ ]. 
         (* where (fun t t' => True) ] *)
         (* TODO use an attribute constraint to encode that Stage <= length name *)
         (* TODO other invariants are not encoded *)
