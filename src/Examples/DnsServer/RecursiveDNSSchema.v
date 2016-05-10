Require Import
        Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List.

Require Import
        Fiat.Common.SumType
        Fiat.Computation.ListComputations
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.Packet.

Require Import
        Bedrock.Word
        Bedrock.Memory.


Import Coq.Vectors.VectorDef.VectorNotations.

Local Open Scope vector_scope.

(* The schema, packet structure, and spec are based on the following four RFCs:

RFC 1034: high-level DNS outline
RFC 1035: implementation details
RFC 2308: negative caching -- for more information on failures and SOA records
RFC 1536: common implementation errors and fixes -- for efficiency/security problems *)

(* What subdomain we're on in a question, e.g. new requests get stage None *)
(* when working on a referral, the stage is set to the match count b/t the *)
(* referral and question e.g. question = s.g.com, referral = for g.com, *)
(* stage = match count = 2 (excluding root) *)

(* String definitions *)
Definition sREQUESTS := "Requests".
Definition sSTAGE := "Stage".
Definition sID := "ID".
Definition sIP := "IP".
Definition sRESULT := "Result".
Definition sDOMAIN := "Domain".

Definition sCACHE := "Cache".
Definition sSERVER := "Server".
Definition sPID := "Packet id".
Definition sFLAGS := "Packet flags".

Definition sHOST := "Source host".
Definition sEMAIL := "Contact email".
Definition sSERIAL := "Serial number".
Definition sREFRESH := "Refresh time".
Definition sRETRY := "Retry time".
Definition sEXPIRE := "Expire time".
Definition sMinTTL := "minTTL".
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
Definition sCACHETYPE := "Cache type".
Definition sCACHEDVALUE := "Cached value".

Definition sREQID := "Request ID".
Definition sREFERRALID := "Referral ID".
Definition sMATCHCOUNT := "# labels matched".
Definition sQUERYCOUNT := "# times queried".

Definition sORDER := "SLIST order". (* using referral IDs *)
Definition sSLIST := "SLIST".
Definition sSLIST_ORDERS := "SLIST orders".

Definition sTIME_LAST_CALCULATED := "Time the TTL was last calculated".
Local Open Scope Heading_scope.

(* Heading for a pending request. This is a packet plus a *)
(* unique ID associated with the request and a timeout for *)
(* discarding stale requests. *)
Definition RequestHeading : Heading :=
  < sID :: ID,    (* unique, ascending *)
  sIP :: W,     (* IP address of the request source*)
  sTTL :: timeT > (* Timeout for request *)
  ++ packetHeading.

(* The heading of current resource records for known servers *)
(* (called the SLIST in RFC 1035); these records are augmented *)
(* with a query count field that is used to ensure fair distribution *)
(* of queries among a domain's nameservers. The desing decision here *)
(* is that when new servers are discovered, the resolver will do *)
(* the necessary address/name linking before recording them in this *)
(* list. *)
Definition SLISTHeading :=
  < sQUERYCOUNT :: W, (* number of times we've queried this server *)
  sTTL :: timeT, (* remaining time to live of known server *)
  sDOMAIN :: DomainName, (* Domain of known server *)
  sIP :: W > (* Address of server. *).

(* The cache holds either answers (resource records returned by a *)
(* query) or failures (negative responses). *)
Definition CacheType :=
  BoundedString ["Answer"; "Failure"].

(* Stores an SOA (Start of Authority) record for cached failures, *)
(* according to RFC 2308. The SOA's TTL is used as the length of *)
(* time to assume a name failure. *)

Definition FailureRecord :=
  @Tuple (<"RCODE" :: ResponseCode> ++ SOAHeading).

Definition CachedValueTypes :=
  [ resourceRecord; FailureRecord ].

Definition CachedValue := SumType CachedValueTypes.

Definition rRecord2CachedValue (vrr : resourceRecord)
  : CachedValue := inj_SumType CachedValueTypes (ibound (indexb (Bound := ["Answer"; "Failure"]) ``"Answer")) vrr.

Definition Failure2CachedValue (vrr : FailureRecord)
  : CachedValue := inj_SumType CachedValueTypes (ibound (indexb (Bound := ["Answer"; "Failure"]) ``"Failure")) vrr.

(* Only cache specific resource records in response to a query. *)
Definition CachedQueryTypes :=
  BoundedString (OurRRecordTypes ++ ExtraRRecordTypes).

Definition CachedQueryTypes_inj (rr : CachedQueryTypes) : QType :=
  BoundedIndex_injR rr.

Coercion CachedQueryTypes_inj : CachedQueryTypes >-> QType.
Coercion rRecord2CachedValue : resourceRecord >-> CachedValue.
Coercion Failure2CachedValue : FailureRecord >-> CachedValue.

Definition CacheHeading :=
  < sTTL :: timeT, (* Lifetime of cached value *)
  sCACHETYPE :: CacheType, (* Type of cached value *)
  sDOMAIN:: DomainName, (* Domain of cached Query*)
  sQTYPE :: CachedQueryTypes,  (* Type of cached query *)
  sCACHEDVALUE :: CachedValue >. (* Cached data *)

Definition RecResolverSchema :=
  Query Structure Schema
        [ relation sREQUESTS has schema RequestHeading;

            relation sSLIST has schema SLISTHeading;

            relation sCACHE has schema CacheHeading ]
        enforcing [ ].

(* Should probably restrict cache to have either an answer *)
(* or a failure for a domain and question type. *)

Definition requestTTL : timeT := 500.
Definition serverTTL : timeT := 500.
Definition cachedTTL : timeT := 500.

Section DecomposeEnumField.

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

  (* Define new schema *)

  Fixpoint BreakdownHeading'
             {n m}
             (attr : Fin.t n)
             (sch : Vector.t Type n)
             (a : Vector.t Type m)
             {struct attr}
    : Vector.t (Vector.t Type n) m :=
    match attr in Fin.t n return Vector.t _ n ->  Vector.t (Vector.t _ n) m with
    | Fin.F1 _ =>
      fun sch =>
        Vector.map (fun t => Vector.cons _ t _ (Vector.tl sch)) a
    | Fin.FS _ attr' =>
      fun sch =>
        Vector.map (fun t => Vector.cons _ (Vector.hd sch) _ t)
                   (BreakdownHeading' attr' (Vector.tl sch) a)
    end sch.

  (* Could fuse this with Breakdown Heading, but efficiency shouldn't matter too much. *)
  Definition BreakdownSchema
             {m}
             (heading : RawSchema)
             (attr : Fin.t _)
             (a : Vector.t Type m)
    : Vector.t RawSchema m :=
    Vector.map
      (fun rawheading =>
         {| rawSchemaHeading := Build_RawHeading rawheading;
            attrConstraints := None;
            tupleConstraints := None |})
      (BreakdownHeading' attr (AttrList (rawSchemaHeading heading)) a).

  Definition VectorNthTail
             {n}
           (schemaIdx : Fin.t n)
           (rawSchemas : Vector.t RawSchema (S n))
           (attrIdx : Fin.t (NumAttr (rawSchemaHeading rawSchemas[@Fin.FS schemaIdx])))
    : Fin.t (NumAttr (rawSchemaHeading (Vector.tl rawSchemas)[@schemaIdx])).
    revert schemaIdx attrIdx; pattern n, rawSchemas; eapply Vector.caseS; intros;
      exact attrIdx.
  Defined.

  Fixpoint BreakdownRawQueryStructureSchema'
           {n m}
           (schemaIdx : Fin.t n)
           (rawSchemas : Vector.t RawSchema n)
           (attrIdx : Fin.t (NumAttr (rawSchemaHeading (Vector.nth rawSchemas schemaIdx))))
           (a : Vector.t Type (S m))
           {struct schemaIdx}
    : Vector.t RawSchema (n + m) :=
    match schemaIdx in Fin.t n return
          forall (rawSchemas : Vector.t _ n),
            Fin.t (NumAttr (rawSchemaHeading (Vector.nth rawSchemas schemaIdx)))
            -> Vector.t RawSchema (n + m)  with
    | Fin.F1 _ =>
      fun rawSchemas attrIdx =>
        let newSchema := BreakdownSchema _ attrIdx a in
        Vector.append (Vector.cons _ (Vector.hd newSchema) _ (Vector.tl rawSchemas)) (Vector.tl newSchema)
    | Fin.FS _ attr' =>
      fun rawSchemas attrIdx =>
        Vector.cons _ (Vector.hd rawSchemas) _
                    (BreakdownRawQueryStructureSchema' attr' _ (VectorNthTail _ _ attrIdx) a)
    end rawSchemas attrIdx.

    Definition BreakdownRawQueryStructureSchema
               {m}
               (raw_qs_schema : RawQueryStructureSchema)
               (schemaIdx : Fin.t _)
               (attrIdx : Fin.t _)
               (a : Vector.t Type (S m))
      : RawQueryStructureSchema :=
      {| qschemaSchemas :=
           BreakdownRawQueryStructureSchema' schemaIdx (qschemaSchemas raw_qs_schema) attrIdx a;
         qschemaConstraints := [ ] |}.
