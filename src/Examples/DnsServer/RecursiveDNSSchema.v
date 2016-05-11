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

  Definition AddRawQueryStructureSchema
             {m}
             (raw_qs_schema : RawQueryStructureSchema)
             (new_schemas : Vector.t RawSchema m)
    : RawQueryStructureSchema :=
    {| qschemaSchemas := Vector.append (qschemaSchemas raw_qs_schema) new_schemas;
       qschemaConstraints := [ ] |}.
  
  Fixpoint LiftTuple_AddRawQueryStructureSchema
           {n m : nat}
           (old_schemas : Vector.t RawSchema n)
           (new_schemas : Vector.t RawSchema m)             
           Ridx
           (tup : @RawTuple (GetNRelSchemaHeading old_schemas Ridx))
           {struct old_schemas}
    : @RawTuple
        (GetNRelSchemaHeading (Vector.append old_schemas new_schemas)
                              (Fin.L m Ridx)).
    refine (match old_schemas in Vector.t _ n return
                  forall (Ridx : Fin.t n),
                    @RawTuple (GetNRelSchemaHeading old_schemas Ridx)
                    -> @RawTuple
                         (GetNRelSchemaHeading (Vector.append old_schemas new_schemas)
                                               (Fin.L m Ridx)) with
            | Vector.nil => fun Ridx tup => Fin.case0 (fun _ => _) Ridx
            | Vector.cons _ _ _ => fun Ridx tup => _
            end Ridx tup).
    revert t tup0; pattern n0, Ridx0; apply Fin.caseS; simpl.
    - intros; exact tup0.
    - intros; exact (LiftTuple_AddRawQueryStructureSchema _ _ _ _ _ tup0).
  Defined.

  Definition AddRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (new_schemas : Vector.t RawSchema m)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure (AddRawQueryStructureSchema qs_schema new_schemas))
    : Prop :=
    (forall Ridx tup,
        IndexedEnsemble_In (GetUnConstrRelation r_o Ridx) tup
        <-> IndexedEnsemble_In (GetUnConstrRelation r_n (Fin.L m Ridx)) (LiftTuple_AddRawQueryStructureSchema _ _ Ridx tup)).
  
  (* Define new schema *)

  Fixpoint DecomposeHeading
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
                   (DecomposeHeading attr' (Vector.tl sch) a)
    end sch.

  Fixpoint Tuple_mapHeading
           {m q} {A' B' C}
           (idx : Fin.t m)
           (a : Vector.t C m)
           (f : _ -> _ q) 
           (tup : ilist2 (A := A') (B := B') (Vector.map f a)[@idx])
           {struct idx}
    : ilist2 (B := B') (f a[@idx]).
    refine (match idx in Fin.t m return
                  forall (a : Vector.t C m)
                         (f : _ -> _ q) 
                         (tup : ilist2 (B := B') (Vector.map f a)[@idx]),
                    ilist2 (B := B') (f a[@idx]) with
            | Fin.F1 _ => _
            | Fin.FS _ idx' => _
            end a f tup); clear a tup; intro; try revert idx';
      pattern n, a; apply Vector.caseS.
    - intros; exact tup.
    - simpl; intros; eapply Tuple_mapHeading; eauto.
  Defined.

  Fixpoint Tuple_mapHeading_inv
           {m q} {A' B' C}
           (idx : Fin.t m)
           (a : Vector.t C m)
           (f : _ -> _ q) 
           (tup : ilist2 (B := B') (f a[@idx]))
           {struct idx}
    : ilist2 (A := A') (B := B') (Vector.map f a)[@idx].
    refine (match idx in Fin.t m return
                  forall (a : Vector.t C m)
                         (f : _ -> _ q) 
                         (tup : ilist2 (B := B') (f a[@idx])),
                    ilist2 (B := B') (Vector.map f a)[@idx] with
            | Fin.F1 _ => _
            | Fin.FS _ idx' => _
            end a f tup); clear a tup; intro; try revert idx';
      pattern n, a; apply Vector.caseS.
    - intros; exact tup.
    - simpl; intros; eapply Tuple_mapHeading_inv; eauto.
  Defined.

  Fixpoint Tuple_DecomposeHeading_inj
           {n m}             
           (attrIdx : Fin.t n)
           (heading : Vector.t Type n)
           (a : Vector.t Type m)
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth heading attrIdx)
           (idx : Fin.t m)
           (tup : ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) idx))
           {struct attrIdx}
    : ilist2 (B := @id Type) heading.
    refine
      (match attrIdx in Fin.t n return
             forall (heading : Vector.t Type n)
                    (a : Vector.t Type m)
                    (a_inj : forall idx, Vector.nth a idx -> Vector.nth heading attrIdx)
                    (idx : Fin.t m)
                    (tup : ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) idx)),
               ilist2 (B := @id Type) heading with
       | Fin.F1 _ => fun heading' => _
       | Fin.FS _ attr' => fun heading' => _
       end heading a a_inj idx tup).
    - clear; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      exact (icons2 (B := @id Type)
                    (a_inj idx (ilist2_hd (Tuple_mapHeading idx a _ tup)))
                    (ilist2_tl (Tuple_mapHeading idx a _ tup))).
    - revert attr'; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      exact (icons2 
               (ilist2_hd (Tuple_mapHeading _ _ _ tup0)) 
               (Tuple_DecomposeHeading_inj
                  _ _ attr' t _ a_inj0 _
                  (ilist2_tl (Tuple_mapHeading _ _ _ tup0)))).
  Defined.

  Fixpoint Tuple_DecomposeHeading_proj
           {n m}             
           (attrIdx : Fin.t n)
           (heading : Vector.t Type n)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth heading attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth heading attrIdx),
               a[@a_proj_index attr])
           (tup : ilist2 (B := @id Type) heading)
           {struct attrIdx}
    : ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) (a_proj_index (ith2 tup attrIdx))).
    refine
      (match attrIdx in Fin.t n return
             forall
               (heading : Vector.t Type n)
               (a : Vector.t Type m)
               (a_proj_index : Vector.nth heading attrIdx -> Fin.t m)
               (a_proj : forall (attr : Vector.nth heading attrIdx),
                   a[@a_proj_index attr])
               (tup : ilist2 (B := @id Type) heading),
               ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) (a_proj_index (ith2 tup attrIdx))) with
       | Fin.F1 _ => fun heading' => _
       | Fin.FS _ attr' => fun heading' => _
       end heading a a_proj_index a_proj tup).
    - clear; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      exact (Tuple_mapHeading_inv
               _ a _ (icons2 (B := @id Type) (a_proj (ilist2_hd tup)) (ilist2_tl tup))).
    - revert attr'; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      refine (Tuple_mapHeading_inv
                _ _ _
                (icons2 (B := @id Type)
                        (ilist2_hd tup0)
                        (Tuple_DecomposeHeading_proj _ _ _ _ _ _ a_proj0 (ilist2_tl tup0)))).
  Defined.  

  (* Could fuse this with Decompose Heading, but efficiency shouldn't matter too much. *)
  Definition DecomposeSchema
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
      (DecomposeHeading attr (AttrList (rawSchemaHeading heading)) a).
  
  Definition DecomposeRawQueryStructureSchema
             {m}
             (raw_qs_schema : RawQueryStructureSchema)
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
    : RawQueryStructureSchema :=
    {| qschemaSchemas :=
         DecomposeSchema (Vector.nth (qschemaSchemas raw_qs_schema) schemaIdx)
                         attrIdx a;
       qschemaConstraints := [ ] |}.

(*  ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx))
         ============================
         ilist2 (DecomposeHeading attrIdx (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) a)[@a_proj_index (ith2 tup attrIdx)] =
   ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx))))
  
  Definition DecomposeRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : Prop.
    refine ((forall Ridx, Same_set _ (GetUnConstrRelation r_o Ridx)
                           (GetUnConstrRelation (fst r_n) Ridx)) /\ _).
    assert (forall tup, @ilist2 Type (@id Type) (NumAttr (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx))
    (@DecomposeHeading (NumAttr (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx)) m attrIdx
       (AttrList (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx)) a)[@
    a_proj_index
      (@ith2 Type (@id Type) (NumAttr (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx))
         (AttrList (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx)) tup attrIdx)] = @RawTuple
    (@GetNRelSchemaHeading (numRawQSschemaSchemas (@DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx a))
       (qschemaSchemas (@DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx a))
       (a_proj_index (@GetAttributeRaw (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx) tup attrIdx)))).
    unfold RawTuple.
    intro.
    
    simpl.
    unfold 
    pose (forall tup tup',
              IndexedEnsemble_In (GetUnConstrRelation (fst r_n) schemaIdx) tup
              -> IndexedEnsemble_In (GetUnConstrRelation (snd r_n) (a_proj_index (GetAttributeRaw tup attrIdx))) (Tuple_DecomposeHeading_proj attrIdx _ a _ a_proj tup)).
    Check (fun (tup : @RawTuple (rawSchemaHeading (@GetNRelSchema (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) schemaIdx))) => Tuple_DecomposeHeading_proj attrIdx _ a _ a_proj tup). 
    simpl in P.
    
    /\ (forall tup,
                   IndexedEnsemble_In (GetUnConstrRelation (fst r_n) schemaIdx) tup
                . 

  Definition DecomposeRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
             (RelationMap : forall (Ridx : Fin.t (numRawQSschemaSchemas qs_schema)),
                 RawTuple
                 -> Fin.t ((numRawQSschemaSchemas qs_schema) + m))
             (TupleMap : forall Ridx (tup : RawTuple), RawTuple)
             (RelationMap' : forall (Ridx : Fin.t ((numRawQSschemaSchemas qs_schema) + m)),
                 RawTuple
                 -> Fin.t (numRawQSschemaSchemas qs_schema))
             (TupleMap' : forall Ridx' (tup : RawTuple), RawTuple)
    : Prop :=
    (forall Ridx tup,
        IndexedEnsemble_In (GetUnConstrRelation r_o Ridx) tup
        -> IndexedEnsemble_In (GetUnConstrRelation r_n (RelationMap Ridx tup)) (TupleMap Ridx tup) )
    /\ (forall Ridx' tup',
           IndexedEnsemble_In (GetUnConstrRelation r_n Ridx') tup'
           -> IndexedEnsemble_In (GetUnConstrRelation r_o (RelationMap' Ridx' tup')) (TupleMap' Ridx' tup') ).

  Definition DecomposeRelationMap
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t (numRawQSschemaSchemas qs_schema))
             (attrIdx : Fin.t (NumAttr (rawSchemaHeading (qschemaSchemas qs_schema)[@schemaIdx])))
             (a : Vector.t Type (S m))
             (Ridx : Fin.t (numRawQSschemaSchemas qs_schema))
             (tup : @RawTuple (@GetNRelSchemaHeading (numRawQSschemaSchemas qs_schema) (qschemaSchemas qs_schema) Ridx))
    : Fin.t (numRawQSschemaSchemas qs_schema + m).

    (RelationMap : Fin.t (numRawQSschemaSchemas qs_schema)
                   -> Fin.t ((numRawQSschemaSchemas qs_schema) + m)) *)
