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
            (*where (fun t => ibound (indexb t!"BID") = SumType_index _ t!"B" ) and (fun t t' => True) *);
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

  Definition Tuple_DecomposeRawQueryStructure_proj
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (tup : ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)))
    :  ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx)))).
    unfold DecomposeRawQueryStructureSchema in *; simpl in *.
    unfold GetNRelSchema, DecomposeSchema in *;
      simpl in *.
    erewrite VectorSpec.nth_map by eauto; simpl.
    eapply Tuple_DecomposeHeading_proj; eauto.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_inj
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) idx)))
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)).
    unfold DecomposeRawQueryStructureSchema in *; simpl in *.
    unfold GetNRelSchema, DecomposeSchema in *;
      simpl in *.
    erewrite VectorSpec.nth_map in tup by eauto; simpl.
    simpl in tup.
    eapply Tuple_DecomposeHeading_inj; eauto.
  Defined.

  Fixpoint Tuple_DecomposeRawQueryStructure_Tuple_inj
             {n m : nat}
             (headings : _ )
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type)
          (AttrList
             (rawSchemaHeading
                (Vector.map
                   (fun
                      rawheading : t Type n =>
                    {|
                    rawSchemaHeading := {|
                                        NumAttr := _;
                                        AttrList := rawheading |};
                    attrConstraints := None;
                    tupleConstraints := None |})
                   headings)[@idx])))
             {struct idx}
      : ilist2 (B := @id Type) headings[@idx].
  Proof.
    destruct idx; simpl in *; 
      revert tup; try revert idx;
        pattern n0, headings; apply Vector.caseS.
    - simpl; intros; exact tup.
    - simpl; intros.
      apply Tuple_DecomposeRawQueryStructure_Tuple_inj.
      apply tup.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_inj'
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) idx)))
             (Tuple_inj :
                ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) idx))
                ->
                ilist2 (B := @id Type)
     (DecomposeHeading attrIdx
        (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) a)[@idx] := Tuple_DecomposeRawQueryStructure_Tuple_inj _ idx)
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)).
    eapply Tuple_DecomposeHeading_inj; eauto.
  Defined.

    Fixpoint Tuple_DecomposeRawQueryStructure_Tuple_proj
             {n m : nat}
             (headings : _ )
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) headings[@idx])
             {struct idx}
             :
ilist2 (B := @id Type)
          (AttrList
             (rawSchemaHeading
                (Vector.map
                   (fun
                      rawheading : t Type n =>
                    {|
                    rawSchemaHeading := {|
                                        NumAttr := _;
                                        AttrList := rawheading |};
                    attrConstraints := None;
                    tupleConstraints := None |})
                   headings)[@idx]))
          .
  Proof.
    destruct idx; simpl in *; 
      revert tup; try revert idx;
        pattern n0, headings; apply Vector.caseS.
    - simpl; intros; exact tup.
    - simpl; intros.
      apply Tuple_DecomposeRawQueryStructure_Tuple_proj.
      apply tup.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_proj'
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (tup : ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)))
             (Tuple_proj :
                ilist2 (B := @id Type)
                       (DecomposeHeading attrIdx
                                         (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) a)[@a_proj_index (GetAttributeRaw tup attrIdx)]
                -> ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx))))
              := Tuple_DecomposeRawQueryStructure_Tuple_proj _ (a_proj_index _))
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx)))).
    eapply Tuple_proj; eapply Tuple_DecomposeHeading_proj; eauto.
  Defined.
  
  Definition DecomposeRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : Prop :=
    (forall Ridx, Same_set _ (GetUnConstrRelation r_o Ridx)
                           (GetUnConstrRelation (fst r_n) Ridx))
    /\ (forall Ridx tup,
           IndexedEnsemble_In (GetUnConstrRelation (snd r_n) Ridx) tup
           ->  IndexedEnsemble_In (GetUnConstrRelation (fst r_n) schemaIdx)
                                  (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj _ tup))
    /\ (forall tup,
           IndexedEnsemble_In (GetUnConstrRelation (fst r_n) schemaIdx) tup
           -> IndexedEnsemble_In (GetUnConstrRelation (snd r_n) (a_proj_index (GetAttributeRaw tup attrIdx))) (Tuple_DecomposeRawQueryStructure_proj' _ _ a _ a_proj tup)).

    Definition DecomposeRawQueryStructureSchema_AbsR'
             {m : nat}
             {qs_schema : QueryStructureSchema}
             ( schemaIdx' : BoundedIndex (QSschemaNames qs_schema))
             (schemaIdx := ibound (indexb schemaIdx'))
             {attrIdx' : BoundedIndex (HeadingNames (QSGetNRelSchemaHeading (qs_schema) schemaIdx'))}
             (attrIdx := ibound (indexb attrIdx'))
             (attrIdx_inj : Fin.t _ -> Fin.t _)
             (EnumTypes : Vector.t Type m)
             (f' : Vector.nth (AttrList _) (attrIdx_inj attrIdx) -> SumType EnumTypes)
             (f'' : SumType EnumTypes -> Vector.nth (AttrList _) (attrIdx_inj attrIdx))
             (a_proj_index : Vector.nth (AttrList _) (attrIdx_inj attrIdx) -> Fin.t m :=
                fun attr => SumType_index EnumTypes (f' attr))
             (a_proj : forall (attr : Vector.nth _ (attrIdx_inj attrIdx)), EnumTypes[@a_proj_index attr] :=
                fun attr => SumType_proj EnumTypes (f' attr))
             (a_inj : forall idx, Vector.nth EnumTypes idx -> Vector.nth (AttrList _) (attrIdx_inj attrIdx) :=
                fun idx attr => f'' (inj_SumType EnumTypes idx attr))
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx (attrIdx_inj attrIdx) EnumTypes))
      : Prop :=
      DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                            schemaIdx (attrIdx_inj attrIdx)
                                            EnumTypes a_proj_index a_proj a_inj r_o r_n.

Definition DecomposeRawQueryStructureSchema_empty_AbsR
             {m : nat}
             {qs_schema : QueryStructureSchema}
  : forall (schemaIdx : Fin.t _)
           (attrIdx : Fin.t _)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx),
        DecomposeRawQueryStructureSchema_AbsR
          schemaIdx attrIdx a a_proj_index a_proj a_inj
          (DropQSConstraints (QSEmptySpec qs_schema))
          (DropQSConstraints (QSEmptySpec qs_schema),
           imap2 (fun ns : RawSchema => rawRel (RelationSchema:=ns))
                 (Build_EmptyRelations
                    (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)))).
Proof.
  intros.
  repeat split; simpl; intros; intuition.
  - unfold GetUnConstrRelation in H.
    rewrite <- ith_imap2,
     EmptyRefinements.ith_Bounded_BuildEmptyRelations in H.
    simpl in H; unfold IndexedEnsemble_In in H; destruct_ex;
      inversion H.
  - unfold GetUnConstrRelation, DropQSConstraints, QSEmptySpec in H.
    rewrite <- ith_imap2 in H.
    simpl in H.
    rewrite EmptyRefinements.ith_Bounded_BuildEmptyRelations in H.
    simpl in H; unfold IndexedEnsemble_In in H; destruct_ex;
      inversion H.
Qed.

Definition DecomposeRawQueryStructureSchema_Insert_AbsR_neq
             {m : nat}
             {qs_schema : QueryStructureSchema}
  : forall (schemaIdx : Fin.t _)
           (attrIdx : Fin.t _)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
           r_o
           r_n,
    DecomposeRawQueryStructureSchema_AbsR
      schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
    ->
    forall Ridx tup,
      Ridx <> schemaIdx
      -> DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj
        (UpdateUnConstrRelation r_o Ridx (EnsembleInsert tup (GetUnConstrRelation r_o Ridx)))
        (UpdateUnConstrRelation (fst r_n) Ridx (EnsembleInsert tup (GetUnConstrRelation (fst r_n) Ridx)), snd r_n).
Proof.
  repeat split; simpl; intros.
  - destruct (fin_eq_dec Ridx Ridx0); subst;
      unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite !ith_replace2_Index_eq.
      unfold Included; intros.
      inversion H1; subst; intuition.
      * econstructor; eauto.
      * econstructor 2; eapply (proj1 H Ridx0); apply H2.
    + rewrite !ith_replace2_Index_neq; eauto.
      unfold Included; intros; eapply (proj1 H Ridx0); apply H1.
  - destruct (fin_eq_dec Ridx Ridx0); subst;
      unfold GetUnConstrRelation, UpdateUnConstrRelation.   
    + rewrite !ith_replace2_Index_eq.
      unfold Included; intros.
      inversion H1; subst; intuition.
      * econstructor; eauto.
      * econstructor 2; eapply (proj1 H Ridx0); apply H2.
    + rewrite !ith_replace2_Index_neq; eauto.
      unfold Included; intros; eapply (proj1 H Ridx0); apply H1.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation.  
    rewrite !ith_replace2_Index_neq; eauto.
    eapply (proj2 H); eauto.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.  
    rewrite !ith_replace2_Index_neq in H1; eauto.
    eapply (proj2 H); eauto.
Qed.

Lemma Tuple_DecomposeRawQueryStructure_inj_inverse
      {m : nat}
      {qs_schema : QueryStructureSchema}
  : forall (schemaIdx : Fin.t _)
           (attrIdx : Fin.t _)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
           tup,
    Tuple_DecomposeRawQueryStructure_inj' schemaIdx attrIdx a a_inj
                                          (a_proj_index (GetAttributeRaw tup attrIdx))
                                          (Tuple_DecomposeRawQueryStructure_proj' schemaIdx attrIdx a a_proj_index a_proj
                                                                                 tup) = tup.
Admitted.

Definition DecomposeRawQueryStructureSchema_Insert_AbsR_eq
             {m : nat}
             {qs_schema : QueryStructureSchema}
  : forall (schemaIdx : Fin.t _)
           (attrIdx : Fin.t _)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
           r_o
           r_n,
    DecomposeRawQueryStructureSchema_AbsR
      schemaIdx attrIdx a a_proj_index a_proj a_inj
      r_o r_n
    ->
    forall tup,
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj
        (UpdateUnConstrRelation r_o schemaIdx (EnsembleInsert tup (GetUnConstrRelation r_o schemaIdx)))
        (UpdateUnConstrRelation (fst r_n) schemaIdx (EnsembleInsert tup (GetUnConstrRelation (fst r_n) schemaIdx)),
         UpdateUnConstrRelation (snd r_n)
                                (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))
                                (EnsembleInsert {| elementIndex := elementIndex tup;
                                                   indexedElement :=
                                                     Tuple_DecomposeRawQueryStructure_proj'
                                                       _ _ _ _ a_proj
                                                       (indexedElement tup) |} (GetUnConstrRelation (snd r_n) (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))))).
  repeat split; simpl; intros.
  - destruct (fin_eq_dec schemaIdx Ridx); subst;
      unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite !ith_replace2_Index_eq.
      unfold Included; intros.
      inversion H0; subst; intuition.
      * econstructor; eauto.
      * econstructor 2; eapply (proj1 H Ridx); apply H1.
    + rewrite !ith_replace2_Index_neq; eauto.
      unfold Included; intros; eapply (proj1 H Ridx); apply H0.
  - destruct (fin_eq_dec schemaIdx Ridx); subst;
      unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite !ith_replace2_Index_eq.
      unfold Included; intros.
      inversion H0; subst; intuition.
      * econstructor; eauto.
      * econstructor 2; eapply (proj1 H Ridx); apply H1.
    + rewrite !ith_replace2_Index_neq; eauto.
      unfold Included; intros; eapply (proj1 H Ridx); apply H0.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
    + rewrite !ith_replace2_Index_eq in *.
      simpl in H0.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))); subst.
      rewrite !ith_replace2_Index_eq in H0.
      destruct H0 as [? [? | ?] ].
      * destruct tup; injections; econstructor; econstructor.
        f_equal; simpl.
        apply Tuple_DecomposeRawQueryStructure_inj_inverse.
      * destruct (proj1 (proj2 H) (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx)) tup0).
        econstructor; eauto.
        econstructor; econstructor 2; eauto.
      * rewrite !ith_replace2_Index_neq in H0 by eauto.
        destruct (proj1 (proj2 H) Ridx tup0 H0); eauto.
        econstructor; econstructor 2; eauto.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
    + rewrite !ith_replace2_Index_eq in H0.
      destruct H0 as [? [? | ?] ]; subst.
      * try rewrite !ith_replace2_Index_eq.
        econstructor; econstructor; f_equal.
      * destruct (proj2 (proj2 H) tup0).
        econstructor; eauto.
        simpl in *.
        econstructor; simpl.
        destruct tup; simpl in *.
        clear r_o H H0 a_inj.
        unfold In.
        destruct (fin_eq_dec (a_proj_index (GetAttributeRaw tup0 attrIdx))
                             (a_proj_index (GetAttributeRaw indexedElement attrIdx))
                 ); subst; 
          [ | rewrite !ith_replace2_Index_neq; eauto].
        match goal with
          |- ith2 (replace_Index2 _ _ ?idx _) ?idx' _ =>
          assert (idx = idx')
        end.
Admitted.

Lemma UnConstrFreshIdx_Same_Set_Equiv {ElementType} :
  forall (ensemble ensemble' : @IndexedEnsemble ElementType),
    Same_set _ ensemble ensemble'
    -> forall bound,
      UnConstrFreshIdx ensemble bound
      <-> UnConstrFreshIdx ensemble' bound.
Proof.
  unfold Same_set, UnConstrFreshIdx; intros.
  intuition.
  - eapply H; eapply H1; eauto.
  - eapply H; eapply H0; eauto.
Qed.

Lemma refine_UnConstrFreshIdx_Same_Set_Equiv {ElementType} :
  forall (ensemble ensemble' : @IndexedEnsemble ElementType),
    Same_set _ ensemble ensemble'
    -> refine {idx : nat | UnConstrFreshIdx ensemble idx}
              {idx : nat | UnConstrFreshIdx ensemble' idx}.
Proof.
  intros.
  unfold refine; intros; computes_to_inv; computes_to_econstructor.
  rewrite UnConstrFreshIdx_Same_Set_Equiv; eauto.
Qed.

Corollary refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv
  {m : nat}
  {qs_schema : RawQueryStructureSchema}
  (schemaIdx : Fin.t _)
  (attrIdx : Fin.t _)
  (a : Vector.t Type m)
  (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
  (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
  (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
  (r_o : UnConstrQueryStructure qs_schema)
  (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
  : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
    -> forall Ridx,
    refine {idx : nat | UnConstrFreshIdx (GetUnConstrRelation r_o Ridx) idx}
           {idx : nat | UnConstrFreshIdx (GetUnConstrRelation (fst r_n) Ridx) idx}.
Proof.
  intros; apply refine_UnConstrFreshIdx_Same_Set_Equiv.
  apply (proj1 H Ridx).
Qed.

Fixpoint Iterate_Equiv_QueryResultComp
         m
         {ResultT}
         (heading : RawHeading)
         (headings : Fin.t m -> RawHeading)
         (Ensembles : forall (idx : Fin.t m),
             @IndexedEnsemble (@RawTuple (headings idx)))
         (inj_Tuple : forall (idx : Fin.t m),
             @RawTuple (headings idx)
             -> @RawTuple heading)
         (body : @RawTuple heading -> Comp (list ResultT))
         {struct m}
  : Comp (list ResultT) :=
  match m return
        forall (headings : Fin.t m -> RawHeading),
          (forall (idx : Fin.t m),
              @IndexedEnsemble (@RawTuple (headings idx)))
          -> (forall (idx : Fin.t m),
                 @RawTuple (headings idx)
                 -> @RawTuple heading)
          -> Comp (list ResultT)
         with
         | 0 => fun _ _ _ => (ret List.nil)
         | S m =>
           fun headings Ensembles inj_Tuple =>
             res <- QueryResultComp (Ensembles Fin.F1)
                 (fun tup => body (inj_Tuple Fin.F1 tup));
             res' <- Iterate_Equiv_QueryResultComp heading
                  (fun idx => headings (Fin.FS idx))
                  (fun idx => Ensembles (Fin.FS idx))
                  (fun idx tup => (inj_Tuple (Fin.FS idx) tup))
                  body
             ;
             ret (List.app res res')
          end headings Ensembles inj_Tuple.

Lemma refine_Iterate_Equiv_QueryResultComp
  {m : nat}
  {qs_schema : RawQueryStructureSchema}
  {ResultT}
  (schemaIdx : Fin.t _)
  (body : @RawTuple _ -> Comp (list ResultT))
  (attrIdx : Fin.t _)
  (a : Vector.t Type m)
  (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
  (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
  (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
  (r_o : UnConstrQueryStructure qs_schema)
  (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
  : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
    ->
    refine (UnConstrQuery_In r_o schemaIdx body)
           (Iterate_Equiv_QueryResultComp
              _ _
              (GetUnConstrRelation (snd r_n))
              (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj) body).
Admitted.

Arguments DecomposeRawQueryStructureSchema : simpl never.
Arguments DecomposeRawQueryStructureSchema_AbsR : simpl never.
Arguments inj_SumType : simpl never.
Arguments inj_SumType : simpl never.
Arguments SumType_proj : simpl never.
Arguments SumType_index : simpl never.
Arguments Vector.nth _ _ _ !_ / .

Definition EEImpl : FullySharpened EESpec.
    unfold EESpec.
    start sharpening ADT.
    start_honing_QueryStructure'.
    let AbsR' := constr:(@DecomposeRawQueryStructureSchema_AbsR' _ EESchema ``"foo" ``"B"
                                                                id EnumTypes id id) in  hone representation using AbsR'.
    {
      simplify with monad laws.
      apply refine_pick_val.
      apply DecomposeRawQueryStructureSchema_empty_AbsR.
    }
    { (* Insert *)
      unfold DecomposeRawQueryStructureSchema_AbsR' in *.
      simpl in *; simplify with monad laws; cbv beta; simpl.
      rewrite (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0 Fin.F1).
      unfold H; eapply refine_under_bind; intros.
      apply refine_under_bind_both; intros.
      apply refine_pick_val.
      eapply (DecomposeRawQueryStructureSchema_Insert_AbsR_eq H0).
      finish honing.
    }
    { (* Query *)
      unfold DecomposeRawQueryStructureSchema_AbsR' in *.
      simpl in *; simplify with monad laws; cbv beta; simpl.
      rewrite refine_For; simplify with monad laws.
      rewrite (refine_Iterate_Equiv_QueryResultComp _ H0).
      simpl.
      simplify with monad laws.
      unfold Tuple_DecomposeRawQueryStructure_inj'.
      simpl.
      unfold GetAttributeRaw; simpl.
      unfold icons2; simpl.
      unfold ilist2_tl, ilist2_hd; simpl.
      (* More refinements here. *)

Abort.
End DecomposeEnumField.
