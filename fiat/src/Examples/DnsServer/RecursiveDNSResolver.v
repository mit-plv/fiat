Require Import
        Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List
        Bedrock.Word
        Bedrock.Memory
        Fiat.Computation.ListComputations.

Require Import
        Fiat.Computation.IfDec
        Fiat.QueryStructure.Specification.Operations.InsertAll
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.RecursiveDNSSchema.

Import Vectors.VectorDef.VectorNotations.

Local Open Scope vector.
Local Open Scope Tuple_scope.

Definition linkAuthorityToAdditional
           (curTime : timeT)
           (this : QueryStructure RecResolverSchema)
           (authority : list resourceRecord)
           (additional : list resourceRecord)
  : Comp (QueryStructure RecResolverSchema) :=
  authorityAndAdditional <-
                         {aal | NoDup aal /\
                                forall (ns : NS_Record)
                                       (ans : A_Record),
                                  List.In < sDOMAIN :: (ns!sRDATA : DomainName),
                                            sIP :: (ans!sRDATA : W) > aal
                            <-> (List.In (NS_Record2RRecord ns) authority
                                 /\ List.In (A_Record2RRecord ans) additional
                                 /\ ns!sRDATA = ans!sNAME) };
    `(this, _) <- @StatefulInsertAll RecResolverSchema _ _ _ this ``sSLIST
                       () authorityAndAdditional
                       (@QSInsert _)
                       (fun aal _ => ret (< sQUERYCOUNT :: (natToWord _ 0 : W),
                                          sTTL :: (curTime ^+ serverTTL : timeT ) > ++ aal, tt))
                       (fun a s => ret s);
    ret this
.

Definition addAnswersToCache
           (curTime : timeT)
           (this : QueryStructure RecResolverSchema)
           (answers : list resourceRecord)
           (authority : list resourceRecord)
           (additional : list resourceRecord)
  : Comp (QueryStructure RecResolverSchema) :=
  `(this, _) <- @StatefulInsertAll RecResolverSchema _ _ _ this ``sCACHE
   () (answers ++ authority ++ additional)
   (@QSInsert _)
   (fun aal _ => ret (< sTTL :: curTime ^+ cachedTTL,
                        sCACHETYPE :: ``"Answer",
                        sDOMAIN :: aal!sNAME,
                        sQTYPE :: aal!sTYPE,
                        sCACHEDVALUE :: rRecord2CachedValue aal >, tt))
   (fun a s => ret s);
    ret this.

Definition DnsSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure RecResolverSchema,

    Def Constructor "Init" : rep := empty,,

    Def Method3 "Process"
        (this : rep)
        (sourceIP : W)
        (curTime : timeT)
        (p : packet) : rep * packet * option W :=
      If p!"QR" Then
         (* It's a new request! *)
         vs <- For (v in this!sCACHE) (* Search cache for an answer *)
                    Where (p!"question"!"qtype" = CachedQueryTypes_inj v!sQTYPE)
                    Where (curTime <= v!sTTL) (* only alive cached values *)
                    Return (v ! sCACHEDVALUE) ;
         If is_empty vs Then (* Need to launch a recursive query *)
            (* Generate a unique ID for the new request. *)
            (reqIDs <- For (req in this!sREQUESTS)
                            Where (curTime <= req!sTTL)
                            Return (req!sID);
             newID <- { newID | ~ List.In newID reqIDs};
             (* Find the best known servers to query *)
             bestServer <- MaxElement
                             (fun r r' : @Tuple SLISTHeading =>
                                (prefix r!sDOMAIN r'!sDOMAIN)
                                /\ r!sQUERYCOUNT <= r'!sQUERYCOUNT)
                             (For (server in this!sSLIST)
                              Where (prefix server!sDOMAIN p!"question"!"qname")
                              Where (curTime <= server!sTTL)
                              Return server);
             Ifopt bestServer as bestServer Then (* Pick the first server*)
             `(this, _) <- Delete req from this ! sREQUESTS where (req!sTTL <= curTime);
             `(this, b) <- Insert < sID :: newID,
                                    sIP :: sourceIP,
                                    sTTL :: curTime ^+ requestTTL > ++ p into this!sREQUESTS; (* Add the request to the list. *)
             ret (this, (<"id" :: newID,
                          "QR" :: false,
                          "Opcode" :: ``"Query",
                          "AA" :: false,
                          "TC" :: false,
                          "RD" :: true,
                          "RA" :: false,
                          "RCode" :: ``"NoError",
                          "question" :: p!"question",
                          "answers" :: [ ],
                          "authority" :: [ ],
                          "additional" :: [ ] >, Some bestServer!sIP))
             Else (* There are no known servers that can answer this request. *)
             ret (this, (buildempty false ``"ServFail" p, Some sourceIP)) (* This won't happen if the server has been properly initialized with the root servers. *)
            )
       Else                   (* Return cached answer *)
       (answers <- { answers | NoDup answers
                               /\ forall ans : resourceRecord,
                         List.In ans answers <->
                         List.In (A := CachedValue) ans vs };
          If is_empty answers Then (* It must be a cached failure *)
             failures <- { failures | NoDup failures
                                      /\ forall fail : SOA_Record,
                               List.In (A := resourceRecord) fail failures <->
                               List.In (A := CachedValue) fail vs };
             ret (this, (add_additionals failures (buildempty false ``"NXDomain" p), Some sourceIP)) (* Add the SoA record to additional and return negative result*)
          Else
          ret (this, (add_answers answers (buildempty false ``"NoError" p), Some sourceIP)))
         (* Add the answers to the packet.  *)
       Else (* It's a response *)
       (reqs <- For (req in this!sREQUESTS)
                     Where (req!sID = p!"id")
                     Where (req!"question"!"qtype" = p!"question"!"qtype")
                     Return req;
        Ifopt List.hd_error reqs as req Then
          (IfDec p!"RCODE" = ``"NoError" Then
            (If isAnswer p Then    (* We have an answer! We first try to  the outstanding request that this is an answer to. *)
                `(this, reqs) <- Delete req from this!sREQUESTS where (req!sID = p!"id");
                this <- addAnswersToCache curTime this p!"answers" p!"authority" p!"additional";
                ret (this, (<"id" :: req!"id",
                             "QR" :: true,
                             "Opcode" :: req!"Opcode",
                             "AA" :: false,
                             "TC" :: p!"TC",
                             "RD" :: req!"RD",
                             "RA" :: true,
                             "RCode" :: ``"NoError",
                             "question" :: req!"question",
                             "answers" :: p!"answers",
                             "authority" :: p!"authority",
                             "additional" :: p!"additional" >, Some req!sIP) )

           Else  (* We need to issue another query based on the response. *)
           (this <- linkAuthorityToAdditional curTime this p!"authority" p!"additional";
             bestServer <- MaxElement
                             (fun r r' : @Tuple SLISTHeading =>
                                (prefix r!sDOMAIN r'!sDOMAIN)
                                /\ r!sQUERYCOUNT <= r'!sQUERYCOUNT)
                             (For (server in this!sSLIST)
                              Where (prefix server!sDOMAIN p!"question"!"qname")
                              Where (curTime <= server!sTTL)
                              Return server);
             Ifopt bestServer as bestServer Then (* Pick the first server*)
               ret (this, (<"id" :: p!"id",
                            "QR" :: false,
                            "Opcode" :: ``"Query",
                            "AA" :: false,
                            "TC" :: false,
                            "RD" :: true,
                            "RA" :: false,
                            "RCode" :: ``"NoError",
                            "question" :: p!"question",
                            "answers" :: [ ],
                            "authority" :: [ ],
                            "additional" :: [ ] >, Some bestServer!sIP))
             Else
               ret (this, (p, None ) )
         ) )
         Else (* We need to cache a negative response*)
         (soas <- { soas | NoDup soas
                           /\ forall soa : SOA_Record,
                        List.In soa soas <->
                        List.In (A := resourceRecord) soa (p!"authority") };
         Ifopt List.hd_error soas as soa Then (* The response has an SOA *)
           reqType <- SingletonSet (fun b : CachedQueryTypes => req!"question"!"qtype" = CachedQueryTypes_inj b);
           Ifopt reqType as reqType Then
             (`(this, foo) <- Insert (< sTTL :: curTime ^+ cachedTTL,
                                        sCACHETYPE :: ``"Failure",
                                        sDOMAIN :: req!"question"!"qname",
                                        sQTYPE :: reqType,
                                        sCACHEDVALUE :: Failure2CachedValue (<"RCODE" :: (p!"RCODE" : ResponseCode) > ++ soa!sRDATA : FailureRecord ) > )
               into this!sCACHE;
              ret (this, (p, Some req!sIP))  )
            Else (* It's not a record we care to cache *)
             ret (this, (p, Some req!sIP) )
           Else (* If there's no SOA record in authority, don't cache *)
           ret (this, (p, Some req!sIP ) ) ) )
         Else (* The answer is not affiliated with the packet *)
           ret (this, (p, None ) ) )
       }.
