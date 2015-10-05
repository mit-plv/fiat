Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms.

Require Import
        Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsLemmas.

Require Import Fiat.Examples.DnsServer.DnsSchema_new.

(* Only Init, MakeId, and Process should be public methods. The rest are private, for internal use. *)

(* So long strings of Ascii Bool Bool... won't show up in Set Printing All *)
Definition Init := "Init".
Definition MakeId := "MakeId".
Definition AddRequest := "AddRequest".
Definition GetRequestStage := "GetRequestStage".
Definition UpdateRequestStage := "UpdateRequestStage".
Definition GetServerForLongestSuffix := "GetServerForLongestSuffix".
Definition InsertResultForDomain := "InsertResultForDomain".
Definition DeletePendingRequestInfo := "DeletePendingRequestInfo".
Definition DeleteCachedNameResult := "DeleteCachedNameResult".
Definition PacketToReferralRows :="PacketToReferralRows".
Definition InsertReferralRowsIntoCache := "InsertReferralRowsIntoCache".
Definition ReferralRowsToSLIST := "ReferralRowsToSLIST".
Definition GetFirstReferralAndUpdateSLIST := "GetFirstReferralAndUpdateSLIST".
Definition SortSLIST := "SortSLIST".
Definition UpdateCacheReferralsAndSLIST := "UpdateCacheReferralsAndSLIST".
Definition UpdateTTLs := "UpdateTTLs".
Definition Process := "Process".

Definition DnsRecSig : ADTSig :=
  ADTsignature {
      Constructor Init : unit -> rep,

      (* request state methods *)
      Method MakeId : rep * name -> rep * id,

     (* TTL *)
      Method UpdateTTLs : rep * time -> rep * bool,

      (* Main method. Talks to an outside "wrapper" in continuation-passing style. Given the time and something from the wrapper, figures out what to do with it and returns a response that may be an error, answer, or request for the wrapper to send a question to another server. *)
      Method Process : rep * time * FromOutside -> rep * ToOutside
    }.


(* Helper functions *)

Definition upperbound' := upperbound (fun x => x).

Definition nonempty {A : Type} (l : list A) := negb (beq_nat (List.length l) 0).

(* Double the monad, double the fun! *)
Fixpoint iterate {A B : Type} {R : RepHint} (r : rep) (f : rep -> A -> (Comp (rep * B)))
        (l : list A) : Comp (rep * list B) :=
    match l with
    | nil => ret (r, nil)
    | x :: xs =>
      resHead <- f r x;
        let (rHead, ansHead) := resHead in
        resTail <- iterate rHead f xs;
          let (rEnd, ansEnd) := resTail in
          ret (rEnd, ansHead :: ansEnd)
    end.

Definition listToOption {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | x :: _ => Some x
  end.

(* Used to join the authority and additional fields for producing a referral row *)
Definition list_join {A B : Type} f (l1 : list A) (l2 : list B)
  : list (A * B) :=
  filter f (list_prod l1 l2).

(* The amount of time a record has left to live (unintentionally dramatic) *)
Definition timeLeft TTL currTime timeLastCalculated :=
  TTL - (currTime - timeLastCalculated).

Definition hasTimeLeft_prop TTL currTime timeLastCalculated :=
  timeLeft TTL currTime timeLastCalculated > 0.

Definition hasTimeLeft_comp TTL currTime timeLastCalculated :=
  match nat_compare (timeLeft TTL currTime timeLastCalculated) 0 with
  | Gt => true
  | _ => false
  end.

(* Set Printing All. *)


Notation "qs ! R" :=
  (GetRelationBnd qs {| bindex := R; indexb := _ |})
  : QuerySpec_scope.

Definition IndexedEnsemble_In
           (U : Type) (x : U) (A : @IndexedEnsemble U) :=
  exists idx, A {| elementIndex := idx;
                   indexedElement := x |}.

Arguments IndexedEnsemble_In [_] _ A%QuerySpec.

(* Stub Methods. *)
Definition UpdateTTLs_stub {A} (r : A) (t : time) := ret (r, false).

Fixpoint InsertAll {qsSchema}
         {A}
         (r : QueryStructure qsSchema)
         (idx : BoundedIndex (QSschemaNames qsSchema))
         (rowFunc : A -> Comp _)
         (As : list A) :=
  (* monad iteration instead. TODO param over table *)
  match As with
  (* this shouldn't happen since an answer must have at >= 1 answer record *)
  | nil => ret (r, false)
  | a :: As' =>
    newRow <- rowFunc a;
    res <- QSInsert r (ibound (indexb idx)) newRow;
      let (r'', _) := res in
      InsertAll r'' idx rowFunc As'
  end.

Definition isQuestion (p : packet) :=
  match p!"answers", p!"authority", p!"additional" with
  | nil, nil, nil => true
  | _, _, _ => false
  end.

Definition isAnswer (p : packet) := negb (is_empty (p!"answers")).

Definition isReferral (p : packet) :=
  is_empty (p!"answers")
  && (negb (is_empty (p!"authority")))
  && (negb (is_empty (p!"additional"))).
Set Printing Implicit.

Definition linkAuthorityAnswer (p : packet) timeArrived: list (@Tuple ReferralHeading) :=
  let authRdataMatchesAddlName (tup2 : resourceRecord * resourceRecord) :=
      match (fst tup2)!sRDATA with
      | inl n => beq_name n ((snd tup2)!sNAME)
      | _ => false
      end in
  let auth_addl_join := list_join authRdataMatchesAddlName (p!"authority") (p!"additional") in
  map (fun tup_pairs : resourceRecord * resourceRecord =>
         let (auth, addl) := tup_pairs in
         < sREFERRALDOMAIN :: (auth!sNAME : name),
          sRTYPE :: (auth!sTYPE : RRecordType),
          sRCLASS :: (auth!sCLASS : RRecordClass),
          sRTTL :: (auth!sTTL : nat),
          (* inline RDATA and additional record *)
          sSERVERDOMAIN :: (addl!sNAME : name),
          sSTYPE :: (addl!sTYPE : RRecordType),
          sSCLASS :: (addl!sCLASS : RRecordClass),
          sSTTL :: (addl!sTTL : nat),
          sSIP :: match (addl!sRDATA) with
                  | inl n => n
                  | _ => [ ]
                  end,
          (* IP in RDATA of additional record *)
          sTIME_LAST_CALCULATED :: timeArrived>) auth_addl_join.

(* Given a list of *new* referralrows (i.e. came from a packet, or is SBELT), *)
(* put them in the request's SLIST, and return the current best referral. Calls many *)
(* helper functions. *)

Definition UpdateCacheReferralsAndSLISTSpec (r : QueryStructure DnsRecSchema)
           (currTime : time) (reqId : id) (pac : packet) (referrals : list ReferralRow)
                : Comp (_ * ToOutside) :=
             (* Insert referrals into cache *)
             r'' <- InsertAll r ``sCACHE_REFERRALS (fun x => ret x) referrals;
             (* Get name of the original question *)
             req <- For (req in (fst r'')!sREQUESTS)
                         Where (req!sID = reqId)
                         Return req!sQNAME;
             match req with
             | [ questionDomain ] =>
               (* TODO: filter by type, class *)
               (* Put the referrals into the request's sLIST *)
               validReferrals <- [[ ref in referrals |
                                    ~ exists slist_ref,
                                        IndexedEnsemble_In slist_ref ((fst r'')!sSLIST)
                                        /\ (ref!sREFERRALDOMAIN = slist_ref!sREFERRALDOMAIN)]];
               r''' <- InsertAll (fst r'') ``sSLIST
                        (fun curRef : ReferralRow =>
                           (* Augment a referral row with the additional fields in the SLIST *)
                           (* referral row (ids, counts) *)
                           (* Calculate match count of referral domain to question domain *)
                           (* e.g. ref domain = g.com, question domain = s.g.com -> count = 2 *)
                           longestSharedSuffix <- { name' : name |
                                                    IsPrefix name' curRef!sREFERRALDOMAIN
                                                    /\ IsPrefix name' [""]
                                                    /\ forall name'' : name,
                                                        IsPrefix name'' curRef!sREFERRALDOMAIN
                                                        -> IsPrefix name'' [""]
                                                        -> List.length name' >= List.length name'' };
                         (* Generate unique ids that are all greater than the existing ids *)
                         newID <- { id : nat | forall ref,
                                      IndexedEnsemble_In ref (r!sSLIST)
                                      -> ref!sREQID = reqId
                                      -> id > ref!sREFERRALID };
                         ret (<sREQID :: reqId, sREFERRALID :: newID,
                              sMATCHCOUNT :: (List.length longestSharedSuffix),
                              sQUERYCOUNT :: 0 (* New Row / hasn't been queried before*) >
                              ++ curRef))
                        referrals;
               (* Get the "best" referral (the one with the lowest position in SLIST), *)
               (* add 1 to its query count, update the request's match count, and  *)
               (* then return that "best" referral *)
               r4 <- Update slist_ref from (fst r''')!sSLIST as slist_ref'
                       making slist_ref'!sQUERYCOUNT = slist_ref!sQUERYCOUNT + 1
                       where (slist_ref!sREQID = reqId /\
                              forall slist_ref'',
                                IndexedEnsemble_In slist_ref'' (r!sSLIST)
                                -> slist_ref''!sMATCHCOUNT <= slist_ref!sMATCHCOUNT);
                match r4 with
                | (r5, bestRef :: _) =>
                   r6 <- Update req from r5!sREQUESTS as req'
                            making req'!sSTAGE = Some bestRef!sMATCHCOUNT
                            where (req!sID = reqId);
                (* Send the same question to the server with the IP given in the referral *)
                   ret (fst r6, ServerQuestion reqId bestRef!sSIP pac)
                | (r5, _) => ret (r5, NoReferralsLeft reqId pac)
                end
               | _ => ret (fst r'', NoReferralsLeft reqId pac)
             end.

Definition DnsSpec_Recursive : ADT (*DnsRecSig*) _ :=
  QueryADTRep DnsRecSchema {
    Def Constructor0 Init : rep := empty,

      (* ----- REQUESTS *)

      (* Generate a unique id for a request. Wrapper's responsibility to use this id for everything concerning this request and pass the correct id into functions. Requests can have (different id, same name) but not (same id, different name) since a packet can only contain one question *)
      Def Method1 MakeId (r : rep) (n : name) : rep * id :=
      (* Make this a straightforward Pick *)
      freshAscendingId <- {idx : nat | forall n, IndexedEnsemble_In n (r!sREQUESTS)
                                                 -> idx > n!sID };
        ret (r, freshAscendingId),

        (* ---------- TTL *)
     (* Decrement the TTLs of everything and store currTime in time_last_calculated,
        delete pointers to any SLIST referrals or cached rows soon to be deleted,
        and delete them (the ones with TTL 0)
       (TODO: code could be more efficient if we only updated those in a particular table,
        but then it would be longer)

     As a recurrence relation:
     TTL_(n+1) = TTL_n - (time_right_now - time_last_calculated) *)
        (* TODO: store the absolute time that the record should be deleted/ignored instead (when it's first added to a table), and calculate the updated TTL again when returning it *)
        Def Method1 UpdateTTLs (r : rep) (currTime : time) : rep * bool :=
          (* Decrement all TTLs and set the time_last_calculated to now *)
          q <- Update c from r!sSLIST as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sSTTL = timeLeft c!sSTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          q <- Update c from (fst q)!sCACHE_REFERRALS as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sSTTL = timeLeft c!sSTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          q <- Update c from (fst q)!sCACHE_ANSWERS as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sTTL = timeLeft c!sTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          q <- Update c from (fst q)!sCACHE_FAILURES as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!"minTTL" = timeLeft c!"minTTL" currTime c!sTIME_LAST_CALCULATED)
            where True;
          (* Delete all rows from SLIST or cache with no time left to live *)
          q <- Delete row from (fst q)!sSLIST where row!sSTTL = 0;
          qref <- Delete row from (fst q)!sCACHE_REFERRALS where row!sSTTL = 0;
          qans <- Delete row from (fst qref)!sCACHE_ANSWERS where row!sTTL = 0;
          qfail <- Delete row from (fst qans)!sCACHE_FAILURES where row!"minTTL" = 0;
          q <- Delete row from (fst qfail)!sCACHE_POINTERS where
          ((exists ref, List.In ref (snd qref) /\ row!sDOMAIN = ref!sREFERRALDOMAIN)
             \/ (exists ref, List.In ref (snd qans) /\ row!sDOMAIN = ref!sDOMAIN)
             \/ (exists ref, List.In ref (snd qfail) /\ row!sDOMAIN = ref!sDOMAIN));

            (* For cache tables: get all to-be-deleted rows' names and delete those from cache pointers *)
          ret (fst q, true),

          (* ----- MAIN METHOD *)

      (* Main method. Talks to an outside "wrapper" in continuation-passing style. Given the time and something from the wrapper, figures out what to do with it and returns a response that may be an error, answer, or request for the wrapper to send a question to another server. *)
          (* TODO need to inline other functions; stubs for now *)
          (* TODO rep is not threaded through in Process *)
          Def Method4 Process (r : rep) (timeArrived : time)
              (reqId : id) (pac : packet) (failure : option SOA)
          : rep * ToOutside :=
            let SBELT := @nil ReferralRow in (* TODO add root ip *)

            (* --- FUNCTION START --- *)
          (* Is the request pending? (Are we currently working on it?) *)
          pendingReq <- For (req in r!sREQUESTS)
                        Where (reqId = req!sID)
                        Return req;
          (* There should be either one or none *)
          Ifopt (hd_error pendingReq) as pendingReq' Then
            (* Pending *)
            if isQuestion pac then
              ret (r, InvalidQuestion reqId)
            else
              (* Figure out if the packet is an answer, failure, or referral *)
              (* doesn't thoroughly check for malformed packets, e.g. contains answer and failure *)
              if isReferral pac then
                referralRows <- ret (linkAuthorityAnswer pac timeArrived);
                UpdateCacheReferralsAndSLISTSpec r reqId timeArrived pac referralRows
              (* Some variety of done (since not a referral) *)
              else
                nm <- For (req in r!sREQUESTS)
                      Where (reqId = req!sID)
                      Return (req!sQNAME);
                match nm with
                | reqName :: _  =>
                  (* Delete the pending request's entry in the request's table, *)
                  (* its SLIST order, and its SLIST *)
                  r1 <- Delete row from r!sREQUESTS where row!sID = reqId;
                  r3 <- Delete row from (fst r1)!sSLIST where row!sREQID = reqId;
                    (* Delete a cached name's entry in the cache pointer table, as well *)
                  (* as all relevant cached answers or failures (note, does not delete *)
                  (* things from referrals or SLIST). *)
                  results <- For (pointer in (fst r3)!sCACHE_POINTERS)
                             Where (pointer!sDOMAIN = reqName)
                             Return (pointer!sCACHETABLE);
                  r4 <- match results with
                        (* domain to be deleted is not actually in cache *)
                        | [ ] => ret (r, Nope)
                        | tbl :: _ =>
                          r1 <- Delete row from r!sCACHE_POINTERS where row!sDOMAIN = reqName;
                        match tbl with
                        | CAnswers =>
                          answer_res <- Delete row from (fst r1)!sCACHE_ANSWERS where row!sDOMAIN = reqName;
                        ret (fst answer_res, Ans (snd answer_res))
                        | CFailures =>
                          failure_res <- Delete row from (fst r1)!sCACHE_FAILURES where row!sDOMAIN = reqName;
                        ret (fst failure_res, Fail (listToOption (snd failure_res)))
                        end
                        end;
                if isAnswer pac then
                  (* Update cache *)
                  (* Given a time and either an answer or a failure, convert that to the *)
                  (* correct row type and insert the rows in the correct cache table. *)
                  (* Assumes that someone has already checked that the domain is not in any *)
                  (* of the caches. *)
                  r1 <- Insert <sDOMAIN :: reqName, sCACHETABLE :: CAnswers >%Tuple into (fst r4)!sCACHE_POINTERS;
                  r2 <- InsertAll (fst r1) ``sCACHE_ANSWERS
                     (fun ans =>
                        ret (< sDOMAIN :: reqName,
                             sPACKET_SECTION :: PAnswer,
                             sTIME_LAST_CALCULATED :: timeArrived> ++ ans))
                     (pac!"answers");
                  r3 <- InsertAll (fst r2) ``sCACHE_ANSWERS
                     (fun ans =>
                        ret (< sDOMAIN :: reqName,
                             sPACKET_SECTION :: PAuthority,
                             sTIME_LAST_CALCULATED :: timeArrived> ++ ans))
                     (pac!"authority");
                  r4 <- InsertAll (fst r3) ``sCACHE_ANSWERS
                     (fun ans =>
                        ret (< sDOMAIN :: reqName,
                             sPACKET_SECTION :: PAdditional,
                             sTIME_LAST_CALCULATED :: timeArrived> ++ ans))
                     (pac!"additional");
                  (* Done, forward it on *)
                  ret (fst r4, ClientAnswer reqId pac)
                else match failure with
                     (* Failure. Done, forward it on *)
                     | Some soa =>
                       (* Update cache *)
                       r1 <- Insert <sDOMAIN :: reqName, sCACHETABLE :: CFailures > into (fst r4)!sCACHE_POINTERS;
                     r2 <- Insert (<sDOMAIN :: reqName, sTIME_LAST_CALCULATED :: timeArrived>
                                                  ++ soa) into (fst r1)!sCACHE_FAILURES;
                       ret (fst r2, ClientFailure reqId pac soa)
                     | None => ret (fst r4, MissingSOA reqId pac) (* will also result in request del *)
                     end
                | _ => ret (r, InvalidId reqId pac)
                end
          Else
            (* Not pending *)
            if negb (isQuestion pac) then (* is a referral, answer, or failure *)
              ret (r, InvalidResponse reqId)
            else
              (* But have we seen it before? *)
              (* For a given name, look in the cache and return the rows that match the longest suffix of the name. Subcase: if there already is a concrete answer/failure/referral for the name, return that. *)
              let reqName := (pac!"questions"!"qname") in
              (* Check if we have cached results for reqName *)
              results <- For (pointer in r!sCACHE_POINTERS)
                      Where (pointer!sDOMAIN = reqName)
                      Return (pointer!sCACHETABLE);
                (* TODO: filter by packetsection = answer? are authority/additional useful? *)
                res <- (
                                suffixes <- For (ans in r!sCACHE_REFERRALS)
                                         Where (IsPrefix ans!sREFERRALDOMAIN reqName)
                                         Return ans;
                                let domainLength (tup : ReferralRow) := List.length tup!sREFERRALDOMAIN in
                                longestSuffixes <- [[suffix in suffixes | upperbound domainLength suffixes suffix]];
                                match results with
                                | CAnswers :: _ =>
                                  (* There may be multiple rows in Answers, containing various answer/authority/addl *)
                                  (* This returns all of them and leaves it to Process to hierarchize/query them *)
                                  (* (they should all be for the same domain though; the longest suffix is unique *)
                                  nameRes <- For (f in r!sCACHE_ANSWERS)
                                          Where (f!sDOMAIN = reqName)
                                          Return f;
                                (* TTL* *)
                                ret (r, Ans nameRes)

                                | CFailures :: _ =>
                                  (* This domain [s.g.com] failed. If we have any results for the longest prefix, *)
                                  (* return them and label them as referrals. (e.g. an answer for [g.com])  *)
                                  (* Otherwise, return failure. *)
                                  If (is_empty longestSuffixes) Then
                                     nameRes <- For (f in r!sCACHE_FAILURES)
                                     Where (f!sDOMAIN = reqName)
                                     Return f;
                                (* TTL* *)
                                ret (r, Fail (listToOption nameRes))
                                    Else
                                    ret (r, Ref longestSuffixes)

                                | [ ] =>
                                  (* name has nothing cached for it, but we might have referrals for subdomains *)
                                  If (is_empty longestSuffixes) Then
                                     ret (r, Nope) (* this name has nothing cached for it *)
                                     Else
                                     ret (r, Ref longestSuffixes)
                                end);
                let (r, suffixResults) := res in
                match suffixResults with
                (* Yes we have seen it *)
                (* TODO: we may need to modify the return packet  *)
                | Fail failure =>
                  (* Return the exactly one SOA row from cache as a packet *)
                  match failure with
                     (* Failure. Done, forward it on *)
                     | None => ret (r, InternalCacheError reqId pac)
                     (* TTL* *)
                     | Some soa =>
                       ret (r, ClientFailure reqId pac (toPacket_soa soa))
                     end
                | Ans answers =>
                  (* filter out Authority and Additional *)
                  actualAns <- [[ record in answers | record!sPACKET_SECTION = PAnswer ]];
                  match actualAns with
                  | nil => ret (r, InternalCacheError reqId pac)
                  | ans :: ans' =>
                    (* Arbitrarily choose the first answer, put it in a packet, and return it *)
                    (* TODO: could also re-hierarchize all the answer/authority/additional into pac *)
                    (* should anything go in authority and additional? *)
                    let pac' := add_answer (buildempty pac) (toPacket_ans ans) in
                    ret (r, ClientAnswer reqId pac')
                  end
                | Ref referralRows =>
                  (* Add pending request *)
                  (* TODO thread rep properly through AddRequest and UpdateCacheReferralsAndSLIST
                     (and in Nope) *)
                  res <- Insert (Build_RequestState pac reqId None) into r!sREQUESTS;
                  (* Initialize the SLIST with best referrals, then send a question w/ the first *)
                  UpdateCacheReferralsAndSLISTSpec r reqId timeArrived pac referralRows
                (* No we haven't seen it *)
                | Nope =>
                  (* Add pending request *)
                  res <- Insert (Build_RequestState pac reqId None) into r!sREQUESTS;
                  (* Initialize the SLIST with SBELT, pick one and send a question w/ the first *)
                  UpdateCacheReferralsAndSLISTSpec r reqId timeArrived pac SBELT

              end }%methDefParsing.

(* All the old internal methods. *)

      (* Uses the pre-generated id *)
      (*Def Method2 AddRequest (r : rep)
          (pac : packet)
          (freshAscendingId : id) : rep * bool :=
          Insert (Build_RequestState pac freshAscendingId None) into r!sREQUESTS,

      (* Stage is explained in the schema file *)
        Def Method1 GetRequestStage
            (r : rep)
            (reqId : id)
        : rep * option Stage :=
          stages <- For (req in r!sREQUESTS)
                    Where (reqId = req!sID)
                    Return (req!sSTAGE);
        ret (r, hd_error stages),
        (* there are 0 or 1 requests matching a specific id (since unique) *)

        Def Method2 UpdateRequestStage (r : rep)
            (reqID : id)  (reqStage : Stage) : rep * bool :=
          q <- Update c from r!sREQUESTS as c'
            making c'!sSTAGE = reqStage
            where (c!sID = reqID);
        ret (fst q, nonempty (snd q)),

        (* ----- CACHE *)

        (* Given a time and either an answer or a failure, convert that to the correct row type
           and insert the rows in the correct cache table.
        Assumes that someone has already checked that the domain is not in any of the caches. *)
        Def Method2 InsertResultForDomain (r : rep)
            (timeArrived : time)
            (toStore : ToStore) : rep * bool :=
          q <- UpdateTTLs_stub r timeArrived;
          let (r, _) := q in

          match toStore with
          | Answer reqName pac =>
            r1 <- Insert <sDOMAIN :: reqName, sCACHETABLE :: CAnswers >%Tuple into r!sCACHE_POINTERS;
          r2 <- InsertAll (fst r1) ``sCACHE_ANSWERS
             (fun ans =>
                ret (< sDOMAIN :: reqName,
                sPACKET_SECTION :: PAnswer,
                sTIME_LAST_CALCULATED :: timeArrived> ++ ans))
             (pac!"answers");
          r3 <- InsertAll (fst r2) ``sCACHE_ANSWERS
             (fun ans =>
                ret (< sDOMAIN :: reqName,
                     sPACKET_SECTION :: PAuthority,
                     sTIME_LAST_CALCULATED :: timeArrived> ++ ans))
             (pac!"authority");
          InsertAll (fst r3) ``sCACHE_ANSWERS
                    (fun ans =>
                       ret (< sDOMAIN :: reqName,
                            sPACKET_SECTION :: PAdditional,
                            sTIME_LAST_CALCULATED :: timeArrived> ++ ans))
                    (pac!"additional")

          | Failure reqName pac soa =>
            r1 <- Insert <sDOMAIN :: reqName, sCACHETABLE :: CFailures > into r!sCACHE_POINTERS;
            Insert (<sDOMAIN :: reqName, sTIME_LAST_CALCULATED :: timeArrived>
                                         ++ soa) into (fst r1)!sCACHE_FAILURES

          end,

(* Delete a pending request's entry in the request's table, its SLIST order, and its SLIST *)
          Def Method1 DeletePendingRequestInfo (r : rep) (reqId : id) : rep * bool :=
           r1 <- Delete row from r!sREQUESTS where row!sID = reqId;
           r2 <- Delete row from (fst r1)!sSLIST_ORDERS where row!sREQID = reqId;
           r3 <- Delete row from (fst r2)!sSLIST where row!sREQID = reqId;
           ret (fst r3, nonempty (snd r1) || nonempty (snd r2) || nonempty (snd r3)),

           (* Delete a cached name's entry in the cache pointer table, as well as all relevant
              cached answers or failures (note, does not delete things from referrals or SLIST). *)
          Def Method1 DeleteCachedNameResult (r : rep) (domain : name) : rep * CacheResult :=
             results <- For (pointer in r!sCACHE_POINTERS)
                     Where (pointer!sDOMAIN = domain)
                     Return (pointer!sCACHETABLE);
        match results with
        (* domain to be deleted is not actually in cache *)
        | [ ] => ret (r, Nope)
        | tbl :: _ =>
          r1 <- Delete row from r!sCACHE_POINTERS where row!sDOMAIN = domain;
          match tbl with
          | CAnswers =>
            answer_res <- Delete row from (fst r1)!sCACHE_ANSWERS where row!sDOMAIN = domain;
            ret (fst answer_res, Ans (snd answer_res))
          | CFailures =>
              failure_res <- Delete row from (fst r1)!sCACHE_FAILURES where row!sDOMAIN = domain;
            ret (fst failure_res, Fail (listToOption (snd failure_res)))
          end
        end,

        (* For a given name, look in the cache and return the rows that match the longest suffix of the name. Subcase: if there already is a concrete answer/failure/referral for the name, return that. *)
        Def Method2 GetServerForLongestSuffix (r : rep)
            (currTime : time) (reqName : name) : rep * CacheResult :=
          (* Update the TTLs *)
          r' <- UpdateTTLs_stub r currTime;
        (* Check if we have cached results for reqName *)
          results <- For (pointer in (fst r')!sCACHE_POINTERS)
                     Where (pointer!sDOMAIN = reqName)
                     Return (pointer!sCACHETABLE);
        (* TODO: filter by packetsection = answer? are authority/additional useful? *)
          suffixes <- For (ans in (fst r')!sCACHE_REFERRALS)
                   Where (IsPrefix ans!sREFERRALDOMAIN reqName)
                   Return ans;
          let domainLength (tup : ReferralRow) := List.length tup!sREFERRALDOMAIN in
          longestSuffixes <- [[suffix in suffixes | upperbound domainLength suffixes suffix]];
            match results with
            | CAnswers :: _ =>
              (* There may be multiple rows in Answers, containing various answer/authority/addl *)
              (* This returns all of them and leaves it to Process to hierarchize/query them *)
              (* (they should all be for the same domain though; the longest suffix is unique *)
              nameRes <- For (f in (fst r')!sCACHE_ANSWERS)
                         Where (f!sDOMAIN = reqName)
                         Return f;
                (* TTL* *)
                ret (fst r', Ans nameRes)

            | CFailures :: _ =>
              (* This domain [s.g.com] failed. If we have any results for the longest prefix, *)
              (* return them and label them as referrals. (e.g. an answer for [g.com])  *)
              (* Otherwise, return failure. *)
              If (is_empty longestSuffixes) Then
                 nameRes <- For (f in (fst r')!sCACHE_FAILURES)
                            Where (f!sDOMAIN = reqName)
                            Return f;
                (* TTL* *)
                ret (fst r', Fail (listToOption nameRes))
              Else
              ret (fst r', Ref longestSuffixes)

            | [ ] =>
              (* name has nothing cached for it, but we might have referrals for subdomains *)
              If (is_empty longestSuffixes) Then
                 ret (fst r', Nope) (* this name has nothing cached for it *)
              Else
                 ret (fst r', Ref longestSuffixes)
            end,

            (* -------- REFERRAL/SLIST FUNCTIONS *)

            (* Filters referrals for the valid ones (not already in list + type, class), *)
            (* puts referrals in SLIST table with unique id (per request), and *)
            (* adds everything to the SLIST order and re-sorts that by match count *)
            Def Method3 ReferralRowsToSLIST (r : rep) (reqId : id)
                (questionName : name) (referrals : list ReferralRow) : rep * bool :=

              (* TODO: filter by type, class *)
              validReferrals <- [[ ref in referrals |
                                   ~ exists slist_ref,
                                       IndexedEnsemble_In slist_ref (r!sSLIST)
                                       /\ (ref!sREFERRALDOMAIN = slist_ref!sREFERRALDOMAIN)]];
              InsertAll r ``sSLIST
                        (fun curRef : ReferralRow =>
                           (* Augment a referral row with the additional fields in the SLIST *)
                           (* referral row (ids, counts) *)
                           (* Calculate match count of referral domain to question domain *)
                           (* e.g. ref domain = g.com, question domain = s.g.com -> count = 2 *)
                           longestSharedSuffix <- { name' : name |
                                                    IsPrefix name' curRef!sREFERRALDOMAIN
                                                    /\ IsPrefix name' questionName
                                                    /\ forall name'' : name,
                                                        IsPrefix name'' curRef!sREFERRALDOMAIN
                                                        -> IsPrefix name'' questionName
                                                        -> List.length name' >= List.length name'' };
                         (* Generate unique ids that are all greater than the existing ids *)
                         newID <- { id : nat | forall ref,
                                      IndexedEnsemble_In ref (r!sSLIST)%QuerySpec
                                      -> ref!sREQID = reqId
                                      -> id > ref!sREFERRALID };
                         ret (<sREQID :: reqId, sREFERRALID :: newID,
                              sMATCHCOUNT :: (List.length longestSharedSuffix),
                              sQUERYCOUNT :: 0 (* New Row / hasn't been queried before*) >
                              ++ curRef))
                        referrals,

              (* Get the "best" referral (the one with the highest matchCount), *)
              (* add 1 to its query count, update the request's match count, and re-sort *)
              (* SLIST according to this. Then returns that "best" referral *)
              Def Method2 GetFirstReferralAndUpdateSLIST
                  (r : rep) (curTime : time) (reqId : id)
              : rep * (option SLIST_ReferralRow) :=
                r' <- UpdateTTLs_stub r curTime;
                r'' <- Update slist_ref from (fst r')!sSLIST as slist_ref'
                       making slist_ref'!sQUERYCOUNT = slist_ref!sQUERYCOUNT + 1
                       where (slist_ref!sREQID = reqId /\
                              forall slist_ref'',
                                IndexedEnsemble_In slist_ref'' (r!sSLIST)
                                -> slist_ref''!sMATCHCOUNT <= slist_ref!sMATCHCOUNT);
                match r'' with
                | (r''', bestRef :: _) =>
                   res <- Update req from r'''!sREQUESTS as req'
                            making req'!sSTAGE = Some bestRef!sMATCHCOUNT
                            where (req!sID = reqId);
                   ret (fst res, Some (bestRef))
                | (r''', _) => ret (r''', None)
                end,

          (* Given a list of *new* referralrows (i.e. came from a packet, or is SBELT),
             put them in the request's SLIST, and return the current best referral. Calls many
             helper functions. *)
        Def Method4 UpdateCacheReferralsAndSLIST (r : rep)
            (currTime : time) (reqId : id) (pac : packet) (referrals : list ReferralRow)
                : rep * ToOutside :=
                  r' <- UpdateTTLs_stub r currTime;
             (* Insert referrals into cache *)
             r'' <- InsertAll (fst r') ``sCACHE_REFERRALS (fun x => ret x) referrals;
             (* Get name of the original question *)
             req <- For (req in (fst r'')!sREQUESTS)
                         Where (req!sID = reqId)
                         Return req!sQNAME;
             match req with
             | [ questionDomain ] =>
               (* TODO: filter by type, class *)
               (* Put the referrals into the request's sLIST *)
               validReferrals <- [[ ref in referrals |
                                    ~ exists slist_ref,
                                        IndexedEnsemble_In slist_ref ((fst r'')!sSLIST)
                                        /\ (ref!sREFERRALDOMAIN = slist_ref!sREFERRALDOMAIN)]];
               r''' <- InsertAll (fst r'') ``sSLIST
                        (fun curRef : ReferralRow =>
                           (* Augment a referral row with the additional fields in the SLIST *)
                           (* referral row (ids, counts) *)
                           (* Calculate match count of referral domain to question domain *)
                           (* e.g. ref domain = g.com, question domain = s.g.com -> count = 2 *)
                           longestSharedSuffix <- { name' : name |
                                                    IsPrefix name' curRef!sREFERRALDOMAIN
                                                    /\ IsPrefix name' [""]
                                                    /\ forall name'' : name,
                                                        IsPrefix name'' curRef!sREFERRALDOMAIN
                                                        -> IsPrefix name'' [""]
                                                        -> List.length name' >= List.length name'' };
                         (* Generate unique ids that are all greater than the existing ids *)
                         newID <- { id : nat | forall ref,
                                      IndexedEnsemble_In ref (r!sSLIST)
                                      -> ref!sREQID = reqId
                                      -> id > ref!sREFERRALID };
                         ret (<sREQID :: reqId, sREFERRALID :: newID,
                              sMATCHCOUNT :: (List.length longestSharedSuffix),
                              sQUERYCOUNT :: 0 (* New Row / hasn't been queried before*) >
                              ++ curRef))
                        referrals;
               (* Get the "best" referral (the one with the lowest position in SLIST), *)
               (* add 1 to its query count, update the request's match count, and  *)
               (* then return that "best" referral *)
               r4 <- Update slist_ref from (fst r''')!sSLIST as slist_ref'
                       making slist_ref'!sQUERYCOUNT = slist_ref!sQUERYCOUNT + 1
                       where (slist_ref!sREQID = reqId /\
                              forall slist_ref'',
                                IndexedEnsemble_In slist_ref'' (r!sSLIST)
                                -> slist_ref''!sMATCHCOUNT <= slist_ref!sMATCHCOUNT);
                match r4 with
                | (r5, bestRef :: _) =>
                   r6 <- Update req from r5!sREQUESTS as req'
                            making req'!sSTAGE = Some bestRef!sMATCHCOUNT
                            where (req!sID = reqId);
                (* Send the same question to the server with the IP given in the referral *)
                   ret (fst r6, ServerQuestion reqId bestRef!sSIP pac)
                | (r5, _) => ret (r5, NoReferralsLeft reqId pac)
                end
               | _ => ret (fst r'', NoReferralsLeft reqId pac)
             end, *)


(* Set Printing All. *)
Print DnsSpec_Recursive.
