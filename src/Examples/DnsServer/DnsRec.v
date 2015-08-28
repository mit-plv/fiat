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
        Fiat.Examples.DnsServer.packet_new
        Fiat.Examples.DnsServer.DnsLemmas.

Require Import Fiat.Examples.DnsServer.DnsSchema_new.

(* Only Init, MakeId, and Process should be public methods. The rest are private, for internal use. *)
Definition DnsRecSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,

      (* request state methods *)
      Method "MakeId" : rep x name -> rep x id,
      Method "AddRequest" : rep x (packet * id) -> rep x bool,
      Method "GetRequestStage" : rep x id -> rep x option Stage,
      Method "UpdateRequestStage" : rep x (id * Stage) -> rep x bool,

      (* cache methods *)
      Method "InsertResultForDomain" : rep x (time * ToStore) -> rep x bool,
      Method "DeletePendingRequestInfo" : rep x id -> rep x bool,
      Method "DeleteCachedNameResult" : rep x name -> rep x CacheResult,
      Method "GetServerForLongestSuffix" : rep x (time * name) -> rep x CacheResult,

      (* methods related to referrals and SLIST manipulation *)
      Method "PacketToReferralRows" : rep x (time * packet) -> rep x list ReferralRow,
      Method "InsertReferralRowsIntoCache" : rep x list ReferralRow -> rep x bool,
      Method "SortSLIST" : rep x id -> rep x bool,
      Method "ReferralRowsToSLIST" : rep x (id * name * list ReferralRow) -> rep x bool,
      Method "GetFirstReferralAndUpdateSLIST" : rep x (time * id) -> rep x option SLIST_ReferralRow,
      Method "UpdateCacheReferralsAndSLIST" : rep x (time * id * packet * list ReferralRow) -> rep x ToOutside,

     (* TTL *)
      Method "UpdateTTLs" : rep x time -> rep x bool,
                                           
      (* Main method. Talks to an outside "wrapper" in continuation-passing style. Given the time and something from the wrapper, figures out what to do with it and returns a response that may be an error, answer, or request for the wrapper to send a question to another server. *)
      Method "Process" : rep x (time * FromOutside) -> rep x ToOutside
    }.

Variable s : list nat.
Check [[x in s | True]].        (* Comp (list nat) -- multiple choice, over existing var s *)
Check { x : nat | True }.   (* Comp nat -- single choice, over type nat *)
Check { b : bool | decides b True }. (* Comp bool -- check *)

(* Boilerplate to take various fields/attributes and produce a tuple.
Should be auto-generated in newer versions of Fiat*)
Definition Build_RequestState pac id stage :=
  let q := questions pac in
  < Build_Component (Build_Attribute sID nat) id,
  Build_Component (Build_Attribute sQNAME name) (qname q),
  Build_Component (Build_Attribute sSTAGE Stage) stage,
  Build_Component (Build_Attribute sQTYPE RRecordType) (qtype q),
  Build_Component (Build_Attribute sQCLASS RRecordClass) (qclass q),
  Build_Component (Build_Attribute sPID (Bvector 16)) (id' pac),
  Build_Component (Build_Attribute sFLAGS (Bvector 16)) (flags pac)
  >.

Definition Build_CachePointerRow reqName table :=
  < Build_Component (Build_Attribute sDOMAIN name) reqName,
    Build_Component (Build_Attribute sCACHETABLE CacheTable) table >.

Definition Build_CacheReferralsRow tup :=
  let '(referralDomain, rType, rClass, rTTL, serverDomain, sType, sClass, sTTL, sIP, timeLastCalculated) := tup in
  < Build_Component (Build_Attribute sREFERRALDOMAIN name) referralDomain,
  Build_Component (Build_Attribute sRTYPE RRecordType) rType,
  Build_Component (Build_Attribute sRCLASS RRecordClass) rClass,
  Build_Component (Build_Attribute sRTTL nat) rTTL,

  Build_Component (Build_Attribute sSERVERDOMAIN name) serverDomain,
  Build_Component (Build_Attribute sSTYPE RRecordType) sType,
  Build_Component (Build_Attribute sSCLASS RRecordClass) sClass,  
  Build_Component (Build_Attribute sSTTL nat) sTTL,
  Build_Component (Build_Attribute sSIP name) sIP,
  Build_Component (Build_Attribute sTIME_LAST_CALCULATED nat) timeLastCalculated >.

Definition Build_CacheAnswersRow tup :=
  let '(rDomain, rSection, rName, rType, rClass, rTTL, rRdata, timeLastCalculated) := tup in
  < Build_Component (Build_Attribute sDOMAIN name) rDomain,
  Build_Component (Build_Attribute sPACKET_SECTION PacketSection) rSection,
  Build_Component (Build_Attribute sNAME name) rName,
  Build_Component (Build_Attribute sTYPE RRecordType) rType,
  Build_Component (Build_Attribute sCLASS RRecordClass) rClass,
  Build_Component (Build_Attribute sTTL nat) rTTL,
  Build_Component (Build_Attribute sRDATA name) rRdata,
  Build_Component (Build_Attribute sTIME_LAST_CALCULATED nat) timeLastCalculated >.

Definition Build_CacheFailuresRow tup :=
  let '(rDomain, rHost, rEmail, rSerial, rRefresh, rRetry, rExpire, rMinTTL, timeLastCalculated) := tup in
  < Build_Component (Build_Attribute sDOMAIN name) rDomain,
  Build_Component (Build_Attribute sHOST name) rHost,
  Build_Component (Build_Attribute sEMAIL name) rEmail,
  Build_Component (Build_Attribute sSERIAL nat) rSerial,
  Build_Component (Build_Attribute sREFRESH nat) rRefresh,
  Build_Component (Build_Attribute sRETRY nat) rRetry,
  Build_Component (Build_Attribute sEXPIRE nat) rExpire,    
  Build_Component (Build_Attribute sMinTTL nat) rMinTTL,
  Build_Component (Build_Attribute sTIME_LAST_CALCULATED nat) timeLastCalculated >.

Definition ToSLISTRow (refRow : ReferralRow) reqId refId matchCount queryCount :=
  < Build_Component (Build_Attribute sREQID nat) reqId,
  Build_Component (Build_Attribute sREFERRALID nat) refId,
  Build_Component (Build_Attribute sREFERRALDOMAIN name) refRow!sREFERRALDOMAIN,
  Build_Component (Build_Attribute sRTYPE RRecordType) refRow!sRTYPE,
  Build_Component (Build_Attribute sRCLASS RRecordClass) refRow!sRCLASS,
  Build_Component (Build_Attribute sRTTL nat) refRow!sRTTL,

  Build_Component (Build_Attribute sSERVERDOMAIN name) refRow!sSERVERDOMAIN,
  Build_Component (Build_Attribute sSTYPE RRecordType) refRow!sSTYPE,
  Build_Component (Build_Attribute sSCLASS RRecordClass) refRow!sSCLASS,  
  Build_Component (Build_Attribute sSTTL nat) refRow!sSTTL,
  Build_Component (Build_Attribute sSIP name) refRow!sSIP,
  Build_Component (Build_Attribute sTIME_LAST_CALCULATED nat) refRow!sTIME_LAST_CALCULATED,

  Build_Component (Build_Attribute sMATCHCOUNT nat) matchCount,
  Build_Component (Build_Attribute sQUERYCOUNT nat) queryCount >.

Definition ToSLISTOrder reqId order :=
  < Build_Component (Build_Attribute sREQID nat) reqId,
  Build_Component (Build_Attribute sORDER (list refPosition)) order >.

Definition toPacket_soa (soa : FailureRow) : SOA :=
  {| sourcehost := soa!sHOST;
    contact_email := soa!sEMAIL;
    serial := soa!sSERIAL;
    refresh := soa!sREFRESH;
    retry := soa!sRETRY;
    expire := soa!sEXPIRE;
    minTTL := soa!sMinTTL |}.

Definition toPacket_ans (ans : AnswerRow) : answer :=
  {| aname := ans!sNAME;
    atype := ans!sTYPE;
    aclass := ans!sCLASS;
    ttl := ans!sTTL;
    rdata := ans!sRDATA |}.

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

(* Helper functions *)

Definition upperbound' := upperbound (fun x => x).

Definition nonempty {A : Type} (l : list A) := negb (beq_nat (List.length l) 0).

(* Double the monad, double the fun! *)
Fixpoint iterate {A B : Type} {R : RepHint} (r : repHint) (f : repHint -> A -> (Comp (repHint * B)))
        (l : list A) : Comp (repHint * list B) :=
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

Definition DnsSpec_Recursive : ADT DnsRecSig :=
  QueryADTRep DnsRecSchema {
    Def Constructor Init (_ : unit) : rep := empty,

      (* ----- REQUESTS *)

      (* Generate a unique id for a request. Wrapper's responsibility to use this id for everything concerning this request and pass the correct id into functions. Requests can have (different id, same name) but not (same id, different name) since a packet can only contain one question *)
      query MakeId (r : rep, n : name) : id :=
        ids <- For (req in r!sREQUESTS)
            Return (req!sID);
        freshAscendingId <- {idx : nat | upperbound' ids idx };
        ret freshAscendingId,

        (* Uses the pre-generated id *)
      update AddRequest (r : rep, tup : packet * id) : bool := 
        let (pac, freshAscendingId) := tup in
        Insert (Build_RequestState pac freshAscendingId None) into r!sREQUESTS,

        (* Stage is explained in the schema file *)
      query GetRequestStage (r : rep, reqId : id) : option Stage :=
        stages <- For (req in r!sREQUESTS)
            Where (reqId = req!sID)
            Return (req!sSTAGE);
        (* there are 0 or 1 requests matching a specific id (since unique) *)
        ret (hd_error stages),

        update UpdateRequestStage (r : rep, tup : id * Stage) : bool :=
          let (reqId, reqStage) := tup in
          q <- Update c from r!sREQUESTS as c'
            making c'!sSTAGE = reqStage
            where (c!sID = reqId);
        let (updated, affected) := q in
        ret (updated, nonempty affected),

        (* ----- CACHE *)

        (* Given a time and either an answer or a failure, convert that to the correct row type
           and insert the rows in the correct cache table.
        Assumes that someone has already checked that the domain is not in any of the caches. *)
       update InsertResultForDomain (r : rep, tup : time * ToStore) : bool :=
          let (timeArrived, toStore) := tup in

          let UpdateTTLs (r : repHint) (t : time) := ret (r, false) in
          q <- UpdateTTLs r timeArrived;
          let (r, _) := q in

          match toStore with
          | Answer reqName pac => 

            (* monad iteration instead. TODO param over table *)
            let fix InsertAll (r' : repHint) rowFunc tups :=
                match tups with
                (* this shouldn't happen since an answer must have at >= 1 answer record *)
                | nil => ret (r', false)
                | ptup :: ptups =>
                  res <- Insert (rowFunc ptup) into r'!sCACHE_ANSWERS;
                  let (r'', _) := res in
                  InsertAll r'' rowFunc ptups
                end in

            let flattenWithRec p type rec :=
                let q := questions p in
                (reqName, type, aname rec, atype rec, aclass rec, ttl rec, rdata rec, timeArrived) in
            let flattenPacket p type recs := List.map (fun rec => flattenWithRec p type rec) recs in
            let tups p := flattenPacket p PAnswer (answers p)
                                        ++ flattenPacket p PAuthority (authority p)
                                        ++ flattenPacket p PAdditional (additional p) in
            res1 <- Insert (Build_CachePointerRow reqName CAnswers) into r!sCACHE_POINTERS;
          let (r1, _) := res1 in
          InsertAll r Build_CacheAnswersRow (tups pac)

          | Failure reqName pac soa =>
            (* ignoring authority/answer/additional fields; using only the one SOA *)
            let mkFailTup p soa := 
                (reqName, sourcehost soa, contact_email soa, 
                 serial soa, refresh soa, retry soa, expire soa, minTTL soa, timeArrived) in
            res1 <- Insert (Build_CachePointerRow reqName CFailures) into r!sCACHE_POINTERS;
          let (r1, _) := res1 in
          Insert (Build_CacheFailuresRow (mkFailTup pac soa)) into r1!sCACHE_FAILURES

          end,

          (* Delete a pending request's entry in the request's table, its SLIST order, and its SLIST *)
          update DeletePendingRequestInfo (r : rep, reqId : id) : bool :=
           res1 <- Delete row from r!sREQUESTS where row!sID = reqId;
           let (r1, rows1) := res1 in
           res2 <- Delete row from r1!sSLIST_ORDERS where row!sREQID = reqId;
           let (r2, rows2) := res2 in
           res3 <- Delete row from r2!sSLIST where row!sREQID = reqId;
           let (r3, rows3) := res3 in
           ret (r3, nonempty rows1 || nonempty rows2 || nonempty rows3),
          
           (* Delete a cached name's entry in the cache pointer table, as well as all relevant
              cached answers or failures (note, does not delete things from referrals or SLIST). *)
            update DeleteCachedNameResult (r : rep, domain : name) : CacheResult :=
          results <- For (pointer in r!sCACHE_POINTERS)
                   Where (pointer!sDOMAIN = domain)
                   Return (pointer!sCACHETABLE);
        match results with
        (* domain to be deleted is not actually in cache *)
        | nil => ret (r, Nope)
        | tbl :: _ =>
          res <- Delete row from r!sCACHE_POINTERS where row!sDOMAIN = domain;
          let (r1, _) := res in
          match tbl with
          | CAnswers =>
            answer_res <- Delete row from r1!sCACHE_ANSWERS where row!sDOMAIN = domain;
            let (r2, ans_deleted) := answer_res in
            ret (r2, Ans ans_deleted)
          | CFailures =>
              failure_res <- Delete row from r1!sCACHE_FAILURES where row!sDOMAIN = domain;
            let (r2, fail_deleted) := failure_res in
            ret (r2, Fail (listToOption fail_deleted))                
          end
        end,

        (* For a given name, look in the cache and return the rows that match the longest suffix of the name. Subcase: if there already is a concrete answer/failure/referral for the name, return that. *)
        query GetServerForLongestSuffix (r : rep, tup : time * name) : CacheResult :=
          let (currTime, reqName) := tup in

          let UpdateTTLs (r : repHint) (t : time) := ret (r, false) in
          q <- UpdateTTLs r currTime;
          let (r, _) := q in

          let getLongestSuffixes name :=
              (* TODO: filter by packetsection = answer? are authority/additional useful? *)
            suffixes <- For (ans in r!sCACHE_REFERRALS)
                Where (IsPrefix ans!sREFERRALDOMAIN name) 
                Return ans;
            let domainLength (tup : ReferralRow) := List.length tup!sREFERRALDOMAIN in
            [[suffix in suffixes | upperbound domainLength suffixes suffix]] in

          (* Check if we have cached results for reqName *)
          results <- For (pointer in r!sCACHE_POINTERS)
                   Where (pointer!sDOMAIN = reqName)
                   Return (pointer!sCACHETABLE);
        match results with
        | nil =>
          (* name has nothing cached for it, but we might have referrals for subdomains *)
          longestSuffixes <- getLongestSuffixes reqName;
          match longestSuffixes with
          | _ :: _ =>
            (* TTL* *)
            ret (Ref longestSuffixes)
          | nil => 
          (* assuming prefix/subdomain failure does not imply domain failure.
             e.g. s.com fails -/-> c.s.com fails *)
            ret Nope (* this name has nothing cached for it *)
          end
          
        | table :: _ => 
          match table with
                              
          | CFailures => 
            (* This domain [s.g.com] failed. If we have any results for the longest prefix, return them
               and label them as referrals.
               (e.g. an answer for [g.com]) Otherwise, return failure. *)
            longestSuffixes <- getLongestSuffixes reqName;
            match longestSuffixes with
            | _ :: _ => ret (Ref longestSuffixes)
            | nil =>
              (* There should be only one row in Failures, containing the SOA record *)
              nameRes <- For (f in r!sCACHE_FAILURES)
                      Where (f!sDOMAIN = reqName)
                      Return f;
              (* TTL* *)
              ret (Fail (listToOption nameRes))
          
            (* There may be multiple rows in Answers, containing various answer/authority/addl *)
            (* This returns all of them and leaves it to Process to hierarchize/query them *)
            (* (they should all be for the same domain though; the longest suffix is unique *)
            end

          | CAnswers => 
            (* There may be multiple rows in Answers, containing various answer/authority/addl *)
            (* This returns all of them and leaves it to Process to hierarchize/query them *)
            nameRes <- For (f in r!sCACHE_ANSWERS)
                    Where (f!sDOMAIN = reqName)
                    Return f;
            (* TTL* *)
            ret (Ans nameRes)
          end
        end,
          
        (* -------- REFERRAL/SLIST FUNCTIONS *)

        (* Does a join on the authority and additional fields of a referral-containing packet to de-hierarchize it into rows. For an example, see RFC 1034, page 47. *)
     query PacketToReferralRows (r : rep, tup : time * packet) : list ReferralRow :=
          let (timeArrived, pac) := tup in

          let UpdateTTLs (r : repHint) (t : time) := ret (r, false) in
          q <- UpdateTTLs r timeArrived;
          let (r, _) := q in

          (* link authority and additional fields *)
          (* for each auth in authority, for each addl in additional, *)
          (*  if auth's rdata = addl's name, flatten the whole thing into a row and add it *)
          let authRdataMatchesAddlName (tup2 : answer * answer) :=
              let (auth, addl) := tup2 in
              beq_name (rdata auth) (aname addl) in
          let auth_addl_join := list_join authRdataMatchesAddlName
                                          (authority pac) (additional pac) in
          
          let pairToPacketTup (tup2 : answer * answer) :=
              let q := questions pac in
              let (auth, addl) := tup2 in
              (aname auth, atype auth, aclass auth, ttl auth,
               aname addl, atype addl, aclass addl, ttl addl,
               rdata addl, timeArrived) in
          ret (map (fun tup2 => Build_CacheReferralsRow (pairToPacketTup tup2)) auth_addl_join),

          (* Unfortunately, can't parametrize iterate by the table, so here's a specific function *)
     update InsertReferralRowsIntoCache (r : rep, referrals : list ReferralRow) : bool :=
            let fix InsertAll (r' : repHint) rows :=
                match rows with
                | nil => ret (r, false)
                | row :: rows' =>
                  res <- Insert row into r'!sCACHE_REFERRALS;
                let (r'', _) := res in
                InsertAll r'' rows'
                end in
            InsertAll r referrals,

          (* Re-sort a particular request's SLIST by descending match count.
             Smaller position = higher match count.
             TODO more sophisticated sorting algorithm. right now it ignores the query count *)
     update SortSLIST (r : rep, reqId : id) : bool :=
              (* Get the SLIST rows first so we can have predicates on them w/o being stuck in the Comp monad *)
          allSLISTrows <- For (ref in r!sSLIST)
                       Where (ref!sREQID = reqId)
                       Return ref;
          let refIds := map (fun ref => ref!sREFERRALID) allSLISTrows in

          (* Delete the order, generate the new sorted order, and insert that *)
          res1 <- Delete row from r!sSLIST_ORDERS where row!sREQID = reqId;
          let (r2, _) := res1 in
          let allUnique {A : Type} l := forall (x : A) (y : A), List.In x l /\ List.In y l -> x <> y in
          (* Get match count of each referral from SLIST and compare *)
          let matchCountGeq id1 id2 := 
              (* let find_row_with id := *)
              (*     find (fun (row : SLIST_ReferralRow) => beq_nat row!sREFERRALID id) allSLISTrows in *)
              (* let ref1row := find_row_with id1 in *)
              (* let ref2row := find_row_with id2 in *)
              (* match ref1row, ref2row with *)
              (* | Some ref1row', Some ref2row' => ref1row'!sMATCHCOUNT >= ref2row'!sMATCHCOUNT *)
              (* | _, _ => False *)
              exists ls, 

              (For (ref1 in r!sSLIST) (ref2 in r!sSLIST)
                    Where (ref1!sMATCHCOUNT >= ref2!sMATCHCOUNT)
                    Return (ref1!sREQID, ref2!sREQID)) ls /\ List.In (id1, id2) ls
              
               in
          (* Permutation of the old order, with unique positions, such that referrals with a greater match count have a smaller position. Positions might not be consecutive *)
          newOrder <- { order : list refPosition | 
                        let orderIds := map refId order in
                        let positions := map refPos order in
                        Permutation orderIds refIds /\ allUnique positions /\
                        (* TODO: factor out into pairwise predicate *)
                        (forall (ref1 ref2 : refPosition), List.In ref1 order /\ List.In ref2 order /\
                                          refPos ref2 > refPos ref1 ->
                                          matchCountGeq (refId ref1) (refId ref2)) };
          Insert (ToSLISTOrder reqId newOrder) into r2!sSLIST_ORDERS,

      (* Filters referrals for the valid ones (not already in list + type, class),
      puts referrals in SLIST table with unique id (per request), and
      adds everything to the SLIST order and re-sorts that by match count *)
     update ReferralRowsToSLIST (r : rep, tup : id * name * list ReferralRow) : bool :=
          let '(reqId, questionName, referrals) := tup in

          (* TODO this function occurs multiple times; parametrize over table / monad iter *)
          let fix InsertAll (r : repHint) (ids : list nat) (rows : list SLIST_ReferralRow) 
              : Comp (repHint * bool) :=
              match ids, rows with
              | nil, nil => ret (r, true)
              | refId :: ids', SLISTrow :: rows' =>
                res <- Insert SLISTrow into r!sSLIST;
                let (r', _) := res in 
                InsertAll r' ids' rows'
              | _, _ => ret (r, false) (* impossible, each row gets an id *)
              end in
          
          (* Calculate match count of referral domain to question domain *)
          (* e.g. ref domain = g.com, question domain = s.g.com -> count = 2 *)
          let matchCount refDomain questionName :=
              longestSharedSuffix <-
              { name' : name | IsPrefix name' refDomain /\ IsPrefix name' questionName /\
                               forall name'' : name, 
                               IsPrefix name'' refDomain /\ IsPrefix name'' questionName -> 
                               List.length name' >= List.length name'' };
              ret (List.length longestSharedSuffix) in

          (* Augment a referral row with the additional fields in the SLIST referral row (ids, counts) *)
          let ToSLISTrow' (r : repHint) (tup : id * ReferralRow) : Comp (repHint * SLIST_ReferralRow) :=
              let (refId, refRow) := tup in
              matchCount' <- matchCount refRow!sREFERRALDOMAIN questionName;
              let queryCount := 0 in (* New referral -- hasn't been queried before *)
              ret (r, ToSLISTRow refRow reqId refId matchCount' queryCount) in
          
          let SortSLIST (r : repHint) (reqId : id) : Comp (repHint * bool) :=
              ret (r, false) in (* TODO stub *)

          (* -------------------------------------- *)
          existingRefs <- For (ref in r!sSLIST)
                       Where True
                       Return ref;
        (* TODO: filter by type, class *)
          let notAlreadyInSLIST (ref : ReferralRow) := 
              ~ exists slist_ref, List.In slist_ref existingRefs
                                  /\ (ref!sREFERRALDOMAIN = slist_ref!sREFERRALDOMAIN) in
          validReferrals <- [[ ref in referrals | notAlreadyInSLIST ref ]];

          (* Get existing ids. could use SLIST ordering, but that's not much less work *)
          refIds <- For (ref in r!sSLIST)
                         Where (ref!sREQID = reqId)
                         Return ref!sREFERRALID;
          (* Generate unique ids that are all greater than the existing ids *)
          newIds <- { ids : list nat | forall (x y : nat), 
                     List.In x refIds /\ List.In y refIds -> 
                     x <> y /\ upperbound' refIds x /\ upperbound' refIds y 
                     /\ List.length ids = List.length referrals };

          (* Turn each referral row into an SLIST referral row, then insert all of them *)
          res0 <- iterate r ToSLISTrow' (List.combine newIds referrals);
          let (r0, SLISTrows) := res0 in
          res <- InsertAll r0 newIds SLISTrows;
          let (r1, _) := res in

          SortSLIST r1 reqId,
          

      (* Get the "best" referral (the one with the lowest position in SLIST),
      add 1 to its query count, update the request's match count, and re-sort SLIST according to this.
      Then returns that "best" referral *)
     update GetFirstReferralAndUpdateSLIST (r : rep, tup : time * id) : option SLIST_ReferralRow :=
      let (currTime, reqId) := tup in

      let UpdateTTLs (r : repHint) (t : time) := ret (r, false) in
      q <- UpdateTTLs r currTime;
      let (r, _) := q in

      let SortSLIST (r : repHint) (reqId : id) : Comp (repHint * bool) :=
          ret (r, false) in (* TODO stub *)

      row <- For (order in r!sSLIST_ORDERS)
              Where (order!sREQID = reqId)
              Return order!sORDER;
          match hd_error row with
          | None => ret (r, None)
          | Some order =>
            match order with
            | nil => ret (r, None)
            | _ :: _ =>
              (* Gets referral with highest match count (according to sorting of req's SLIST order) *)
              refWithLowestPosition <- [[ tup in order | forall tup',
                                            List.In tup' order -> refPos tup <= refPos tup' ]];
            (* Now that we have the ref id, get the row corresponding to that referral *)
              match refWithLowestPosition with
              | nil => ret (r, None) (* not possible *)
              | ref :: _ =>
                let bestRefId := refId ref in
                row <- For (ref in r!sSLIST)
                    Where (ref!sREQID = reqId /\ ref!sREFERRALID = bestRefId)
                    Return ref;
              match hd_error row with
              | None => ret (r, None)
              | Some bestRef =>
                (* Increment queryCount, update match count, and re-sort SLIST according to match ct*)
                (* For now, this won't change the SLIST order, but if the sorting algo starts to include queryCount, that will change the order *)
                res <- Update c from r!sSLIST as c'
                       making c'!sQUERYCOUNT = c!sQUERYCOUNT + 1
                       where (c!sREQID = reqId /\ c!sREFERRALID = bestRefId);
              let (r1, _) := res in
              res1 <- Update c from r1!sREQUESTS as c'
                      making c'!sSTAGE = Some bestRef!sMATCHCOUNT
                      where (c!sID = reqId);
              let (r2, _) := res1 in

              res2 <- SortSLIST r1 reqId;
              let (r3, _) := res2 in
              ret (r3, Some bestRef)
              end
              end
            end
          end,

          (* Given a list of *new* referralrows (i.e. came from a packet, or is SBELT),
             put them in the request's SLIST, and return the current best referral. Calls many
             helper functions. *)
     update UpdateCacheReferralsAndSLIST (r : rep, tup : time * id * packet * list ReferralRow) : ToOutside :=
        let '(currTime, reqId, pac, rows) := tup in

          let UpdateTTLs (r : repHint) (t : time) := ret (r, false) in
          q <- UpdateTTLs r currTime;
          let (r, _) := q in

        (* Stubs for above methods. *)
        let InsertReferralRowsIntoCache (r : repHint) (referrals : list ReferralRow) := ret (r, false) in
        let ReferralRowsToSLIST (r : repHint) reqId questionName (referrals : list ReferralRow) := ret (r, false) in
        let GetFirstReferralAndUpdateSLIST (r : repHint) (currTime : time) (reqId : id)
              : Comp (repHint * option SLIST_ReferralRow) := ret (r, None) in

        res <- InsertReferralRowsIntoCache r rows;
        let (r1, _) := res in
        (* Get name of the original question *)
        qs <- For (req in r!sREQUESTS)
           Where (req!sID = reqId)
           Return req!sQNAME;
        match hd_error qs with (* exactly one *)
        | None => ret (r, InternalCacheError reqId pac)
        | Some questionDomain =>
          res1 <- ReferralRowsToSLIST r1 reqId [""] rows;
        let (r2, _) := res1 in
        
        res3 <- GetFirstReferralAndUpdateSLIST r2 currTime reqId;
        let (r3, bestReferral) := res3 in
        match bestReferral with
        | None => ret (r3, NoReferralsLeft reqId pac)
        | Some bestRef => 
          (* Send the same question to the server with the IP given in the referral *)
          ret (r3, ServerQuestion reqId bestRef!sSIP pac)
        end
        end,

        (* ---------- TTL *)
     (* Decrement the TTLs of everything and store currTime in time_last_calculated,
        delete pointers to any SLIST referrals or cached rows soon to be deleted,
        and delete them (the ones with TTL 0)
       (TODO: code could be more efficient if we only updated those in a particular table,
        but then it would be longer)

     As a recurrence relation:
     TTL_(n+1) = TTL_n - (time_right_now - time_last_calculated) *)
        (* TODO: store the absolute time that the record should be deleted/ignored instead (when it's first added to a table), and calculate the updated TTL again when returning it *)
        update UpdateTTLs (r : rep, currTime : time) : bool :=
          (* Decrement all TTLs and set the time_last_calculated to now *)
          q <- Update c from r!sSLIST as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sSTTL = timeLeft c!sSTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          let (r, _) := q in

          q <- Update c from r!sCACHE_REFERRALS as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sSTTL = timeLeft c!sSTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          let (r, _) := q in

          q <- Update c from r!sCACHE_ANSWERS as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sTTL = timeLeft c!sTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          let (r, _) := q in

          q <- Update c from r!sCACHE_FAILURES as c'
            making (c'!sTIME_LAST_CALCULATED = currTime /\
                    c'!sMinTTL = timeLeft c!sMinTTL currTime c!sTIME_LAST_CALCULATED)
            where True;
          let (r, _) := q in

     (* For cache tables: get all to-be-deleted rows' names and delete those from cache pointers *)
          tbd_ref_names <- For (c in r!sCACHE_REFERRALS)
                        Where (c!sSTTL = 0)
                        Return (c!sREFERRALDOMAIN);
          tbd_ans_names <- For (c in r!sCACHE_ANSWERS)
                        Where (c!sTTL = 0)
                        Return (c!sDOMAIN);
          tbd_fail_names <- For (c in r!sCACHE_FAILURES)
                        Where (c!sMinTTL = 0)
                        Return (c!sDOMAIN);
          let toBeDeleted := tbd_ref_names ++ tbd_ans_names ++ tbd_fail_names in

          let deleteCachePointer (r : repHint) name :=
              q <- Delete row from r!sCACHE_POINTERS where row!sDOMAIN = name;
              let (r, affected) := q in
              ret (r, nonempty affected) in
          q <- iterate r deleteCachePointer toBeDeleted;
          let (r, _) := q in
          
     (* For SLIST referrals: get all to-be-deleted rows' req+ref ids and delete those from SLIST order *)
          tbd_reqId_and_refId <- For (c in r!sSLIST)
                        Where (c!sSTTL = 0)
                        Return (c!sREQID, c!sREFERRALID);

          let deleteReqSLISTentry (r : repHint) (tup : id * id) :=
              let (reqId, refId') := tup in
              q <- For (c in r!sSLIST_ORDERS)
                Where (c!sREQID = reqId)
                Return (c!sORDER);
              match hd_error q with
              | None => ret (r, false)
              | Some order =>
                (* Delete referral with id refId from the request's SLIST *)
                let order_ref_deleted := filter (fun tup => negb (beq_nat (refId tup) refId')) order in
                q <- Update c from r!sSLIST_ORDERS as c'
                     making (c'!sORDER = order_ref_deleted)
                     where (c!sREQID = reqId);
                let (r, affected) := q in
                ret (r, nonempty affected)
              end in
          q <- iterate r deleteReqSLISTentry tbd_reqId_and_refId;
          let (r, _) := q in

          (* Delete all rows from SLIST or cache with no time left to live *)
          q <- Delete row from r!sSLIST where row!sSTTL = 0;
          let (r, _) := q in
          q <- Delete row from r!sCACHE_REFERRALS where row!sSTTL = 0;
          let (r, _) := q in
          q <- Delete row from r!sCACHE_ANSWERS where row!sTTL = 0;
          let (r, _) := q in
          q <- Delete row from r!sCACHE_FAILURES where row!sMinTTL = 0;
          let (r, _) := q in

          ret (r, true),

          (* ----- MAIN METHOD *)

      (* Main method. Talks to an outside "wrapper" in continuation-passing style. Given the time and something from the wrapper, figures out what to do with it and returns a response that may be an error, answer, or request for the wrapper to send a question to another server. *)
          (* TODO need to inline other functions; stubs for now *)
          (* TODO rep is not threaded through in Process *)
        update Process (r : rep, tup : time * FromOutside) : ToOutside :=
          let SBELT := @nil ReferralRow in (* TODO add root ip *)
          (* let AddRequest (r : repHint) (tup : packet * id) := ret (r, false) in *)
          (* let InsertResultForDomain (r : repHint) (toStore : ToStore) := ret (r, false) in *)
          (* let GetServerForLongestSuffix (r : repHint) (reqName : name) := ret (r, Nope) in *)
          (* let DeleteCachedNameResult (r : repHint) (domain : name) := ret (r, Nope) in *)
          (* let DeletePendingRequestInfo (r : repHint) (reqId : id) := ret (r, false) in *)
          (* (* SLIST/referral stubs *) *)
          (* let PacketToReferralRows (r : repHint) (pac : packet) := ret (r, @nil ReferralRow) in *)
          (* let UpdateCacheReferralsAndSLIST reqId pac (r : repHint) (rows : list ReferralRow) := *)
          (*     ret (r, InvalidQuestion 0) in *)
          let AddRequest (tup : packet * id) := ret false in
          let InsertResultForDomain (timeArrived : time) (toStore : ToStore) := ret false in
          let GetServerForLongestSuffix (currTime : time) (reqName : name) := ret Nope in
          let DeleteCachedNameResult (domain : name) := ret Nope in
          let DeletePendingRequestInfo (reqId : id) := ret false in
          (* SLIST/referral stubs *)
          let PacketToReferralRows (timeArrived : time) (pac : packet) := ret (@nil ReferralRow) in
          let UpdateCacheReferralsAndSLIST (currTime : time) reqId pac (rows : list ReferralRow) := 
              ret (InvalidQuestion 0) in
          
          (* Utility functions *)
          let isQuestion p := 
              match answers p, authority p, additional p with
              | nil, nil, nil => true
              | _, _, _ => false
              end in
          let isAnswer p := 
              match answers p with
              | nil => false
              | _ :: _ => true
              end in
          let isReferral p :=
              match answers p, authority p, additional p with
              | nil, _ :: _, _ :: _ => true
              | _, _, _ => false
              end
          in
          let GetRequestName (reqId : id) : Comp (option name) :=
            names <- For (req in r!sREQUESTS)
                  Where (reqId = req!sID)
                  Return (req!sQNAME);
            ret (hd_error names) in

          let (timeArrived, fromOutside) := tup in
          let '(reqId, pac, failure) := fromOutside in
          let reqName := qname (questions pac) in

          let UpdateTTLs (r : repHint) (t : time) := ret (r, false) in
          q <- UpdateTTLs r timeArrived;
          let (r, _) := q in

          (* --- FUNCTION START --- *)
          (* Is the request pending? (Are we currently working on it?) *)
          pendingReq <- For (req in r!sREQUESTS)
                   Where (reqId = req!sID)
                   Return req;
          (* There should be either one or none *)
          match hd_error pendingReq with
          | None => 
            (* Not pending *)
            if negb (isQuestion pac) then (* is a referral, answer, or failure *)
              ret (r, InvalidResponse reqId)
            else
              (* But have we seen it before? *)
              suffixResults <- GetServerForLongestSuffix timeArrived reqName;
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
                    let pac' := add_ans (buildempty pac) (toPacket_ans ans) in
                    ret (r, ClientAnswer reqId pac')
                  end
                | Ref referralRows =>
                  (* Add pending request *)
                  (* TODO thread rep properly through AddRequest and UpdateCacheReferralsAndSLIST 
                     (and in Nope) *)
                  res <- AddRequest (pac, reqId);
                  (* Initialize the SLIST with best referrals, then send a question w/ the first *)
                  outsideResult <- UpdateCacheReferralsAndSLIST reqId timeArrived pac referralRows;
                  ret (r, outsideResult)
                (* No we haven't seen it *)
                | Nope => 
                  (* Add pending request *)
                  res <- AddRequest (pac, reqId);
                  (* Initialize the SLIST with SBELT, pick one and send a question w/ the first *)
                  outsideResult <- UpdateCacheReferralsAndSLIST reqId timeArrived pac SBELT;
                  ret (r, outsideResult)
              end                
          | Some pendingReq' => 
            (* Pending *)
            if isQuestion pac then
              ret (r, InvalidQuestion reqId)
            else
              (* Figure out if the packet is an answer, failure, or referral *)
              (* doesn't thoroughly check for malformed packets, e.g. contains answer and failure *)
              if isReferral pac then
                referralRows <- PacketToReferralRows timeArrived pac;
                outsideResult <- UpdateCacheReferralsAndSLIST timeArrived reqId pac referralRows;
                ret (r, outsideResult)
              (* Some variety of done (since not a referral) *)
              else 
                nm <- GetRequestName reqId;
                match nm with
                | None => ret (r, InvalidId reqId pac)
                | Some reqName =>
                  _ <- DeletePendingRequestInfo reqId; (* TODO return the proper rep *)
                  _ <- DeleteCachedNameResult reqName;
                if isAnswer pac then
                  (* Update cache *)
                  _ <- InsertResultForDomain timeArrived (Answer reqName pac);
                  (* Done, forward it on *)
                  ret (r, ClientAnswer reqId pac)
                else match failure with
                     (* Failure. Done, forward it on *)
                     | Some soa => 
                       (* Update cache *)
                       _ <- InsertResultForDomain timeArrived (Failure reqName pac soa);
                       ret (r, ClientFailure reqId pac soa)
                     | None => ret (r, MissingSOA reqId pac) (* will also result in request del *)
                     end
                end
          end
   }.

(* General TODO

- TODO.txt
- authoritative server needs to be patched for packet changes
- fill in stubs
- pass rep around properly in process
- Filter rows by record type and class
- Bounded amount of work (delete a referral in SLIST when queried too many times)
- Returning all answer/authority/additional instead of just one (re-hierarchizing rows into packet)
- Proper SBELT IP
- Dealing with CNAME; requires FueledFix
- CNAME in answers and having that as the answer for the domain and the aliases (see RFC 1034, 6.2.7)
- Inverse queries
- Parallelism (long term research goal)
variant types for cache pointers
caching opportunity with SLIST_ORDER (remove table, compute order whenever needed -> generate table)
- variant types for cache pointers
- caching opportunity with SLIST_ORDER (remove table, compute order whenever needed -> generate table) *)

(* Set Printing All. *)
Print DnsSpec_Recursive.
