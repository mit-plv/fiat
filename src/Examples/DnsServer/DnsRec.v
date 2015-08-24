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
        Fiat.Examples.DnsServer.DnsLemmas. (* might need _new *)

Require Import Fiat.Examples.DnsServer.DnsSchema_new.

Definition DnsRecSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,

      (* request state methods; ignoring other methods like getting class/type *)
      Method "MakeId" : rep x name -> rep x id,
      Method "AddRequest" : rep x (packet * id) -> rep x bool,
      Method "GetRequestStage" : rep x id -> rep x option Stage,
      Method "UpdateRequestStage" : rep x (id * Stage) -> rep x bool,

      (* cache methods *)
      Method "InsertResultForDomain" : rep x ToStore -> rep x bool,
      Method "DeletePendingRequestInfo" : rep x id -> rep x bool,
      Method "DeleteCachedNameResult" : rep x name -> rep x CacheResult,
                                       (* + update (= delete+insert), checkinvariant,
                                          and packaging a set of rows into a WrapperResponse7 *)
      Method "GetServerForLongestSuffix" : rep x name -> rep x CacheResult,
      (* Method "EvictOldest" : rep x id -> rep x bool, *)
      (* things stay in the cache -> deleting ones with TTL 0 preserves (decrement all) *)
      (* or, given the current time, decrement TTL? *)

      (* main method *)
      Method "Process" : rep x FromOutside -> rep x ToOutside
                                                  (* needs to add/update requests, not the client *)
    }.

Print ADTSig.
Print ADT.                      (* TODO how does this dep. type work? *)
Variable s : list nat.
Check [[x in s | True]].        (* Comp (list nat) -- multiple choice *)
Check { x : nat | True }.   (* Comp nat -- single choice *)
Check { b : bool | decides b True }. (* Comp bool -- check *)

Definition upperbound' := upperbound (fun x => x).

(* Boilerplate *)
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

Definition Build_CachePointer reqName table :=
  < Build_Component (Build_Attribute sDOMAIN name) reqName,
    Build_Component (Build_Attribute sCACHETABLE CacheTable) table >.

Definition Build_CacheReferralsRow tup :=
  let '(referralDomain, rType, rClass, rTTL, serverDomain, sType, sClass, sTTL, sIP) := tup in
  < Build_Component (Build_Attribute sREFERRALDOMAIN name) referralDomain,
  Build_Component (Build_Attribute sRTYPE RRecordType) rType,
  Build_Component (Build_Attribute sRCLASS RRecordClass) rClass,
  Build_Component (Build_Attribute sRTTL nat) rTTL,

  Build_Component (Build_Attribute sSERVERDOMAIN name) serverDomain,
  Build_Component (Build_Attribute sSTYPE RRecordType) sType,
  Build_Component (Build_Attribute sSCLASS RRecordClass) sClass,  
  Build_Component (Build_Attribute sSTTL nat) sTTL,
  Build_Component (Build_Attribute sSIP name) sIP >.

Definition Build_CacheAnswersRow tup :=
  let '(rDomain, rSection, rName, rType, rClass, rTTL, rRdata) := tup in
  < Build_Component (Build_Attribute sDOMAIN name) rDomain,
  Build_Component (Build_Attribute sPACKET_SECTION PacketSection) rSection,
  Build_Component (Build_Attribute sNAME name) rName,
  Build_Component (Build_Attribute sTYPE RRecordType) rType,
  Build_Component (Build_Attribute sCLASS RRecordClass) rClass,
  Build_Component (Build_Attribute sTTL nat) rTTL,
  Build_Component (Build_Attribute sRDATA name) rRdata >.

Definition Build_CacheFailuresRow tup :=
  let '(rDomain, rHost, rEmail, rSerial, rRefresh, rRetry, rExpire, rMinTTL) := tup in
  < Build_Component (Build_Attribute sDOMAIN name) rDomain,
  Build_Component (Build_Attribute sHOST name) rHost,
  Build_Component (Build_Attribute sEMAIL name) rEmail,
  Build_Component (Build_Attribute sSERIAL nat) rSerial,
  Build_Component (Build_Attribute sREFRESH nat) rRefresh,
  Build_Component (Build_Attribute sRETRY nat) rRetry,
  Build_Component (Build_Attribute sEXPIRE nat) rExpire,    
  Build_Component (Build_Attribute sMinTTL nat) rMinTTL >.

Definition nonempty {A : Type} (l : list A) := negb (beq_nat (List.length l) 0).
(* from Smtp.v *)

Variable nms : list name.
Variable nm : name.
Check (List.length nm).
Check upperbound.
Print upperbound.
Check (upperbound (@List.length string) nms nm).

Definition listToOption {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | x :: _ => Some x
  end.

Definition list_join {A B : Type} f (l1 : list A) (l2 : list B) 
  : list (A * B) := 
filter f (list_prod l1 l2).


(* Set Printing All. *)
Print FromOutside.
Definition DnsSpec_Recursive : ADT DnsRecSig :=
  (* TODO move to definitions *)
  let Init := "Init" in
  let MakeId := "MakeId" in
  let AddRequest := "AddRequest" in
  let GetRequestStage := "GetRequestStage" in
  let UpdateRequestStage := "UpdateRequestStage" in
  let GetServerForLongestSuffix := "GetServerForLongestSuffix" in
  let InsertResultForDomain := "InsertResultForDomain" in
  let DeletePendingRequestInfo := "DeletePendingRequestInfo" in
  let DeleteCachedNameResult := "DeleteCachedNameResult" in
  let EvictOldest := "EvictOldest" in
  let Process := "Process" in

  QueryADTRep DnsRecSchema {
    Def Constructor Init (_ : unit) : rep := empty,

      (* TODO bounded nat / dep type based on name length *)
      (* TODO can have (different id, same name) but not (different name, same id) unless multiple questions *)
      (* wrapper's responsibility to use this id for everything concerning this request 
and associate it with the packet (solve the latter by letting it generate the id and return in fn) *)
      (* ----- REQUESTS *)
      query MakeId (r : rep, n : name) : id :=
        ids <- For (req in r!sREQUESTS)
            Return (req!sID);
        freshAscendingId <- {idx : nat | upperbound' ids idx };
        ret freshAscendingId,
      
      update AddRequest (r : rep, tup : packet * id) : bool := 
        let (pac, freshAscendingId) := tup in (* TODO inline makeid here *)
        Insert (Build_RequestState pac freshAscendingId None) into r!sREQUESTS,

        (* boolean for wrapper *)
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

        (* TODO "delete request" method  *)

        (* ----- CACHE *)
        (* assumes that someone has already checked that the domain is not in any of the caches *)
       update InsertResultForDomain (r : rep, tup : ToStore) : bool :=
          match tup with
          | Answer reqName pac => 

            (* monad iteration instead. TODO param over table *)
            (* TODO add rep as a parameter *)
            let fix InsertAll rowFunc tups :=
                match tups with
                (* this shouldn't happen since an answer must have at >= 1 answer record *)
                | nil => ret (r, false)
                | ptup :: ptups =>
                  b <- Insert (rowFunc ptup) into r!sCACHE_ANSWERS;
                InsertAll rowFunc ptups
                end in

            let flattenWithRec p type rec :=
                let q := questions p in
                (reqName, type, aname rec, atype rec, aclass rec, ttl rec, rdata rec) in
            let flattenPacket p type recs := List.map (fun rec => flattenWithRec p type rec) recs in
            let tups p := flattenPacket p PAnswer (answers p)
                                        ++ flattenPacket p PAuthority (authority p)
                                        ++ flattenPacket p PAdditional (additional p) in
            (* packet -> tuple with heading? tuple surgery notation -- write down example *)
            (* do a pick TODO ^ v*)
            (* all tuples such that (p fields ... answers fields...); insert tuples *)
            res1 <- Insert (Build_CachePointer reqName CAnswers) into r!sCACHE_POINTERS;
          let (r1, _) := res1 in
          InsertAll Build_CacheAnswersRow (tups pac)

          | Failure reqName pac soa =>
            (* ignoring authority/answer/additional fields; using only the one SOA *)
            let mkFailTup p soa := 
                (reqName, sourcehost soa, contact_email soa, 
                 serial soa, refresh soa, retry soa, expire soa, minTTL soa) in
            res1 <- Insert (Build_CachePointer reqName CFailures) into r!sCACHE_POINTERS;
          let (r1, _) := res1 in
          Insert (Build_CacheFailuresRow (mkFailTup pac soa)) into r1!sCACHE_FAILURES

          (* TODO maybe shouldn't be part of the WrapperResponse type / should be in sep fn *)
          | Referral reqId pac => ret (r, false)
          end,

            (* for the pending request reqId, append all referral rows to SLIST *)
            (* need to generate ids, update order, check match count, TTL, etc *)
            (* | Question reqId pac => *)
            (*   (* TODO param on table *) *)
            (*   let fix InsertAll' rowFunc tups := *)
            (*   match tups with *)
            (*   | nil => ret (r, false) *)
            (*   | ptup :: ptups => *)
            (*     b <- Insert (rowFunc ptup) into r!sCACHE_REFERRALS; *)
            (*     InsertAll' rowFunc ptups *)
            (*   end in *)
              
            (*   (* need to do special stuff for linking authority and additional fields *) *)
            (*   (* for each auth in authority, for each addl in additional, *)
            (*  if auth's rdata = addl's name, flatten the whole thing into a row and add it *) *)
            (*   let tupsJoin pac := *)
            (*       let authRdataMatchesAddlName (tup2 : answer * answer) := *)
            (*           let (auth, addl) := tup2 in *)
            (*           beq_name (rdata auth) (aname addl) in *)
            (*       let auth_addl_join := list_join authRdataMatchesAddlName *)
            (*                                       (authority pac) (additional pac) in *)
                  
            (*       let pairToPacketTup (tup2 : answer * answer) := *)
            (*           let q := questions pac in *)
            (*           let (auth, addl) := tup2 in *)
            (*           ( *)
            (*            (* id' pac, flags pac, qname q, qtype q, qclass q, *) *)
            (*            aname auth, atype auth, aclass auth, ttl auth, *)
            (*            aname addl, atype addl, aclass addl, ttl addl, *)
            (*            rdata addl) *)
            (*       in *)
            (*       map pairToPacketTup auth_addl_join in *)
              
            (*   (* _ <- Insert (Build_CachePointer reqName CReferrals) into r!sCACHE_POINTERS; *) *)
            (*          InsertAll' Build_CacheReferralsRow (tupsJoin pac) *)
            (* end, *)

            (* | CReferrals => *)
          (*   referral_res <- Delete row from r!sCACHE_REFERRALS where row!sREFERRALDOMAIN = domain; *)
          (*   let (r, ref_deleted) := referral_res in *)
          (*   ret (r, Ref ref_deleted) *)

          update DeletePendingRequestInfo (r : rep, reqId : id) : bool :=
           res1 <- Delete row from r!sREQUESTS where row!sID = reqId;
           let (r1, rows1) := res1 in
           res2 <- Delete row from r1!sSLIST_ORDERS where row!sREQID = reqId;
           let (r2, rows2) := res2 in
           res3 <- Delete row from r2!sSLIST where row!sREQID = reqId;
           let (r3, rows3) := res3 in
           ret (r3, nonempty rows1 || nonempty rows2 || nonempty rows3),
          
          (* TODO: given an id, clear the request's SLIST rows and order, and remove from pending reqs *)
          (* This deletes stuff from the CACHE *)
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

        query GetServerForLongestSuffix (r : rep, reqName : name) : CacheResult :=
          let getLongestSuffixes name :=
              (* TODO: filter by packetsection = answer? are authority and additional useful? *)
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
          | _ :: _ => ret (Ref longestSuffixes)
          | nil => 
          (* TODO: does prefix/subdomain failure imply domain failure? s.com fails -> c.s.com fails? *)
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
            ret (Ans nameRes)
          end
        end,
          
          (* TODO use  *)
        (* after a certain time, evict oldest names from cache,
           using either "oldest n names" or "all names with ips before threshold t" (here the latter). smaller ids are older, bigger ips are newer. including threshold *)
          (* update EvictOldest (threshold : nat) : bool := *)
          (*     (* also have an "update all s" *) *)
          (*     (* TODO failure s? *) *)
          (*     (* let increment (time : nat) (req : WrapperResponse) := req in *) *)
          (*     let removeOlder (threshold : nat) (records : list answer) := *)
          (*         [[ rec in records | ttl rec > threshold ]] in *)
          (*     let removeOldRecords (threshold : nat) (req : WrapperResponse) : Comp packet := *)
          (*         match req with *)
          (*         | Question _ p *)
          (*         | Answer p *)
          (*         | Failure p =>  *)
          (*           answers' <- removeOlder threshold (answers p); *)
          (*         authority' <- removeOlder threshold (authority p); *)
          (*         additional' <- removeOlder threshold (additional p); *)
          (*           ret (updateRecords p answers' authority' additional') *)
          (*         end in *)
          (*     (* this isn't right, what i want to do is REMOVE stuff from ans/au/add that are past the threshold, put that back in the packet, and UPDATE the request with that *) *)
          (*     (* layers: WrapperRequest Packet(Field) List Answer --> TTL *) *)
          (*     reqs <- For (req in sCACHE) *)
          (*          Return (req!sDOMAIN, req!sRESULT); *)
          (*   results <- flat_map  *)
          (*           (fun r => Build_CacheRow (fst r) (removeOldRecords threshold (snd r))) reqs; *)
          (*   (* older <- [[ req in reqs | TTLpast oldThreshold req!sRESULT ]]; *) *)
          (*   b <- Delete req from sCACHE where (List.In req reqs); *)
          (*   let (updated, deleted) := b in *)
          (*   ret (updated, nonempty deleted), *)

          (* ----- MAIN METHOD *)

          (* TODO need to inline other functions; stubs for now *)
        update Process (r : rep, tup : FromOutside) : ToOutside :=
          let SBELT := @nil ReferralRow in (* TODO, add root *)
          (* TODO inline; this is a stub *)
          (* TODO this doesn't take/return rep as the actual functions do *)
          let InsertResultForDomain (toStore : ToStore) : Comp bool := ret false in
          let GetServerForLongestSuffix (reqName : name) : Comp CacheResult := ret Nope in
          let DeleteCachedNameResult (domain : name) : Comp CacheResult := ret Nope in
          let DeletePendingRequestInfo (reqId : id) : Comp bool := ret false in
          (* let DeletePendingRequestInfo (r : rep) (reqId : id) : Comp bool := ret (r, false) in *)
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
          let GetRequestName (reqId : id) : Comp (option name) := (* pull out *)
            names <- For (req in r!sREQUESTS)
                  Where (reqId = req!sID)
                  Return (req!sQNAME);
            ret (hd_error names) in

          let '(reqId, pac, failure) := tup in
          let reqName := qname (questions pac) in
          
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
              suffixResults <- GetServerForLongestSuffix reqName;
              match suffixResults with
                (* Yes we have seen it *)
                (* TODO: these are unfinished *)
                | Fail failure =>
                  (* Put the failure in a packet and SOA, and return it *)
                  ret (r, ClientAnswer reqId pac)
                | Ans answers => 
                  (* Choose any (?) answer, put it in a packet, and return it *)
                  ret (r, ClientAnswer reqId pac)
                | Ref referrals =>
                  (* Initialize the SLIST with best referrals, then send a question w/ the first *)
                  ret (r, ServerQuestion reqId pac)
                (* No we haven't seen it *)
                | Nope => 
                  (* Add request to pending *)
                  (* Initialize the SLIST with SBELT, pick one and send a question w/ the first *)
                  ret (r, ServerQuestion reqId pac)  
              end                
          | Some pendingReq' => 
            (* Pending *)
            if isQuestion pac then
              ret (r, InvalidQuestion reqId)
            else
              (* Figure out if the packet is an answer, failure, or referral *)
              (* doesn't thoroughly check for malformed packets, e.g. contains answer and failure *)
              (* TODO: cache these results (need to get the name first) *)
              if isReferral pac then
                (* TODO: unfinished *)
                (* For each valid referral, pre-pend it to the SLIST, then send question w/ the first *)
                (* Update request's pending status *)
                ret (r, ServerQuestion reqId pac)
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
                  _ <- InsertResultForDomain (Answer reqName pac);
                  (* Done, forward it on *)
                  ret (r, ClientAnswer reqId pac)
                else match failure with
                     (* Failure. Done, forward it on *)
                     | Some SOA_Record => 
                       (* Update cache *)
                       _ <- InsertResultForDomain (Failure reqName pac SOA_Record);
                       ret (r, ClientFailure reqId pac SOA_Record)
                     | None => ret (r, InvalidPacket reqId pac) (* will also result in request del *)
                     end
                end
          end
          
        (* wrapper's responsibility to call addrequest first *)
        (* TODO ignoring sTYPE and sCLASS for now; list the other features i left out *)
        (* TODO update stage? *)
   }.

(* Set Printing All. *)
Print DnsSpec_Recursive.
