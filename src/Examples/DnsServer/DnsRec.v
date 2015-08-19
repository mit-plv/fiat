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
        Fiat.Examples.DnsServer.DnsSchema_new
        Fiat.Examples.DnsServer.DnsLemmas. (* might need _new *)

Definition DnsRecSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,

      (* request state methods; ignoring other methods like getting class/type *)
      Method "MakeId" : rep x name -> rep x id,
      Method "AddRequest" : rep x (packet * id) -> rep x bool,
      Method "GetRequestStage" : rep x id -> rep x option Stage,
      Method "UpdateRequestStage" : rep x (id * Stage) -> rep x bool,

      (* cache methods *)
      Method "InsertResultForDomain" : rep x (name * WrapperResponse) -> rep x bool,
      Method "DeleteResultForDomain" : rep x name -> rep x CacheResult,
                                       (* + update (= delete+insert), checkinvariant,
                                          and packaging a set of rows into a WrapperResponse7 *)
      Method "GetServerForLongestPrefix" : rep x name -> rep x CacheResult
      (* Method "EvictOldest" : rep x id -> rep x bool, *)
      (* things stay in the cache -> deleting ones with TTL 0 preserves (decrement all) *)
      (* or, given the current time, decrement TTL? *)

      (* main method *)
      (* Method "Process" : rep x (id * packet) -> rep x WrapperResponse *)
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

Definition nonEmpty {A : Type} (l : list A) := negb (beq_nat (List.length l) 0).
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

Definition DnsSpec_Recursive : ADT DnsRecSig :=
  (* TODO move to definitions *)
  let Init := "Init" in
  let MakeId := "MakeId" in
  let AddRequest := "AddRequest" in
  let GetRequestStage := "GetRequestStage" in
  let UpdateRequestStage := "UpdateRequestStage" in
  let GetServerForLongestPrefix := "GetServerForLongestPrefix" in
  let InsertResultForDomain := "InsertResultForDomain" in
  let DeleteResultForDomain := "DeleteResultForDomain" in
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
            (* where False; *)
        let (updated, affected) := q in
        ret (updated, nonEmpty affected),

        (* TODO "delete request" method  *)

        (* ----- CACHE *)
          (* TODO inline in let-def in process *)
        (* TODO update cache pointer table *)
        (* assumes that someone has already checked that the domain is not in any of the caches *)
       update InsertResultForDomain (r : rep, tup : name * WrapperResponse) : bool :=
          let '(reqName, reqResult) := tup in
            match reqResult with
            | Answer pac => 

              (* monad iteration instead *)
              let fix InsertAll rowFunc tups :=
                  match tups with
                  | nil => ret (r, false)
                  (* this shouldn't happen since an answer must have at >= 1 answer record *)
                  | ptup :: ptups =>
                    b <- Insert (rowFunc ptup) into r!sCACHE_ANSWERS;
                  InsertAll rowFunc ptups
                  end in 

              let flattenWithRec p type rec :=
                  let q := questions p in
                  (reqName, type, aname rec, atype rec, aclass rec, ttl rec, rdata rec) in
              let flattenPacket (p : packet_new.packet) type recs := List.map (fun rec => flattenWithRec p type rec) recs in
              let tups p := flattenPacket p PAnswer (answers p)
                                          ++ flattenPacket p PAuthority (authority p)
                                          ++ flattenPacket p PAdditional (additional p) in
              (* packet -> tuple with heading? tuple surgery notation -- write down example *)
              (* do a pick *)
              (* all tuples such that (p fields ... answers fields...); insert tuples *)
              _ <- Insert (Build_CachePointer reqName CAnswers) into r!sCACHE_POINTERS;
            InsertAll Build_CacheAnswersRow (tups pac)

            | Failure pac soa =>
              (* ignoring authority/answer/additional fields; using only the one SOA *)
              let mkFailTup p soa := 
                  (reqName, sourcehost soa, contact_email soa, 
                   serial soa, refresh soa, retry soa, expire soa, minTTL soa) in
              _ <- Insert (Build_CachePointer reqName CFailures) into r!sCACHE_POINTERS;
            Insert (Build_CacheFailuresRow (mkFailTup pac soa)) into r!sCACHE_FAILURES
            end,

            (* need to do special stuff for linking authority and additional fields *)
            (* for each auth in authority, for each addl in additional,
             if auth's rdata = addl's name, flatten the whole thing into a row and add it *)
            (* | Question serv pac => *)

            (*   let fix InsertAll' rowFunc tups := *)
            (*   match tups with *)
            (*   | nil => ret (r, false) *)
            (*   | ptup :: ptups => *)
            (*     b <- Insert (rowFunc ptup) into r!sCACHE_REFERRALS; *)
            (*     InsertAll' rowFunc ptups *)
            (*   end in  *)
              
            (*   let tupsJoin pac := *)
            (*       let authRdataMatchesAddlName (tup2 : answer * answer) := *)
            (*           let (auth, addl) := tup2 in *)
            (*           beq_name (rdata auth) (aname addl) in *)
            (*       let auth_addl_join := list_join authRdataMatchesAddlName  *)
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
              
            (*   _ <- Insert (Build_CachePointer reqName CReferrals) into r!sCACHE_POINTERS;               *)
            (*   InsertAll' Build_CacheReferralsRow (tupsJoin pac) *)

            (* | CReferrals => *)
          (*   referral_res <- Delete row from r!sCACHE_REFERRALS where row!sREFERRALDOMAIN = domain; *)
          (*   let (r, ref_deleted) := referral_res in *)
          (*   ret (r, Ref ref_deleted) *)
            
            (* TODO: look in cache pointer table and delete that pointer afterward *)
            update DeleteResultForDomain (r : rep, domain : name) : CacheResult :=
          results <- For (pointer in r!sCACHE_POINTERS)
                   Where (pointer!sDOMAIN = domain)
                   Return (pointer!sCACHETABLE);
        match results with
        | nil => ret (r, Nope)
              
        | tbl :: _ =>
          match tbl with
          | CAnswers =>
            answer_res <- Delete row from r!sCACHE_ANSWERS where row!sDOMAIN = domain;
            let (r, ans_deleted) := answer_res in
            ret (r, Ans ans_deleted)
          | CFailures =>
              failure_res <- Delete row from r!sCACHE_FAILURES where row!sDOMAIN = domain;
            let (r, fail_deleted) := failure_res in
            ret (r, Fail (listToOption fail_deleted))
          end
        end,

        (* the real update function = delete everything for the name, then insert the result *)

        (* given a full name ["scholar", "google", "com"], return option IP 
           for the longest suffix of the URL, if an IP exists, return that. 
           otherwise return none *)
          (* Other server uses suffix, so we will use suffix too *)

        query GetServerForLongestPrefix (r : rep, reqName : name) : CacheResult :=
          (* copies the pattern from delete; factor out? *)
          results <- For (pointer in r!sCACHE_POINTERS)
                   Where (pointer!sDOMAIN = reqName)
                   Return (pointer!sCACHETABLE);
        match results with
        | nil =>
          (* Need to do the suffix thing here *)
(* For Answers: ? 
For Failures: ?

If nothing: return Nope  *)
          (* suffixes <- For (req in r!sCACHE_ANSWERS) *)
            (*          Where (IsPrefix reqName req!sDOMAIN) *)
            (*          Return req; *)
            (* let domainLength (tup : AnswerRow) := List.length tup!sDOMAIN in *)
            (* longestPrefixes <- [[suffix in suffixes | upperbound domainLength suffixes suffix]]; *)
            (* match longestPrefixes with *)
            (* | nil => ret None *)
            (* | row :: rows => *)
            (*   sufResults <- For (pointer in r!sCACHE_POINTERS) *)
            (*              Where (pointer!sDOMAIN = reqName) *)
            (*           Return (pointer!sCACHETABLE); *)
            (*   match results with *)
            (*   | nil => ret None *)
            (*   | table :: _ =>  *)
            (*   (* TODO: arbitrarily pick the first of the longest suffixes *) *)
            (*   (* pick ONE of the longest suffixes [same?] then look in the pointer table for which table it's in then then get all of the rows for that suffix  and make it into a packet/wrapperresponse *) *)
          (*   ret None *)
          ret Nope
        | table :: _ => 
          match table with
          | CFailures => 
            (* There should be only one row in Failures, containing the SOA record *)
            (* This domain [s.g.com] failed. If we have any result for the longest prefix, return it.
                Otherwise, return failure. TODO *)
            nameRes <- For (f in r!sCACHE_FAILURES)
                    Where (f!sDOMAIN = reqName)
                    Return f;
          ret (Fail (listToOption nameRes))

          | CAnswers => 
            (* There may be multiple rows in Answers, containing various answer/authority/addl *)
            (* This returns all of them and leaves it to Process to hierarchize/query them *)
            nameRes <- For (f in r!sCACHE_ANSWERS)
                    Where (f!sDOMAIN = reqName)
                    Return f;            
            ret (Ans nameRes)
          end
        end
          
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
          (*   ret (updated, nonEmpty deleted), *)

          (* ----- MAIN METHOD *)

          (* When we put in that there's a referral for a name:
what if there's a worse (shorter) referral with a longer TTL? and a better (longer) referral with a shorter TTL? what if one is already in the cache? should one be evicted in favor of the other? should we store both and use them depending on the time?

Also, might a referral for one name also serve as a referral for another? (yes, that's why we have the suffix searching)

Need some way to ensure that
if name => referral is in the table,
it's the "best possible" ones/bundle of them? what about WRT record type?
scholar.google.com => 
  g83429p.x.edu (at IP 10.2.0.27) will give the answer for google.com 
 *)
          
        (* wrapper's responsibility to call addrequest first *)
        (* TODO ignoring sTYPE and sCLASS for now *)
    (* query Process (tup : id * packet) : WrapperResponse := *)
    (*         (* TODO query = pure fn? change to update / use explicit rep *) *)
    (*       let (reqId, p) := tup in *)
    (*       let reqName := qname (questions p) in *)
    (*       (* Figure out if it's a new request or a response by looking for its stage. *) *)
    (*       reqStage <- For (req in r!sREQUESTS) *)
    (*         Where (reqId = req!sID) *)
    (*         Return req!sSTAGE; *)
    (*     (* should be using `unique` here, TODO *) *)
    (*     match hd_error reqStage with *)
    (*     | None => ret (Failure p) *)
    (*     | Some reqStage =>  *)
    (*       (match reqStage with *)
    (*       | None =>  *)
    (*         (* A new request. Send a Question with the root server name and the unchanged packet *) *)
    (*         (* the question in the packet should never change *) *)
    (*         (* TODO look in cache. needs to look for each prefix. check if cache says answer/ref/fail *) *)
    (*         let rootName := ["."] in *)
    (*         ret (Question rootName p) *)
    (*       | Some stageNum =>  *)
    (*         (* A response to an existing request. Figure out if it's an answer, a referral,  *)
    (*            or a failure. TODO split out this part; reused with cache stuff *) *)
    (*         (* If a packet with answers has referrals, they are ignored *) *)
    (*         (match answers p with *)
    (*         | pAnswer :: answers' =>  *)
    (*           (* Done! Forward on the packet *) *)
    (*           (* TODO look in cache and update cache; check if cache says answer/ref/fail *) *)
    (*           b <- Delete req from r!sREQUESTS where req!sID = reqId; *)
    (*           ret (Answer p)  *)
    (*         | nil => *)
    (*           (* Figure out if it's a referral or a failure *) *)
    (*           (match authority p with *)
    (*            | nil =>  *)
    (*              (* Failure. TODO look in cache and update cache *) *)
    (*              b <- Delete req from r!sREQUESTS where req!sID = reqId; *)
    (*              ret (Failure p) *)
    (*            | pAuthority :: authorities =>  *)
    (*              (* Referral. *) *)
    (*              (* TODO authority should be the name, additional should be the real IP *) *)
    (*              (* TODO multiple authorities should be impossible; pick the first; could search all*) *)
    (*              (* TODO look in cache and update cache; check if cache says answer/ref/fail *) *)
    (*              (* TODO can't call this function so I'm inlining it *) *)
    (*              (* b <- UpdateRequestStage (reqId, reqStage + 1); *) *)
    (*              b <- Update req from r!sREQUESTS *)
    (*                making sSTAGE |= (Some (stageNum + 1)) *)
    (*              where (req!sID = reqId); *)
    (*              (* TODO: discards the rest of the info in answer record; use? or have root info too *) *)
    (*              ret (Question (aname pAuthority) p) *)
    (*            end) *)
    (*         end) *)
    (*       end) *)
    (*     end *)
              }.

(* Set Printing All. *)
Print DnsSpec_Recursive.

(* wrapper: makes id
adds the request with name and id; we indicate its stage is None, so it hasn't started yet

once we have the id and packet, we check:

is it old or new? (is the stage None or some number?)
  (the question in the packet should match the name corresponding to the IP)
(pretending we have no cache for now)

- a new request: 
  send a Question with the root server name and the packet (unchanged?)
  update stage to 0 (stage 2 = we have just sent a question about "google" in scholar.google.com. 0 corresponds to the root server)
  (TODO: since we have no IPs for now, just use the name ".")

- an old request: 
  it might be an answer, or it might be a referral
  if the answers section contains answers, just return all of them (i.e. forward the packet on)
    remove request (success)
    update cache with answers TODO

  if the answer section is empty:
    // TODO // : should fix other server to use authority AND additional

    if the authority section contains >1 authority:
      TODO: pick any one authority, do the case below. this might be impossible though according to RFC
      (or it could search all of them)

    if the authority section contains 1 authority: 
      send Question with the name of that server and the unchanged packet
      update request stage to stage + 1
      update cache TODO
       
    if the authority section contains 0 authorities:
      it's not an answer, so this failed. forward packet on (as failure)
      remove request
      update cache TODO
 *)
