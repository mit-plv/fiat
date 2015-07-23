Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindSuffixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import
        Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.


Definition server := name.      (* both IP and server name *)

Inductive WrapperResponse : Type :=
| Question : server -> packet -> WrapperResponse
| Answer : packet -> WrapperResponse
| Failure : packet -> WrapperResponse.

Definition DnsRecSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "MakeId" : rep x name -> rep x id,
      Method "AddRequest" : rep x (id * name) -> rep x bool,
      Method "GetRequestStage" : rep x id -> rep x option Stage,
      Method "UpdateRequestStage" : rep x (id * Stage) -> rep x bool,
                                    (* inlined in Process *)
      (* Method "GetServerForLongestSuffix" : rep x name -> rep x option (IP * id), *)
      (* Method "InsertServerForName" : rep x (name * IP * id) -> rep x bool, *)
      (* Method "EvictOldest" : rep x id -> rep x bool, *)
      Method "Process" : rep x (id * packet) -> rep x WrapperResponse
    }.

Print ADTSig.
Print ADT.                      (* TODO how does this dep. type work? *)
Variable s : list nat.
Check [[x in s | True]].

Definition upperbound' := upperbound (fun x => x).

Definition Build_RequestState id reqName stage :=
  < Build_Component (Build_Attribute sID nat) id,
  Build_Component (Build_Attribute sNAME name) reqName,
  Build_Component (Build_Attribute sSTAGE Stage) stage >.

Definition Build_CacheRow reqName reqIP reqId :=
  < Build_Component (Build_Attribute sNAME name) reqName,
  Build_Component (Build_Attribute sIP IP) reqIP,
  Build_Component (Build_Attribute sID id) reqId >.

Definition nonEmpty {A : Type} (l : list A) := negb (beq_nat (List.length l) 0).
(* from Smtp.v *)

Variable nms : list name.
Variable nm : name.
Check (List.length nm).
Check upperbound.
Print upperbound.
Check (upperbound (@List.length string) nms nm).

Definition Init := "Init".
Definition MakeId := "MakeId".
Definition AddRequest := "AddRequest".
Definition GetRequestStage := "GetRequestStage".
Definition UpdateRequestStage := "UpdateRequestStage".
Definition GetServerForLongestSuffix := "GetServerForLongestSuffix".
Definition InsertServerForName := "InsertServerForName".
Definition EvictOldest := "EvictOldest".
Definition Process := "Process".

Definition DnsSpec_Recursive : ADT DnsRecSig :=
  QueryADTRep DnsRecSchema {
    Def Constructor Init (_ : unit) : rep := empty,

      (* TODO bounded nat / dep type based on name length *)
      (* TODO can have (different id, same name) but not (different name, same id) unless multiple questions *)
      (* wrapper's responsibility to use this id for everything concerning this request 
and associate it with the packet (solve the latter by letting it generate the id and return in fn) *)
      (* ----- REQUESTS *)
      query MakeId (n : name) : id :=
        ids <- For (req in sREQUESTS)
            Return (req!sID);
        freshAscendingId <- {idx : nat | upperbound' ids idx };
        ret freshAscendingId,
      
        (* just change the type to query? *)
      update AddRequest (tup : id * name) : bool := 
        let (freshAscendingId, reqName) := tup in (* TODO inline makeid here *)
        Insert (Build_RequestState freshAscendingId reqName None) into sREQUESTS,
        (* ret (r, true), *)
        (* want to access r/rep so i can also return something besides a bool? *)

        (* boolean for wrapper *)
      query GetRequestStage (reqId : id) : option Stage :=
        stages <- For (req in sREQUESTS)
            Where (reqId = req!sID)
            Return (req!sSTAGE);
        (* there are 0 or 1 requests matching a specific id (since unique) *)
        ret (hd_error stages),

        update UpdateRequestStage (tup : id * Stage) : bool :=
          let (reqId, reqStage) := tup in
          q <- Update c from sREQUESTS
            making sSTAGE |= reqStage
          where (c!sID = reqId);
        let (updated, affected) := q in
        ret (updated, nonEmpty affected),

        (* TODO "delete request" method  *)

        (* ----- MAIN METHOD *)
        (* wrapper's responsibility to call addrequest first *)
        (* TODO ignoring sTYPE and sCLASS for now *)
    query Process (tup : id * packet) : WrapperResponse :=

          (* TODO inlining makes it take a really long time to check *)
        (* given a full name ["scholar", "google", "com"], return option IP 
           for the longest suffix of the URL, if an IP exists, return that. 
           otherwise return none *)
let GetServerForLongestSuffix (reqName : name) : Comp (option (IP * id)) :=
          suffixes <- For (req in sCACHE)
                     Where (IsSuffix reqName req!sNAME)
                     Return (req!sNAME, req!sIP, req!sID);
        let tupLength t := let '(x, y, z) := t in (@List.length string) x in
        longestSuffixes <- [[suffix in suffixes | upperbound tupLength suffixes suffix]];
        (* similar refinement lemma about just checking one of them *)
        (* TODO: some construct for "if non-empty, pick one and do X, otherwise do Y"? *)
        match longestSuffixes with
        | nil => ret None
        | (_, reqIP, reqID) :: _ => ret (Some (reqIP, reqID))
        end in

        (* given a full name ["scholar", "google", "com"], an IP, and an ID:
           if name is new, insert (name, ip, id) into cache 
           if name exists, update time (id) and ip for it
           (not checking if id/ip are different) *)
          (* TODO inline in let-def in process *)
let InsertServerForName (tup : name * IP * id) : Comp (QueryStructure qsSchemaHint' *bool) :=
          let '(reqName, reqIP, reqId) := tup in
          (* TODO: use the newly-discovered Count construct *)
          b <- For (n in sCACHE)
            Where (reqName = n!sNAME)
            Return ();
          match b with
          | nil => Insert (Build_CacheRow reqName reqIP reqId) into sCACHE
          | _ => (* TODO there should only be one entry for a name; enforce that? *)
            q <- Update n from sCACHE
              making [ sIP |= reqIP; sID |= reqId]
              where (reqName = n!sNAME);
          let (updated, affected) := q in
          ret (updated, nonEmpty affected)
          end in

          (* let EvictOldest (oldThreshold : id) : Comp bool := *)
          (*   b <- Delete c from sCACHE where (le c!sID oldThreshold); *)
          (* let (updated, deleted) := b in *)
          (* ret (updated, nonEmpty deleted) in *)

            (* TODO query = pure fn? change to update / use explicit rep *)
          let (reqId, p) := tup in
          let reqName := qname (questions p) in
          (* Figure out if it's a new request or a response by looking for its stage. *)
          reqStage <- For (req in sREQUESTS)
            Where (reqId = req!sID)
            Return req!sSTAGE;
        (* should be using `unique` here, TODO *)
        match hd_error reqStage with
        | None => ret (Failure p)
        | Some reqStage => 
          (match reqStage with
          | None =>
            cacheResult <- GetServerForLongestSuffix reqName;
            match cacheResult with
            | None =>
            (* TODO look in cache. needs to look for each prefix. check if cache says answer/ref/fail *)
            (* A new request. Send a Question with the root server name and the unchanged packet *)
            let rootName := ["."] in
            ret (Question rootName p)
            | Some (cachedReqID, cachedReqIP)  =>
            let rootName := ["."] in
            ret (Question rootName p)
            end
            (* TODO cache needs to store packets!!! *)
          | Some stageNum => 
            (* A response to an existing request. Figure out if it's an answer, a referral, 
               or a failure. TODO split out this part; reused with cache stuff *)
            (* If a packet with answers has referrals, they are ignored *)
            (match answers p with
            | pAnswer :: answers' => 
              (* Done! Forward on the packet *)
              (* TODO look in cache and update cache; check if cache says answer/ref/fail *)
              b <- Delete req from sREQUESTS where req!sID = reqId;
              ret (Answer p) 
            | nil =>
              (* Figure out if it's a referral or a failure *)
              (match authority p with
               | nil => 
                 (* Failure. TODO look in cache and update cache *)
                 b <- Delete req from sREQUESTS where req!sID = reqId;
                 ret (Failure p)
               | pAuthority :: authorities => 
                 (* Referral. *)
                 (* TODO authority should be the name, additional should be the real IP *)
                 (* TODO multiple authorities should be impossible; pick the first; could search all*)
                 (* TODO look in cache and update cache; check if cache says answer/ref/fail *)
                 (* TODO can't call this function so I'm inlining it *)
                 (* b <- UpdateRequestStage (reqId, reqStage + 1); *)
                 b <- Update req from sREQUESTS
                   making sSTAGE |= (Some (stageNum + 1))
                 where (req!sID = reqId);
                 (* TODO: discards the rest of the info in answer record; use? or have root info too *)
                 ret (Question (aname pAuthority) p)
               end)
            end)
          end)
        end
              }.

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

(* Set Printing All. *)
Print DnsSpec_Recursive.
(* TODO: implement it! *)

(* ------------------------------- *)
(* Old signature and spec *)

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddData" (t : DNSRRecord) : bool :=
      Insert t into sCOLLECTIONS,

    query "Process" (p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsSuffix n r!sNAME) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" / suffix the other way *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
            Then
              bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              if b                (* If the record's QNAME is an exact match  *)
              then
                unique b,                         (* only one match (unique / otherwise) *)
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ t <> CNAME ->>      (* and the query did not request a CNAME *)

                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                                                    (* ?? Shouldn't this use the sDATA ?? *)
                  ret (addan p' b)
                      (* addan : packet -> DNSRRecord -> packet *)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                (* multiple matches -- add them all as answers in the packet *)
                  ret (List.fold_left addan bfrs (buildempty p))
              else              (* prefix but record's QNAME not an exact match *)
                (* return all the longest-prefix records that are nameserver records -- 
                 return a referral to the authoritative servers for those subdomains (need to modify to use the "additional" field?) *)
                (* pick something in the list ("best one") TODO *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

(* -------------------------------------------------------------------------------------- *)

(* TODO [autorewrite with monad laws] breaks when this is moved into DnsLemmas *)

(* implement the DNS record constraint check as code that counts the number of occurrences of
the constraint being broken (refines the boolean x1 in AddData) *)
Lemma refine_count_constraint_broken :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}
           (If (beq_RRecordType n!sTYPE CNAME)
               Then count <- Count
               For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                     (fun tup : Tuple =>
                                        Where (n!sNAME = tup!sNAME)
                                              Return tup ));
            ret (beq_nat count 0) Else ret true).
Proof.
  intros.
  simpl in *.
  
  intros; setoid_rewrite refine_pick_decides at 1;
  [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
  (* refine existence check into query. *)
  match goal with
      |- context[{b | decides b
                              (exists tup : @IndexedTuple ?heading,
                                 (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
      =>
      let H1 := fresh in
      let H2 := fresh in
      makeEvar (Ensemble (@Tuple heading))
               ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                     [unfold Same_set, Included, Ensembles.In;
                       split; [intros x H; pattern (indexedElement x);
                               match goal with
                                   |- ?P'' (indexedElement x) => unify P' P'';
                                     simpl; eauto
                               end
                              | eauto]
                     |
                     assert (DecideableEnsemble P') as H2;
                       [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                       | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  remember n!sTYPE; refine pick val (beq_RRecordType d CNAME); subst;
  [ | case_eq (beq_RRecordType n!sTYPE CNAME); intros;
      rewrite <- beq_RRecordType_dec in H; find_if_inside;
      unfold not; simpl in *; try congruence ].
  simplify with monad laws.
  autorewrite with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------------------- *)

Theorem DnsManual :
  MostlySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

  unfold DnsSpec.

  start sharpening ADT. {
hone method "AddData". {
simpl in *.
(* Set Printing All. auto. *)
Check
       (QSInsert (@Build_QueryStructureHint DnsSchema r_n)
        (@Build_BoundedIndex string
           (@Datatypes.cons string sCOLLECTIONS (@Datatypes.nil string))
           sCOLLECTIONS
           (@Build_IndexBound string sCOLLECTIONS
              (@Datatypes.cons string sCOLLECTIONS (@Datatypes.nil string)) O
              (@eq_refl (option string) (@Some string sCOLLECTIONS)))) n).
(* Insert n into sCOLLECTIONS *)
(*      : Comp (QueryStructure qsSchemaHint' * bool) *)
    
  hone method "Process". {
    simpl in *.
    simplify with monad laws.
    (* Find the upperbound of the results. *)
    etransitivity.
    apply refine_under_bind; intros. (* rewrite? *)
    (* rewrite map_app, map_map, app_nil_r, map_id; simpl. *)
    etransitivity.
    apply refine_bind.
    match goal with
      |- refine _ (?H) => let id := fresh in set (id := H) in *
    end. (* rename ?whatever to H(number) *)
    (* Should honing if branches also be their own tactic? *)
    etransitivity.
    apply refine_If_Then_Else.
    match goal with
      |- context [ [[r in ?A | upperbound ?f ?l r]] ] =>
      pose (@refine_find_upperbound _ f A)
    end.
    etransitivity.
    { apply refine_bind; eauto.
      intro; higher_order_reflexivity. }

    setoid_rewrite (@refine_decides_forall_In' _ _ _ _).
    simplify with monad laws.
    etransitivity.
    Check refine_bind.
    (* implement decision procedure *)
    { 
      apply refine_bind;
      [ apply refine_check_one_longest_prefix_s
      | intro; higher_order_reflexivity ].
      intros. clear H. clear H1. unfold get_name. 
      eapply For_computes_to_In in H0.
      inv H0.
      - apply H.
      - pose proof IsSuffix_string_dec. intros. auto.
      - auto.
    }
    simplify with monad laws.
    setoid_rewrite refine_if_If.
    apply refine_If_Then_Else.
    etransitivity.
    { (* Locate "unique". *)
      
      (* setoid_rewrite refine_check_one_longest_prefix_CNAME. *)
      (* simplify with monad laws. *)
      (* reflexivity. *)
      
      apply refine_bind;        (* rewrite instead of apply *)
      [ eapply refine_check_one_longest_prefix_CNAME | intro; higher_order_reflexivity ].

      inversion H0.
      inversion H2. clear H2.
      - eapply tuples_in_relation_satisfy_constraint_specific.
        Check refine_check_one_longest_prefix_CNAME. apply H0.
      (* exciting! *)
      -                        
        clear H.
        intros.
        instantiate (1 := (qname (questions n))). 
        eapply For_computes_to_In in H0.
        inv H0. unfold IsSuffix in *. unfold get_name.
      + apply H2.
      + pose proof IsSuffix_string_dec. intros. auto.
      + auto.
    }
    simplify with monad laws.
    reflexivity. reflexivity.
    
    reflexivity. subst H1; reflexivity.
    unfold pointwise_relation; intros; higher_order_reflexivity.
    finish honing. finish honing.
}

  start_honing_QueryStructure'.

  hone method "AddData".
  {
    simpl in *.
    Print EnsembleInsert. 
    (* whatever data-integrity constraints there are on the relation, they get automatically added as checks/decision procedures on this (the mutator)  *)
    (* what is H? I guess an unimplemented something of the right type (or whose type is of the right type)? *)

    (* AddData has been expanded in method StringId0 *)
    (* refine (AddData body) (H r_n n) <-- what is that? *)
    (* H := existential variable of the correct (?) type,
       r_n : UnConstrQueryStructure DnsSchema, n : DNSRRecord*)
    (* x1 = check constraint between n (the record) and every other tuple  *)
    (* x2 = check constraint between every other tuple and n (the record) *)
    (* doesn't know that the constraint is symmetric? *)

    (* redundant *)
    (* subst_all. *)
    (* match goal with *)
    (*   |- refine _ (?H _ _) => let id := fresh in set (id := H) in * *)
    (* end.                        (* replace ex var with name H again *) *)
    (* simpl in *. *)
    Check refine_count_constraint_broken.
    (* lemmas like this -- they should be manually factored out and proved, right? *)
    (* how automated is the proof of this lemma? will automation just produce a lot of individual subgoals for each nontrivial decision procedure / chunk of code? *)
    Print refine.
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    Check refine_If_Then_Else_Bind.
    Check Bind_refine_If_Then_Else.
    setoid_rewrite refine_If_Then_Else_Bind.
    setoid_rewrite Bind_refine_If_Then_Else.
    etransitivity.
    Check refine_If_Then_Else.
    apply refine_If_Then_Else.
    - simplify with monad laws.
      apply refine_under_bind; intros. (* x0 disappears? *)
      Check refine_Count.
      setoid_rewrite refine_Count; simplify with monad laws.
      apply refine_under_bind; intros.
      (* remove duplicate check *)
      (* (simplifies x1) *)
      setoid_rewrite refine_subcheck_to_filter; eauto.
      simplify with monad laws.
      rewrite clear_nested_if by apply filter_nil_is_nil.
      (* removes one of the repeated rets, and the filter dec -- how? *)
      higher_order_1_reflexivity. (* ? where did the next goal come from? *)
      eauto with typeclass_instances.
    - simplify with monad laws.
      reflexivity.              (* refine (code) (existential variable) is cleared by reflexivity *)
    - finish honing.            (* can finish honing anywhere? *)
  }
  (* higher level of reasoning *)

  GenerateIndexesForAll         (* ? in IndexSelection, see GenerateIndexesFor *)
  (* specifies that you want to use the suffix index structure TODO *)
  ltac:(CombineCase2 matchFindSuffixIndex matchEqIndex)
         ltac:(fun attrlist => make simple indexes using attrlist).
  (* SearchTerm and SearchUpdateTerm: efficiently do quality test on the name columns *)
  (* it figures out what data structure to use *)
  (* BagMatchSearchTerm *)
  (* implement query as calls to abstract bag find function *)
  (* then plug in data structures that impl bag find (chooses b/t them?) *)

  (* hone constructor "Init". *)
  { 
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
   }

    (* hone method "AddData". *) {
    etransitivity.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    - apply refine_If_Then_Else.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                        ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                        ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                      ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                             ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
    - reflexivity.
    - finish honing.
    }

  (* hone method "Process". *) {
    simplify with monad laws.
    implement_Query             (* in AutoDB, implement_Query' has steps *)
      ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                           ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
    simplify with monad laws.
    simpl.
    setoid_rewrite (refine_pick_val _ H).
    simplify with monad laws.
    setoid_rewrite (@refine_filtered_list _ _ _ _).
    finish honing.
  }
  
  FullySharpenQueryStructure' DnsSchema Index.
  (* implement_bag_methods needs to be patched for this goal. *)

  - implement_bag_methods.
  - implement_bag_methods.
Time Defined.

    Definition DnsDelegateReps
    : ilist (fun ns => Type) (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact (list (@Tuple
           <sNAME :: name, sTYPE :: RRecordType, sCLASS :: RRecordClass,
              sTTL :: nat, sDATA :: string>%Heading)).
    Defined.

    Definition DnsDelegateSearchUpdateTerms
    : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
             (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact  DnsSearchUpdateTerm.
    Defined.



    Definition DnsDelegateImpls
    : i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                   (Rep : Type) =>
                 ComputationalADT.pcADT
                   (BagSig (@Tuple (schemaHeading (relSchema ns)))
                           (BagSearchTermType SearchTerm)
                           (BagUpdateTermType SearchTerm))
                   Rep)
              DnsDelegateSearchUpdateTerms
              DnsDelegateReps.
      simpl; econstructor; [ | econstructor ].
      let p := eval simpl in (projT2 (BagADTImpl (fun _ => true)
                         (@ListAsBag
                            _
                            (BagSearchTermType DnsSearchUpdateTerm)
                            (BagUpdateTermType DnsSearchUpdateTerm)
                            {| pst_name := nil;
                               pst_filter := fun _ => true |}
                            (BagMatchSearchTerm DnsSearchUpdateTerm)
                            (BagApplyUpdateTerm DnsSearchUpdateTerm) ))) in
          exact p.
    Defined.

    Definition DnsImpl : SharpenedUnderDelegates DnsSig.
      Time let
          Impl := eval simpl in (projT1 DnsManual) in exact Impl.
    Defined.

    Print DnsImpl.
    Definition ExtractWorthyDNSImpl : ComputationalADT.cADT DnsSig.
      let s := eval unfold DnsImpl in DnsImpl in
          let Impl := eval simpl in
          (Sharpened_Implementation s
                                    (LookupQSDelegateReps DnsDelegateReps)
                                    (LookupQSDelegateImpls DnsDelegateImpls)) in exact Impl.
    Defined.

    Print ExtractWorthyDNSImpl.

    Extraction "bar.ml" ExtractWorthyDNSImpl.
