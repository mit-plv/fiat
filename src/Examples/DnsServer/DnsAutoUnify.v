Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation.

Require Import Fiat.Examples.DnsServer.DnsSchema.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * packet -> rep * packet
    }.

(* First stab at a declarative specification for the matching algorithm. *)
Inductive matchRR (RRecords : @IndexedEnsemble resourceRecord)
  : RRecordType
    -> name
    -> list resourceRecord (* answers *)
    -> list resourceRecord (* authority *)
    -> list resourceRecord (* additional *)
    -> Prop :=
  (* If the whole of QNAME is matched, we have found the node. *)

  (* If the data at the node is a CNAME, and QTYPE doesn't
     match CNAME, copy the CNAME RR into the answer section
     of the response, change QNAME to the canonical name in
     the CNAME RR, and go back to step 1. *)
| match_eq_CNAME :
    forall nm ttl qtype class rlength rdata answers authority additional,
      IndexedEnsemble_In RRecords
      <sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: CNAME, sRLENGTH :: rlength, sRDATA :: (inl rdata)>
      -> qtype <> CNAME
      -> matchRR RRecords qtype rdata answers authority additional
      -> matchRR RRecords qtype nm
                 (<sNAME :: nm, sTTL :: ttl, sCLASS :: class,
                  sTYPE :: qtype, sRLENGTH :: rlength, sRDATA :: (inl rdata)>
                  :: answers) authority additional

(* Otherwise, copy all RRs which match QTYPE into the answer section. *)
| match_eq_qtype :
    forall nm ttl qtype class rlength rdata,
      IndexedEnsemble_In RRecords
      <sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: qtype, sRLENGTH :: rlength, sRDATA :: rdata>
      -> matchRR RRecords qtype nm
                 [<sNAME :: nm, sTTL :: ttl, sCLASS :: class,
                  sTYPE :: qtype, sRLENGTH :: rlength, sRDATA :: rdata>] nil nil

(* If a match would take us out of the authoritative data,
   we have a referral.  This happens when we encounter a
   node with NS RRs marking cuts along the bottom of a
   zone.

   Copy the NS RRs for the subzone into the authority
   section of the reply.  Put whatever addresses are
   available into the additional section, using glue RRs
   if the addresses are not available from authoritative
   data or the cache. *)

| match_referral :
    forall qname nm ttl qtype class rlength rdata,
      IndexedEnsemble_In RRecords
      <sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: NS, sRLENGTH :: rlength, sRDATA :: rdata>
     -> IsPrefix nm qname
      -> matchRR RRecords qtype nm
                 nil [<sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: NS, sRLENGTH :: rlength, sRDATA :: rdata>] nil.

Definition updateresponse (p : packet) answers authority additional :=
  p ○ [o !! "flags" / replace_order o zero_lt_sixteen true;
        (* 0 = query (changed by client); 1 = response (changed by server) *)
        (* set QR bit to true, meaning this is a response *)
        (* do we want an AA (authoritative answer) flag? *)
        "answers" ::= answers; "authority"  ::= authority; "additional" ::= additional ].

Definition DeclarativeDnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" : rep := empty,

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sCOLLECTIONS,

    Def Method1 "Process" (this : rep) (p : packet) : rep * packet :=
        answers <- {answers' | forall answer,
                       List.In answer answers' <->
                       exists answers authority additional,
                         List.In answer answers /\
                         matchRR (GetRelation this Fin.F1)
                                 (p!"questions"!"qtype")
                                 (p!"questions"!"qname")
                                 answers authority additional};
        authority <- {authority' | forall auth,
                           List.In auth authority' <->
                           exists answers authority additional,
                             List.In auth authority /\
                           matchRR (GetRelation this Fin.F1)
                                 (p!"questions"!"qtype")
                                 (p!"questions"!"qname")
                                 answers authority additional};
        additional <- {additional' | forall add,
                          List.In add additional' <->
                          exists answers authority additional,
                            List.In add additional /\
                            matchRR (GetRelation this Fin.F1)
                                    (p!"questions"!"qtype")
                                    (p!"questions"!"qname")
                                    answers authority additional};
        (* Should check to see if everything is empty, in which case set an error. *)
        ret (this, updateresponse p answers authority additional)}%methDefParsing.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" : rep := empty,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sCOLLECTIONS,

    Def Method1 "Process" (this : rep) (p : packet) : rep * packet :=
        Repeat 1 initializing n with p!"questions"!"qname"
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in this!sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsPrefix r!sNAME n) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (is_empty rs)        (* Are there any matching records? *)
            Then ret (buildempty p) (* No matching records! *)
            Else                (* TODO: this does not filter by matching QTYPE *)
              (bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              If b                (* If the record's QNAME is an exact match  *)
              Then
                unique b,                         (* only one match (unique / otherwise) *)
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ p!"questions"!"qtype" <> CNAME ->>      (* and the query did not request a CNAME *)
                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b)               (* ?? Shouldn't this use the sDATA ?? *)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                (* multiple matches -- add them all as answers in the packet *)
                  ret (List.fold_left add_answer bfrs (buildempty p))
              Else              (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records --
                 ask the authoritative servers *) (* TODO does this return one, or return all? *)
                (bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left add_ns bfrs' (buildempty p))))
          }} >>= fun p => ret (this, p)}%methDefParsing.

Local Arguments packet : simpl never.


(* Making fold_list Opaque greatly speeds up setoid_rewriting. *)
Opaque fold_left.
Opaque packet.

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  hone method "Process".
  simpl in *.
  { doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
  }
  drop_constraintsfrom_DNS.
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone method "AddData".
    simplify with monad laws; etransitivity; set_evars.
    doAny simplify_queries
          Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    setoid_rewrite refine_count_constraint_broken.
    repeat doOne srewrite_each_all drills_each_all finish_each_all.
    repeat doOne srewrite_each_all drills_each_all finish_each_all.
    make_simple_indexes ({|prim_fst := [("FindPrefixIndex", Fin.F1)];
                           prim_snd := () |} : prim_prod (list (string * Fin.t 6)) ())
                        ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
                               ltac:(CombineCase5 BuildLastFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + repeat doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
    + repeat doOne implement_insert''
             ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
    +  unfold SearchUpdateTerm in Index; simpl in Index.
       simpl.
Finish_Master ltac:(CombineCase6 BuildEarlyTrieBag  BuildEarlyBag )
                           ltac:(CombineCase5 BuildLastTrieBag BuildLastBag).
Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.

(* TODO extraction, examples/messagesextraction.v *)
