Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List.

Require Import
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation.Decidable
        Fiat.Computation.IfDec
        Fiat.Computation.FoldComp
        Fiat.Computation.FueledFix
        Fiat.Computation.ListComputations
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation
        Fiat.Examples.DnsServer.AuthoritativeDNSSchema
        Fiat.BinEncoders.Env.Examples.Dns2.
Require Import
        Bedrock.Word
        Fiat.BinEncoders.Env.Common.Specs.

Section BinaryDns.

  Definition bin := list bool.

  Variable cache : Cache.
  Variable cacheAddNat : CacheAdd cache nat.
  Variable cacheEmpty : CacheEncode.

  Variable transformer : Transformer bin.
  Variable transformerUnit : TransformerUnit transformer bool.
  
  Definition encoder x := (x -> CacheEncode -> bin * CacheEncode).
  Definition  decoder x := (bin -> CacheDecode -> x * bin * CacheDecode).
  Variable encode_enum :
    forall (sz : nat) (A B : Type) (ta : t A sz) (tb : t B sz),
      encoder B -> encoder (BoundedIndex ta).

  Variable QType_Ws : Vector.t (word 16) 66.
  Variable QClass_Ws : t (word 16) 4.
  Variable RRecordType_Ws : t (word 16) 59.
  Variable RRecordClass_Ws : t (word 16) 3.
  Variable Opcode_Ws : t (word 4) 4.
  Variable RCODE_Ws : t (word 4) 12.

  Variable recurseDepth : nat.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * bin -> rep * bin
    }.

Definition encode_packet' b :=
  @encode_packet bin cache cacheAddNat transformer transformerUnit
                encode_enum QType_Ws QClass_Ws RRecordType_Ws
                RRecordClass_Ws Opcode_Ws RCODE_Ws b cacheEmpty.

Definition DnsSpec : ADT DnsSig :=
  Def ADT {
    rep := QueryStructure DnsSchema,

    Def Constructor "Init" : rep := empty,,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sRRecords,

    Def Method1 "Process" (this : rep) (b : bin) : rep * bin :=
        p <- {p | fst (encode_packet' p) = b};
        Repeat recurseDepth initializing n with p!"questions"!"qname"
               defaulting rec with (ret (buildempty true ``"ServFail" p)) (* Bottoming out w/o an answer signifies a server failure error. *)
        {{ results <- MaxElements (fun r r' : resourceRecord => IsPrefix r!sNAME r'!sNAME)
                             (For (r in this!sRRecords)      (* Bind a list of all the DNS entries *)
                               Where (IsPrefix r!sNAME n)   (* prefixed with [n] to [rs] *)
                               Return r);
            If (is_empty results) (* Are there any matching records? *)
            Then ret (buildempty true ``"NXDomain" p) (* No matching records, set name error *)
            Else
            (IfDec (List.Forall (fun r : resourceRecord => n = r!sNAME) results) (* If the record's QNAME is an exact match  *)
              Then
              b <- SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                                   List.In (A := resourceRecord) b results
                                   /\ p!"questions"!"qtype" <> QType_inj CNAME); (* and a non-CNAME was requested*)
                Ifopt b as b'
                Then  (* only one matching CNAME record *)
                  p' <- rec b'!sRDATA; (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b') (* Add the CNAME RR to the answer section *)
                Else     (* Copy the records with the correct QTYPE into the answer *)
                         (* section of an empty response *)
                (results <- ⟦ element in results | QType_match (element!sTYPE) (p!"questions"!"qtype") ⟧;
                  ret (add_answers results (buildempty true ``"NoError" p)))
              Else (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records -- *)
                (* ask the authoritative servers *)
              (ns_results <- { ns_results | forall x : NS_Record, List.In x ns_results <-> List.In (A := resourceRecord) x results };
                 (* Append all the glue records to the additional section. *)
                 glue_results <- For (rRec in this!sRRecords)
                                 Where (List.In rRec!sNAME (map (fun r : NS_Record => r!sRDATA) ns_results))
                                 Return rRec;
                 ret (add_additionals glue_results (add_nses (map VariantResourceRecord2RRecord ns_results) (buildempty true ``"NoError" p)))))
          }} >>= fun p => ret (this, fst (encode_packet' p))}.

End BinaryDns.

(*
Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * packet -> rep * packet
    }.


Definition DnsSpec (recurseDepth : nat) : ADT DnsSig :=
  Def ADT {
    rep := QueryStructure DnsSchema,

    Def Constructor "Init" : rep := empty,,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sRRecords,

    Def Method1 "Process" (this : rep) (p : packet) : rep * packet :=
        Repeat recurseDepth initializing n with p!"questions"!"qname"
               defaulting rec with (ret (buildempty true ``"ServFail" p)) (* Bottoming out w/o an answer signifies a server failure error. *)
        {{ results <- MaxElements (fun r r' : resourceRecord => IsPrefix r!sNAME r'!sNAME)
                             (For (r in this!sRRecords)      (* Bind a list of all the DNS entries *)
                               Where (IsPrefix r!sNAME n)   (* prefixed with [n] to [rs] *)
                               Return r);
            If (is_empty results) (* Are there any matching records? *)
            Then ret (buildempty true ``"NXDomain" p) (* No matching records, set name error *)
            Else
            (IfDec (Forall (fun r : resourceRecord => n = r!sNAME) results) (* If the record's QNAME is an exact match  *)
              Then
              b <- SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                                   List.In (A := resourceRecord) b results
                                   /\ p!"questions"!"qtype" <> QType_inj CNAME); (* and a non-CNAME was requested*)
                Ifopt b as b'
                Then  (* only one matching CNAME record *)
                  p' <- rec b'!sRDATA; (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b') (* Add the CNAME RR to the answer section *)
                Else     (* Copy the records with the correct QTYPE into the answer *)
                         (* section of an empty response *)
                (results <- ⟦ element in results | QType_match (element!sTYPE) (p!"questions"!"qtype") ⟧;
                  ret (add_answers results (buildempty true ``"NoError" p)))
              Else (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records -- *)
                (* ask the authoritative servers *)
              (ns_results <- { ns_results | forall x : NS_Record, List.In x ns_results <-> List.In (A := resourceRecord) x results };
                 (* Append all the glue records to the additional section. *)
                 glue_results <- For (rRec in this!sRRecords)
                                 Where (List.In rRec!sNAME (map (fun r : NS_Record => r!sRDATA) ns_results))
                                 Return rRec;
                 ret (add_additionals glue_results (add_nses (map VariantResourceRecord2RRecord ns_results) (buildempty true ``"NoError" p)))))
          }} >>= fun p => ret (this, p)}. *)

Local Arguments packet : simpl never.

(* Making fold_list Opaque greatly speeds up setoid_rewriting. *)
Opaque fold_left.

(* Need to update derivation to work with arbitrary recursion depth. *)

(*Theorem DnsManual (recurseDepth : nat) :
  FullySharpened (DnsSpec recurseDepth).
Proof.
  start sharpening ADT; unfold DnsSpec.
  simpl; pose_string_hyps; pose_heading_hyps.
  hone method "Process".
  simpl in *.
  { simplify with monad laws.

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
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
  }
  drop_constraintsfrom_DNS.
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
        doOne drop_constraints
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
    + doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).


      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      Focused_refine_TopMost_Query.
      implement_In_opt.
      repeat progress distribute_filters_to_joins.
      implement_filters_with_find
        ltac:(find_simple_search_term ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                      ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                             ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm))
               ltac:(find_simple_search_term_dep
                       ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                              ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                     ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep)).



      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      implement_In_opt.
      repeat progress distribute_filters_to_joins.
      setoid_rewrite
      match goal with
  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (refine_Filtered_Query_In_Enumerate H (idx := idx) f) in
            apply H'
      | apply refine_under_bind; intros; implement_In_opt' ]

  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (List_Query_In ?b (fun b : ?QueryT => Where (@?P b) (@?resultComp b))) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (@refine_List_Query_In_Where QueryT _ b P resultComp _) in
            apply H'
      | implement_In_opt'; implement_In_opt' ] end.


    +  unfold SearchUpdateTerm in Index; simpl in Index.
       simpl.
Finish_Master ltac:(CombineCase6 BuildEarlyTrieBag  BuildEarlyBag )
                           ltac:(CombineCase5 BuildLastTrieBag BuildLastBag).
Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl. *)

(* TODO extraction, examples/messagesextraction.v *)
