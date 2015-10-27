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

Ltac hone_Dns :=
  start sharpening ADT;

  hone method "Process"; [ doAnyAll | ]; (* 241 seconds = 4 minutes *)
  start_honing_QueryStructure';
  hone method "AddData"; [ doAnyAll | ]; (* 202 seconds = 3.5 minutes *)
  finish_planning ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics)
                         ltac:(fun makeIndex =>
                                 GenerateIndexesForOne "Process" ltac:(fun attrlist =>
                                                                         let attrlist' := eval compute in (PickIndexes (CountAttributes' attrlist)) in makeIndex attrlist')).

(* Making fold_list Opaque greatly speeds up setoid_rewriting. *)
Opaque fold_left.

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  hone method "Process".
  { (* Stepping through doAnyAll. Uncomment the below line and *)
    (* comment the up until start_honing_QueryStructure' to see the *)
    (* automated tactic work it's magic. *)
    (* Time doAnyAll. *)
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      repeat_and_simplify finish_each_all. }
    { repeat_and_simplify srewrite_each_all.
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify srewrite_each_all.
        do_and_simplify drills_each_all.
        { repeat_and_simplify srewrite_each_all.
          do_and_simplify drills_each_all.
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
        }
        { repeat_and_simplify srewrite_each_all.
          repeat_and_simplify finish_each_all. }
      }
      repeat_and_simplify finish_each_all.
      repeat_and_simplify finish_each_all.
      repeat_and_simplify finish_each_all.
    }
  }
  start_honing_QueryStructure'.
  hone method "AddData".
  { (* Stepping through doAnyAll. Uncomment the below line and *)
    (* comment the up until start_honing_QueryStructure' to see the *)
    (* automated tactic work it's magic. *)
    (* Time doAnyAll. *)
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      repeat_and_simplify finish_each_all. }
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify rewrite_each_all.
        repeat_and_simplify finish_each_all. } }
    do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      do_and_simplify drills_each_all.
      { repeat_and_simplify rewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify rewrite_each_all.
        repeat_and_simplify finish_each_all. } }
  simpl.
  (* Still need to update master_plan with some search instances. *)
  master_plan ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics).

Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.

(* TODO extraction, examples/messagesextraction.v *)
