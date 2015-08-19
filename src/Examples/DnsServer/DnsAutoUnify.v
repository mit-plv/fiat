(*Require HintDbTactics.*)          (* plugin to pass a hint db to a tactic *)

Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

                                               (* in start honing querystructure, it inserts constraints before every insert / decision procedure *)
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > () then.. *)
                                               (* For refines decision procedure *)
    update "AddData" (this : rep, t : DNSRRecord) : bool :=
      Insert t into this!sCOLLECTIONS,

    query "Process" (this : rep, p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in this!sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsPrefix r!sNAME n) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
               (* TODO: this does not filter by matching QTYPE *)
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
                (* return all the prefix records that are nameserver records --
                 ask the authoritative servers *) (* TODO does this return one, or return all? *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

<<<<<<< HEAD
(* -------------------------------------------------------------------------------------- *)

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.
  unfold DnsSpec.

  start sharpening ADT. {


 Tactic Notation "hone" "method" constr(methIdx) :=
   let A :=
       match goal with
         |- Sharpened ?A => constr:(A) end in
   let DSig :=
       match goal with
         |- @refineADT ?DSig _ _ => constr:(DSig)
       end in
   let ASig := match type of A with
                 DecoratedADT ?Sig => Sig
               end in
   let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
      match A with
          BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
      match A with
          BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let MethodDomCod' := eval simpl in (MethodDomCod ASig) in
  let methIdxB := eval simpl in
  (ibound (indexb (@Build_BoundedIndex _ _ (Vector.map methID methSigs) methIdx _))) in
      eapply (@SharpenStep_BuildADT_ReplaceMethod_eq
                Rep' _ _ _ _ consDefs methDefs methIdxB
                (@Build_methDef Rep'
                               {| methID := methIdx;
                                  methDom := fst (MethodDomCod' methIdxB);
                                  methCod := snd (MethodDomCod' methIdxB)
                               |}
                               _
                              ));
    [ intros; simpl in *;
      match goal with
        |  |- refine _ (?E ?nr ?d) => is_evar E; let H := fresh in set (H := E)
        | _ => idtac
      end;
      match goal with
        |  |- refine (@absMethod ?oldRep ?newRep ?AbsR ?Dom ?Cod ?oldMethod ?nr ?d)
                     (?H ?nr ?d) => eapply (@refine_AbsMethod oldRep newRep AbsR Dom Cod oldMethod)
        | _ => cbv [absMethod]
      end; intros
    |
    cbv beta in *|-;
    cbv delta [replace_BoundedIndex replace_Index] in *;
    simpl in *
    ].

  hone method "Process". {
    Time doAnyAll.
  (* 241 seconds = 4 minutes *)
  }
=======
Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.

  start sharpening ADT.

  hone method "Process".
  { Time doAnyAll. } (* 241 seconds = 4 minutes *)
>>>>>>> NewUpdateNotation

  start_honing_QueryStructure'.

  hone method "AddData".
<<<<<<< HEAD
  {
    Time doAnyAll.
  (* 202 seconds = 3.5 minutes *)
  }
  (* rename tactic; time the separate ones *)

  eapply reflexivityT.
  }

Ltac finish_planning' matchIndex
     BuildEarlyIndex BuildLastIndex
     IndexUse createEarlyTerm createLastTerm
     IndexUse_dep createEarlyTerm_dep createLastTerm_dep
     BuildEarlyBag BuildLastBag :=
    (* Automatically select indexes + data structure. *)
    eapply FullySharpened_Finish;
    [ eapply reflexivityT
    | GenerateIndexesForAll
        matchIndex
        ltac:(fun attrlist => make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex;
              match goal with
              | |- FullySharpenedUnderDelegates _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
              | |- _ => (* Otherwise implement each method using the indexed data structure *)
                plan IndexUse createEarlyTerm createLastTerm
                     IndexUse_dep createEarlyTerm_dep createLastTerm_dep
              end;
              pose_headings_all;
              match goal with
              | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
                FullySharpenQueryStructure Schema Indexes
              end
             )
  | simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;

    BuildQSIndexedBags' BuildEarlyBag BuildLastBag
  | cbv zeta; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    simpl Sharpened_Implementation;
    unfold
      Update_Build_IndexedQueryStructure_Impl_cRep,
    Join_Comp_Lists',
    GetIndexedQueryStructureRelation,
    GetAttributeRaw; simpl;
    higher_order_reflexivityT ].

  Ltac finish_planning IndexTactics := IndexTactics finish_planning'.

  Require Import Fiat.QueryStructure.Automation.MasterPlan.

  Unset Ltac Debug.
    eapply FullySharpened_Finish;
    [ eapply reflexivityT
    | | | ].

    (*finish_planning ltac:(CombineIndexTactics ltac:(PrefixIndexTactics) ltac:(EqIndexTactics)). *)

    Set Ltac Debug.
    GenerateIndexesForAll         (* ? in IndexSelection, see GenerateIndexesFor *)
  (* specifies that you want to use the suffix index structure TODO *)
  ltac:(CombineCase3 matchFindPrefixIndex matchEqIndex)
         ltac:(fun attrlist => pose attrlist).
  make_simple_indexes
    attrlist
    ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
           ltac:(CombineCase5 BuildLastFindSuffixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex));
               match goal with
               | |- FullySharpenedUnderDelegates _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
               | |- _ => (* Otherwise implement each method using the indexed data structure *)
                 try plan ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                                 ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                                        ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                                               ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                                                      ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                                             ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep)
               end).

  pose_headings_all;
  FullySharpenQueryStructure DnsSchema Index.


  finish_planning ltac:(CombineIndexTactics ltac:(PrefixIndexTactics) ltac:(EqIndexTactics)).


  GenerateIndexesForAll         (* ? in IndexSelection, see GenerateIndexesFor *)
  (* specifies that you want to use the suffix index structure TODO *)
  ltac:(CombineCase3 matchFindPrefixIndex matchEqIndex)
         ltac:(fun attrlist =>
  make_simple_indexes
    attrlist
    ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
           ltac:(CombineCase5 BuildLastFindSuffixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex));
               match goal with
               | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
               | |- _ => (* Otherwise implement each method using the indexed data structure *)
                 try plan ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                                 ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                                        ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                                               ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                                                      ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                                             ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep)
               end).

  pose_headings_all;
  FullySharpenQueryStructure DnsSchema Index.
}                               (* ending "start sharpening ADT" *)

{ simpl; pose_string_ids; pose_headings_all;
  pose_search_term;  pose_SearchUpdateTerms.
  unfold name in *.
  BuildQSIndexedBags'
  ltac:(CombineCase6 BuildEarlyTrieBag BuildEarlyEqualityBag)
         ltac:(CombineCase5 BuildLastTrieBag BuildLastEqualityBag). }

{ cbv zeta; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    simpl Sharpened_Implementation;
    unfold
      Update_Build_IndexedQueryStructure_Impl_cRep,
    Join_Comp_Lists',
    GetIndexedQueryStructureRelation,
    GetAttributeRaw; simpl;
    higher_order_reflexivityT. }
=======
  { Time doAnyAll. } (* 202 seconds = 3.5 minutes *)

  finish_planning ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics)
  ltac:(fun make_index =>
          make_index ({| prim_fst := [("FindPrefixIndex", Fin.F1)]; prim_snd := () |}
                                                : @ilist3 RawHeading
                                  (fun heading : RawHeading => list (prod string (Attributes heading)))
                                  (numRawQSschemaSchemas (QueryStructureSchemaRaw DnsSchema))
                                  (Vector.map rawSchemaHeading (qschemaSchemas DnsSchema)))).
>>>>>>> NewUpdateNotation

Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.

(* TODO extraction, examples/messagesextraction.v *)
