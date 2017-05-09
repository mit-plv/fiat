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
        Fiat.QueryStructure.Automation.SearchTerms.FindStringPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import
        Bedrock.Word
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Examples.DnsOpt
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt.

Require Import Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.DecomposeSumField
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation
        Fiat.Examples.DnsServer.AuthoritativeDNSSchema.


Section BinaryDns.

  Variable recurseDepth : nat.

  Definition DnsSig : ADTSig :=
    ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * ByteString -> rep * (option ByteString)
    }.

Definition DnsSpec : ADT DnsSig :=
  Def ADT {
    rep := QueryStructure DnsSchema,

    Def Constructor "Init" : rep := empty,,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sRRecords,

    Def Method1 "Process" (this : rep) (b : ByteString) : rep * (option ByteString) :=
        p' <- Pick_Decoder_For DNS_Packet_OK encode_packet_Spec b list_CacheEncode_empty;
       Ifopt p' as p Then
        p' <- Repeat recurseDepth initializing n with p!"question"!"qname"
               defaulting rec with (ret (buildempty true ``"ServFail" p)) (* Bottoming out w/o an answer signifies a server failure error. *)
        {{ results <- MaxElements (fun r r' : resourceRecord => prefix r!sNAME r'!sNAME)
                             (For (r in this!sRRecords)      (* Bind a list of all the DNS entries *)
                               Where (prefix r!sNAME n)   (* prefixed with [n] to [rs] *)
                               Return r);
            If (is_empty results) (* Are there any matching records? *)
            Then ret (buildempty true ``"NXDomain" p) (* No matching records, set name error *)
            Else
            (IfDec (List.Forall (fun r : resourceRecord => r!sNAME = n) results) (* If the record's QNAME is an exact match  *)
              Then
              b <- SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                                   List.In (A := resourceRecord) b results
                                   /\ p!"question"!"qtype" <> QType_inj CNAME); (* and a non-CNAME was requested*)
                Ifopt b as b'
                Then  (* only one matching CNAME record *)
                  p' <- rec b'!sRDATA; (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b') (* Add the CNAME RR to the answer section *)
                Else     (* Copy the records with the correct QTYPE into the answer *)
                         (* section of an empty response *)
                (results <- ⟦ element in results | QType_match (RDataTypeToRRecordType element!sRDATA) (p!"question"!"qtype") ⟧;
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
        }};
       b' <- encode_packet_Spec p' list_CacheEncode_empty;
       ret (this, Some (fst b'))
           Else ret (this, None)
           }.

Ltac implement_insert'' :=
  implement_insert' ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
         ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
         ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm)
         ltac:(CombineCase7 StringPrefixIndexUse_dep EqIndexUse_dep)
         ltac:(CombineCase11 createEarlyStringPrefixTerm_dep createEarlyEqualityTerm_dep)
         ltac:(CombineCase8 createLastStringPrefixTerm_dep createLastEqualityTerm_dep).

Lemma refine_MaxElements A op
  : forall (ca ca' : Comp (list A)),
    refine ca ca'
    -> refine (MaxElements op ca) (MaxElements op ca').
Proof.
  simpl; intros.
  unfold MaxElements, refine; simpl in *; intros.
  rewrite H; assumption.
Qed.

    Lemma refine_Singleton_Set
      : forall (r_o : QueryStructure DnsSchema) q bound l,
        MaxElements (fun r r' : resourceRecord => prefix (GetAttributeRaw r Fin.F1) (GetAttributeRaw r' Fin.F1))
         For (Query_In r_o Fin.F1 (fun r : RawTuple => Where (prefix (GetAttributeRaw r Fin.F1) bound)
                                   Return r )) ↝ l
        -> Forall (fun r : resourceRecord => GetAttributeRaw r Fin.F1 = bound) l
        -> refine
             (SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                                   List.In (A := resourceRecord) b l
                                   /\ q <> QType_inj CNAME))
                          (SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                                   List.In (A := resourceRecord) b l
                                   /\ q <> QType_inj CNAME)).



Ltac drop_constraints :=
  first
    [ simplify with monad laws
    | drop_constraints_from_query'
    | rewrite refine_If_Then_Else_Bind
    | rewrite refine_If_Opt_Then_Else_Bind
    | rewrite refine_if_Then_Else_Duplicate
    | apply refine_MaxElements
    | eapply refineFueledFix; [
      | let refine_bid := fresh in
        intros ? ? ? refine_bod; repeat setoid_rewrite refine_bod ]
    | implement_DropQSConstraints_AbsR ].

Local Opaque MaxElements.
Local Opaque encode_packet_Spec.
Local Opaque SumType.SumType_index.
Local Opaque SumType.SumType_proj.
Local Opaque SumType.inj_SumType.

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.
  start sharpening ADT; unfold DnsSpec.
  pose_string_hyps; pose_heading_hyps.
  drop_constraintsfrom_DNS.
  { (* Add Data. *)
    match goal with
      H : DropQSConstraints_AbsR ?r_o ?r_n
      |- refine (u <- QSInsert ?r_o ?Ridx ?tup;
                 @?k u) _ =>
      eapply (@QSInsertSpec_refine_subgoals _ _ r_o r_n Ridx tup); try exact H
    end; try set_refine_evar.
    - rewrite decides_True; finish honing.
    - simpl; rewrite refine_noDup_CNAME_check_dns by eauto; finish honing.
    - simpl; set_evars; intros; setoid_rewrite refine_count_constraint_broken'; finish honing.
    - simpl; finish honing.
    - simpl; intros; finish honing.
    - intros. refine pick val _; eauto; simplify with monad laws.
      simpl; finish honing.
    - intros. refine pick val _; eauto; simplify with monad laws.
      simpl; finish honing.
  }
  { (* Process *)
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    rewrite refine_if_If.
    match goal with
      |- refine (If_Then_Else ?c _ _) _ =>
      subst_refine_evar; eapply refine_if with (b := c);
        let H := fresh in
        intro H; set_refine_evar; try rewrite H; simpl
    end.
    rewrite H4 in H3.
    computes_to_inv; simpl in H3.


    unfold SingletonSet.

    subst.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    unfold SingletonSet.


    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    (* 51s with apply decomposition lemmas.*)
    (* 73s with rewrite decomposition lemmas.*)
  }
  simpl.
  hone representation using (@DecomposeRawQueryStructureSchema_AbsR
                               _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) _
                               (SumType.SumType_index ResourceRecordTypeTypes)
                               (SumType.SumType_proj ResourceRecordTypeTypes)
                               (SumType.inj_SumType ResourceRecordTypeTypes)
                            ).
  { simplify with monad laws.
    refine pick val _.
    2: apply DecomposeRawQueryStructureSchema_empty_AbsR.
    finish honing.
  }
  { simplify with monad laws.
    drop_constraints_drill.
    rewrite (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0 Fin.F1).
    finish honing.
    drop_constraints.
    drop_constraints_drill.
    drop_constraints.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite refine_Iterate_Equiv_QueryResultComp; try eassumption.
    (* simpl; unfold Tuple_DecomposeRawQueryStructure_inj; simpl. *)
    finish honing.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
    unfold GetAttribute, GetAttributeRaw at 2; simpl.
    unfold ilist2_hd; simpl.
    finish honing.
    rewrite !refine_if_If.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    apply (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ eassumption | intros; set_refine_evar].
    refine pick val _; try eassumption.
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
    unfold GetAttribute, GetAttributeRaw at 2; simpl.
    unfold ilist2_hd; simpl.
    finish honing.
    rewrite refine_if_If.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    apply (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ eassumption | intros; set_refine_evar].
    refine pick val _; try eassumption.
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }
  { doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    rewrite (@MaxElementsUnConstrQuery_In DnsSchema Fin.F1 (fun r : resourceRecord => GetAttributeRaw r Fin.F1) a1 r_o).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    apply refine_under_bind_both; intros; set_refine_evar.
    rewrite (refine_Iterate_Equiv_QueryResultComp _ H0).
    finish honing.
    rewrite refine_If_Then_Else_Bind.
    match goal with
      |- refine (If_Then_Else ?c _ _) _ =>
      subst_refine_evar; eapply refine_if with (b := c);
        let H := fresh in
        intro H; set_refine_evar; try rewrite H; simpl
    end.
    { doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      rewrite refine_If_Then_Else_false.
      refine pick val true.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      simpl.
      finish honing.
      simpl; apply (For_UnConstrQuery_In_Where_Prop _ H2).
      rewrite <- negb_false_iff, <- negb_involutive_reverse in H3.
      apply H3.
    }
    { unfold H4.
      etransitivity.
      eapply refine_under_bind_both_ambivalent with
      (c' := MaxElements (fun r r' : @RawTuple {| NumAttr := 4; AttrList := [DomainName : Type ; timeT : Type; RRecordClass : Type; RDataType : Type]%NamedSchema |} => prefix (GetAttributeRaw r Fin.F1) (GetAttributeRaw r' Fin.F1))
              For (UnConstrQuery_In r_o Fin.F1
                     (fun r : RawTuple =>
                        Where (
                            RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) = NS
                            /\ prefix (GetAttributeRaw r Fin.F1) a1
                            /\ GetAttributeRaw r Fin.F1 <> a1)
                      Return r ))).
        intros.
        eexists a'; split.
        clear; admit.
        match goal with
          |- refine (If_Then_Else ?c _ _) _ =>
          subst_refine_evar; eapply refine_if with (b := c);
            let H := fresh in
            intro H; set_refine_evar; try rewrite H; simpl
        end.
        finish honing.
        refine pick val false; simpl.
        doOne ltac:(drop_constraints)
                     drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
        simpl.
        doOne ltac:(drop_constraints)
                     drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      rewrite (refine_Iterate_Equiv_QueryResultComp _ H0).
      finish honing.
      finish honing.
      rewrite Forall_forall.
      intro.
      clear; admit.
      cbv beta.
      etransitivity.
      apply refine_under_bind_both.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      rewrite (refine_QueryIn_Where _ _ H0).
      unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
      unfold GetAttribute, GetAttributeRaw; simpl.
      unfold ilist2_hd; simpl.
      finish honing.
      intros; finish honing.
      cbv beta.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      finish honing.
    }
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }
  cbv beta.
  drop_constraints_drill.
      finish honing.
      drop_constraints_drill.
      finish honing.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      finish honing.
      finish honing.
      finish honing.
      setoid_rewrite H2.
      simpl; finish honing.
    - Local Opaque encode_packet_Spec.
      doAny ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    - doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)

                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }
  Local Opaque SumType.SumType_index.
  Local Opaque SumType.SumType_proj.
  Local Opaque SumType.inj_SumType.

  hone representation using (@DecomposeRawQueryStructureSchema_AbsR
                               _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) _
                               (SumType.SumType_index ResourceRecordTypeTypes)
                               (SumType.SumType_proj ResourceRecordTypeTypes)
                               (SumType.inj_SumType ResourceRecordTypeTypes)
                            ).
  { simplify with monad laws.
    refine pick val _.
    2: apply DecomposeRawQueryStructureSchema_empty_AbsR.
    finish honing.
  }
  {
    simplify with monad laws.
    drop_constraints_drill.
    rewrite (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0 Fin.F1).
    finish honing.
    drop_constraints_drill.
    drop_constraints_drill.
    setoid_rewrite refine_Iterate_Equiv_QueryResultComp; try eassumption.
    (* simpl; unfold Tuple_DecomposeRawQueryStructure_inj; simpl. *)
    finish honing.
    finish honing.
    drop_constraints_drill.
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simpl.
    unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
    unfold GetAttribute, GetAttributeRaw at 2; simpl.
    unfold ilist2_hd; simpl.
    finish honing.
    rewrite !refine_if_If.
    rewrite !refine_If_Then_Else_Bind.
    drop_constraints_drill.
    drop_constraints_drill.
    simplify with monad laws.
    apply (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0).
    eapply refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv'; eauto.
    intros.
    refine pick val _; try eassumption.
    simplify with monad laws; simpl; finish honing.
    simplify with monad laws; refine pick val _; try eassumption.
    simplify with monad laws; simpl; finish honing.
    simplify with monad laws; refine pick val _; try eassumption.
    simplify with monad laws; simpl; finish honing.
  }
  { simplify with monad laws.
    drop_constraints_drill.
    finish honing.
    rewrite !refine_If_Opt_Then_Else_Bind.
    drop_constraints_drill.
    simplify with monad laws.
    drop_constraints_drill.
    eapply refineFueledFix.
    finish honing.
    intros.
    rewrite (refine_Iterate_Equiv_QueryResultComp _ H0).
    drop_constraints_drill.
    finish honing.
    drop_constraints_drill.
    setoid_rewrite H2.
    finish honing.
    simplify with monad laws.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    drop_constraints_drill.
    simpl.
    unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
    unfold GetAttribute, GetAttributeRaw; simpl.
    unfold ilist2_hd; simpl.
    finish honing.
    drop_constraints_drill.
    finish honing.
    drop_constraints_drill.
    finish honing.
    drop_constraints_drill.
    finish honing.
    rewrite (refine_Iterate_Equiv_QueryResultComp _ H0).
    finish honing.
    drop_constraints_drill.
    finish honing.
    simpl; refine pick val _; try eassumption.
    simplify with monad laws.
    finish honing.
    simplify with monad laws.
    simpl; refine pick val _; try eassumption.
    simplify with monad laws.
    finish honing.
  }
  simpl.



  make_simple_indexes ({|prim_fst := [(FindStringPrefixIndex, @Fin.F1 4)];
                         prim_snd := () |} : prim_prod (list (string * Fin.t 5)) ())
  ltac:(CombineCase6 BuildEarlyFindStringPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
         ltac:(CombineCase5 BuildLastStringFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)).
  { (* Constructor *)
    plan ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
         ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
         ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm)
         ltac:(CombineCase7 StringPrefixIndexUse_dep EqIndexUse_dep)
         ltac:(CombineCase11 createEarlyStringPrefixTerm_dep createEarlyEqualityTerm_dep)
         ltac:(CombineCase8 createLastStringPrefixTerm_dep createLastEqualityTerm_dep).
  }
  { (* Add Data *)
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doAny implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doAny implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doAny implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
  }
  doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
      set_evars) ltac:(finish honing).
    eapply refineFueledFix.
    finish honing.
    intros.
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    implement_insert''.
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doAny implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).

        doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    rewrite H2.

    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).

        doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    Focused_refine_TopMost_Query.
    set_refine_evar.
    etransitivity.
    match goal with
      | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (refine_Filtered_Query_In_Enumerate H (idx := idx) f) in
            apply H'
      | apply refine_under_bind; intros]
    end.
    match goal with
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (List_Query_In ?b (fun b : ?QueryT => Where (@?P b) (@?resultComp b))) _ ] =>
      etransitivity;
        [ let H' := eval simpl in (@refine_List_Query_In_Where QueryT _ b P resultComp) in
              pose proof H' | ]
    end.
    simpl in H10.
    Check (H10 _). P_dec : DecideableEnsemble
                    (fun
                       tup : ilist2
                               [{| NumAttr := 5; AttrList := [DomainName; timeT; RRecordClass; RRecordType; RDataType] |}]%NamedSchema =>
                     List.In (GetAttributeRaw (ilist2_hd tup) Fin.F1)
                       (map (fun r : NS_Record => GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) a5))


    etransitivity.
    let H' := eval simpl in (refine_Filtered_Query_In_Enumerate H (idx := idx) f) in
        apply H'
      | apply refine_under_bind; intros; implement_In_opt' ]

    implement_In_opt.
    repeat progress distribute_filters_to_joins.
    (* Step 3: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep
  |
  ]; pose_string_hyps; pose_heading_hyps.
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).

        doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).

        doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    doOne implement_insert''
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).



  { (* Add Data. *)
  plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
       EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.


  simpl.
  (* All constraints dropped. *)
    progress doOne srewrite_each_all drills_each_all finish_each_all.
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
Time Defined. *)

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
        Repeat recurseDepth initializing n with p!"question"!"qname"
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
                                   /\ p!"question"!"qtype" <> QType_inj CNAME); (* and a non-CNAME was requested*)
                Ifopt b as b'
                Then  (* only one matching CNAME record *)
                  p' <- rec b'!sRDATA; (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b') (* Add the CNAME RR to the answer section *)
                Else     (* Copy the records with the correct QTYPE into the answer *)
                         (* section of an empty response *)
                (results <- ⟦ element in results | QType_match (element!sTYPE) (p!"question"!"qtype") ⟧;
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
