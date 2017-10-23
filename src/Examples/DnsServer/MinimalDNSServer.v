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
        Fiat.BinEncoders.Env.Examples.SimpleDnsOpt
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt.

Require Import Fiat.Examples.DnsServer.SimplePacket
        Fiat.Examples.DnsServer.DecomposeSumField
        Fiat.Examples.DnsServer.SimpleDnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation
        Fiat.Examples.DnsServer.SimpleAuthoritativeDNSSchema.

  (* This "unresponsive" variant of an authoritative DNS Server responds*)
   (* by simply flipping the response bit in the packet without adding any *)
  (* records. It is intended as an initial example for Bedrock compilation. *)

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
        p <- Pick_Decoder_For DNS_Packet_OK
              encode_packet_Spec b list_CacheEncode_empty;
       Ifopt p as p' Then
         p' <- ret (buildempty true ``"NoError" p');
         b' <- encode_packet_Spec p' list_CacheEncode_empty;
         ret (this, Some (fst b'))
       Else (* Not sure what to do in this case, will return None to *)
            (* the shim *)
       ret (this, None)
      }.

Local Opaque encode_packet_Spec.
Local Opaque packetDecoderImpl.

Local Opaque MaxElements.
Local Opaque encode_packet_Spec.
Local Opaque SumType.SumType_index.
Local Opaque SumType.SumType_proj.
Local Opaque SumType.inj_SumType.

Ltac implement_insert'' :=
  implement_insert' ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
         ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
         ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm)
         ltac:(CombineCase7 StringPrefixIndexUse_dep EqIndexUse_dep)
         ltac:(CombineCase11 createEarlyStringPrefixTerm_dep createEarlyEqualityTerm_dep)
         ltac:(CombineCase8 createLastStringPrefixTerm_dep createLastEqualityTerm_dep).

Ltac drop_constraints :=
  first
    [ simplify with monad laws
    | drop_constraints_from_query'
    | rewrite refine_If_Then_Else_Bind
    | rewrite refine_If_Opt_Then_Else_Bind
    | rewrite refine_if_Then_Else_Duplicate
    | apply refine_MaxElements'
    | eapply refineFueledFix; [
      | let refine_bid := fresh in
        intros ? ? ? refine_bod; repeat setoid_rewrite refine_bod ]
    | implement_DropQSConstraints_AbsR ].


Instance ADomainName_eq : Query_eq DomainName := Astring_eq.
Instance ARRecordType_eq : Query_eq RRecordType :=
  {| A_eq_dec := fin_eq_dec |}.

Lemma refine_decode_packet
  : forall b,
    refine (Pick_Decoder_For DNS_Packet_OK encode_packet_Spec b list_CacheEncode_empty)
           (ret match fst packetDecoderImpl b list_CacheDecode_empty
                with
                | Some (p, _, _) => Some p
                | None => None
                end).
Proof.
  intros; eapply refine_Pick_Decoder_For with (decoderImpl := packet_decoder); eauto.
  apply list_cache_empty_Equiv.
  simpl.
  unfold GoodCache; simpl; intuition; congruence.
Qed.

Local Opaque CallBagFind.

Theorem DnsManual :
  {DnsImpl : _ & refineADT DnsSpec DnsImpl}.
Proof.
  eexists; unfold DnsSpec.
  pose_string_hyps; pose_heading_hyps.
  drop_constraintsfrom_DNS.
  { (* Add Data. *)
    etransitivity.
    match goal with
      H : DropQSConstraints_AbsR ?r_o ?r_n
      |- refine (u <- QSInsert ?r_o ?Ridx ?tup;
                 @?k u) _ =>
      eapply (@QSInsertSpec_refine_subgoals_short_circuit _ _ r_o r_n Ridx tup); try exact H
    end; try set_refine_evar.
    - rewrite decides_True; finish honing.
    - simpl.
      rewrite refine_decides_forall_and;
        [
        | let a := fresh in
          intro a; split; [let H' := fresh in intros H'; pattern (indexedElement a); exact H' | intuition]
        | let a := fresh in
          intro a; split; [let H' := fresh in intros H'; pattern (indexedElement a); exact H' | intuition] ].
      rewrite refine_noDup_CNAME_check_dns by eauto.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      match goal with
      |- refine (If_Then_Else ?c _ _) _ =>
      subst_refine_evar; eapply refine_if with (b := c);
        let H := fresh in
        intro H; set_refine_evar; try rewrite H; simpl
    end.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      rewrite refine_no_usurp_authority_check by eauto.
      erewrite beq_RRecordType_trans by eauto.
      simpl.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      rewrite refine_no_usurp_authority_check_dns by eauto.
      repeat doOne ltac:(drop_constraints)
                          drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    - simpl; set_evars; intros.
      rewrite refine_decides_forall_and;
        [
        | let a := fresh in
          intro a; split; [let H' := fresh in intros H'; pattern (indexedElement a); exact H' | intuition]
        | let a := fresh in
          intro a; split; [let H' := fresh in intros H'; pattern (indexedElement a); exact H' | intuition] ].
      setoid_rewrite refine_count_constraint_broken'.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      rewrite refine_no_usurp_authority_check'_dns by eauto.
      repeat doOne ltac:(drop_constraints)
                          drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      repeat doOne ltac:(drop_constraints)
                          drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    - simpl; finish honing.
    - simpl; intros; finish honing.
    - intros. refine pick val _; eauto; simplify with monad laws.
      simpl; finish honing.
    - intros. refine pick val _; eauto; simplify with monad laws.
      simpl; finish honing.
    - simpl.
      repeat first [ progress simpl
                   | setoid_rewrite refine_bind_unit
                   | setoid_rewrite refine_bind_bind
                   | setoid_rewrite refine_If_Then_Else_Bind].
      finish honing.
  }
  { (* Process *)
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }

  simpl.
  assert (forall (r : UnConstrQueryStructure
                        (DecomposeRawQueryStructureSchema DnsSchema Fin.F1
                                                          (Fin.FS (Fin.FS (Fin.FS Fin.F1))) ResourceRecordTypeTypes)), True).
  unfold DecomposeRawQueryStructureSchema, DecomposeSchema in *; simpl in *.
  pose_heading_hyps; auto.
  clear H.
  hone representation using (fun r_o (r_n : UnConstrQueryStructure qs_schema) =>
                               exists r_n',
                               @DecomposeRawQueryStructureSchema_AbsR
                                 _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) _
                                 (SumType.SumType_index ResourceRecordTypeTypes)
                                 (SumType.SumType_proj ResourceRecordTypeTypes)
                                 (SumType.inj_SumType ResourceRecordTypeTypes)
                                 r_o (r_n', r_n)).
  { simplify with monad laws.
    refine pick val _.
    2: eexists _; apply (@DecomposeRawQueryStructureSchema_empty_AbsR _ DnsSchema).
    finish honing.
  }
  { destruct_ex; simplify with monad laws.
    simpl.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    rewrite (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0).
    simpl; finish honing.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    rewrite (refine_Iterate_Count_For_UnConstrQuery_In _ H0).
    unfold Iterate_Equiv_Count_For_UnConstrQuery_In_body; simpl.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
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
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simplify_GetAttributeRaw_inj.
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
    simpl.
    erewrite (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ | eassumption | intros; set_refine_evar; refine pick val (snd r_n'); destruct r_n';
                        try eauto;
                        simplify with monad laws; simpl; try finish honing;
                        unfold H8; instantiate (1 := fun z => ret (snd z, true)); reflexivity].
    simpl.
    Local Transparent UpdateUnConstrRelationInsertC.
    unfold UpdateUnConstrRelationInsertC at 1.
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
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simplify_GetAttributeRaw_inj.
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
    erewrite (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ | eassumption | intros; set_refine_evar; refine pick val (snd r_n'); destruct r_n';
                        try eauto;
                        simplify with monad laws; simpl; try finish honing;
                        unfold H9; instantiate (1 := fun z => ret (snd z, true)); reflexivity].
    simpl.
    unfold UpdateUnConstrRelationInsertC at 1.
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    rewrite (refine_Iterate_Count_For_UnConstrQuery_In _ H0).
    unfold Iterate_Equiv_Count_For_UnConstrQuery_In_body; simpl.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    simplify_GetAttributeRaw_inj.
    simpl; simplify_Query_Where.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    simplify_GetAttributeRaw_inj.
    simpl; simplify_Query_Where.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    simplify_GetAttributeRaw_inj.
    simplify_Query_Where.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    simplify_GetAttributeRaw_inj.
    simplify_GetAttributeRaw_inj.
    simplify_Query_Where.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simplify_GetAttributeRaw_inj.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
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
    erewrite (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ | eassumption | intros; set_refine_evar; refine pick val (snd r_n'); destruct r_n';
                        try eauto;
                        simplify with monad laws; simpl; try finish honing;
                        unfold H8; instantiate (1 := fun z => ret (snd z, true)); reflexivity].
    simpl.
    simpl; unfold UpdateUnConstrRelationInsertC at 1.
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simplify_GetAttributeRaw_inj.
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
    erewrite (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ | eassumption | intros; set_refine_evar; refine pick val (snd r_n'); destruct r_n';
                        try eauto;
                        simplify with monad laws; simpl; try finish honing;
                        unfold H9; instantiate (1 := fun z => ret (snd z, true)); reflexivity].
    simpl; unfold UpdateUnConstrRelationInsertC at 1.
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simplify_GetAttributeRaw_inj.
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
    erewrite (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ | eassumption | intros; set_refine_evar; refine pick val (snd r_n'); destruct r_n';
                        try eauto;
                        simplify with monad laws; simpl; try finish honing;
                        unfold H4; instantiate (1 := fun z => ret (snd z, true)); reflexivity].
    simpl; unfold UpdateUnConstrRelationInsertC at 1.
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where _ _ H0).
    simplify_GetAttributeRaw_inj.
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
    erewrite (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0);
      [ | eassumption | intros; set_refine_evar; refine pick val (snd r_n'); destruct r_n';
                        try eauto;
                        simplify with monad laws; simpl; try finish honing;
                        unfold H5; instantiate (1 := fun z => ret (snd z, true)); reflexivity].
    simpl; unfold UpdateUnConstrRelationInsertC at 1.
    repeat doOne ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
    repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
    refine pick val _; eauto; finish honing.
  }
  { repeat doOne ltac:(drop_constraints)
                        drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }
  simpl.
  pose {| prim_fst := [(EqualityIndex, @Fin.F1 3);
                       (FindStringPrefixIndex, @Fin.F1 3)];
          prim_snd := {|
          prim_fst := [(EqualityIndex, @Fin.F1 3);
                       (FindStringPrefixIndex, @Fin.F1 3)];
          prim_snd := {|
          prim_fst := [(EqualityIndex, @Fin.F1 3);
                       (FindStringPrefixIndex, @Fin.F1 3)];
          prim_snd := {|
          prim_fst := [(EqualityIndex, @Fin.F1 3);
                       (FindStringPrefixIndex, @Fin.F1 3)];
          prim_snd := () |} |} |} |}.

  Time let p' := eval unfold p in p in
           make_simple_indexes p'
                               ltac:(CombineCase6 BuildEarlyFindStringPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
                                      ltac:(CombineCase5 BuildLastStringFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)).

  (* We should be doing automatic data structure selection here. *)
   (* Constructor *)
      initializer.
  
   (* Add Data *)

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
    match goal with
      H : DelegateToBag_AbsR ?r_o ?r_n
      |- refine (l <- {idx | forall Ridx', UnConstrFreshIdx (GetUnConstrRelation ?r_o ?Ridx) idx }; _) _ =>
      let idx' := fresh in
      let idx_OK := fresh in
      destruct (@exists_UnConstrFreshIdx_Max _ _ _ _ H) as [idx idx_OK];
        refine pick val idx; [ | apply idx_OK]
    end.
    Local Opaque CallBagCount.
    repeat doOne ltac:(first [
                implement_Count
                  ltac:(find_simple_search_term
                          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
                                 ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
                                        ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm))
              | implement_insert''])
          ltac:(master_implement_drill
          ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
          ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
          ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm);
                set_evars) ltac:(finish honing).
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
  
  { simplify with monad laws.
    rewrite  refine_decode_packet.
    doAny implement_insert''
          ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
  }
  + hone method "AddData".
    subst.
    simpl.
    doAny ltac:(first [rewrite refine_bind_bind
                      | rewrite refine_bind_unit
                      | rewrite refineEquiv_pick_eq'
                      | simplify with monad laws])
                 ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars; simpl) ltac:(finish honing).
    simpl.
    apply reflexivityT.
    Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).
Print DNSImpl.
