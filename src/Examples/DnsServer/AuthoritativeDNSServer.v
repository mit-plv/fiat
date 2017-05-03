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
        Fiat.Examples.DnsServer.DecomposeEnumField
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
            (IfDec (List.Forall (fun r : resourceRecord => n = r!sNAME) results) (* If the record's QNAME is an exact match  *)
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
        }};
       b' <- encode_packet_Spec p' list_CacheEncode_empty;
       ret (this, Some (fst b'))
           Else ret (this, None)
           }.

Lemma DropQSConstraints_AbsR_SatisfiesTupleConstraints
  : forall {qs_schema} r_o r_n,
    @DropQSConstraints_AbsR qs_schema r_o r_n
    -> forall idx tup tup',
      elementIndex tup <> elementIndex tup'
      -> GetUnConstrRelation r_n idx tup
      -> GetUnConstrRelation r_n idx tup'
      -> SatisfiesTupleConstraints idx (indexedElement tup) (indexedElement tup').
Proof.
  intros. rewrite <- H in *.
  unfold SatisfiesTupleConstraints, GetNRelSchema,
  GetUnConstrRelation, DropQSConstraints in *.
  generalize (rawTupleconstr (ith2 (rawRels r_o) idx)).
  rewrite <- ith_imap2 in *.
  destruct (tupleConstraints (Vector.nth (qschemaSchemas qs_schema) idx)); eauto.
Qed.

Lemma DropQSConstraints_AbsR_SatisfiesAttribute
  : forall {qs_schema} r_o r_n,
    @DropQSConstraints_AbsR qs_schema r_o r_n
    -> forall idx tup,
      GetUnConstrRelation r_n idx tup
      -> SatisfiesAttributeConstraints idx (indexedElement tup).
Proof.
  intros. rewrite <- H in *.
  unfold SatisfiesAttributeConstraints, GetNRelSchema,
  GetUnConstrRelation, DropQSConstraints in *.
  generalize (rawAttrconstr (ith2 (rawRels r_o) idx)).
  rewrite <- ith_imap2 in *.
  destruct (attrConstraints (Vector.nth (qschemaSchemas qs_schema) idx)); eauto.
Qed.

Lemma refine_beq_RRecordType_dec :
  forall rr : resourceRecord,
    refine {b | decides b (rr!sTYPE = CNAME)}
           (ret (beq_RRecordType rr!sTYPE CNAME)).
Proof.
  intros; rewrite <- beq_RRecordType_dec.
  intros; refine pick val _.
  finish honing.
  find_if_inside; simpl; eauto.
Qed.

Lemma refine_constraint_check_into_query'' :
  forall heading R P' P
         (P_dec : DecideableEnsemble P),
    Same_set _ (fun tup => P (indexedElement tup)) P'
    -> refine
         (Pick (fun (b : bool) =>
                  decides b
                          (exists tup2: @IndexedRawTuple heading,
                              (R tup2 /\ P' tup2))))
         (Bind
            (Count (For (QueryResultComp R (fun tup => Where (P tup) Return tup))))
            (fun count => ret (negb (beq_nat count 0)))).
Proof.
  Local Transparent Count.
  unfold refine, Count, UnConstrQuery_In;
    intros * excl * P_iff_P' pick_comp ** .
  computes_to_inv; subst.

  computes_to_constructor.

  destruct (Datatypes.length v0) eqn:eq_length;
    destruct v0 as [ | head tail ]; simpl in *; try discriminate; simpl.

  pose proof (For_computes_to_nil _ R H).
  rewrite not_exists_forall; intro a; rewrite not_and_implication; intros.
  unfold not; intros; eapply H0; eauto; apply P_iff_P'; eauto.

  apply For_computes_to_In with (x := head) in H; try solve [intuition].
  destruct H as ( p & [ x0 ( in_ens & _eq ) ] ); subst.
  eexists; split; eauto; apply P_iff_P'; eauto.

  apply decidable_excl; assumption.
Qed.

Lemma refine_noDup_CNAME_check :
  forall (rr : resourceRecord)
         (R : @IndexedEnsemble resourceRecord),
  (forall tup tup' : IndexedElement,
          elementIndex tup <> elementIndex tup' ->
          R tup ->
          R tup' ->
          (indexedElement tup)!sNAME = (indexedElement tup')!sNAME
          -> (indexedElement tup)!sTYPE <> CNAME)
  -> refine {b |
            decides b
                    (forall tup',
                        R tup' ->
                        rr!sNAME = (indexedElement tup')!sNAME -> rr!sTYPE <> CNAME)}
           (If (beq_RRecordType rr!sTYPE CNAME)
               Then count <- Count
               For
               (QueryResultComp R
                                (fun tup => Where (rr!sNAME = tup!sNAME)
                                                  Return tup )%QueryImpl);
                  ret (beq_nat count 0) Else ret true).
Proof.
  intros.
    intros; setoid_rewrite refine_pick_decides at 1;
    [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
    setoid_rewrite refine_beq_RRecordType_dec; simplify with monad laws.
    apply refine_If_Then_Else; eauto.
    setoid_rewrite refine_constraint_check_into_query'' with (P := fun tup => rr!sNAME = tup!sNAME);
    auto with typeclass_instances.
    rewrite refineEquiv_bind_bind.
    f_equiv.
    unfold pointwise_relation; intros; simplify with monad laws;
      rewrite <- negb_involutive_reverse; reflexivity.
    intuition.
  reflexivity.
Qed.

Corollary refine_noDup_CNAME_check_dns :
  forall (rr : resourceRecord) r_o r_n,
    @DropQSConstraints_AbsR DnsSchema r_o r_n
  -> refine {b |
            decides b
                    (forall tup',
                        (GetUnConstrRelation r_n Fin.F1) tup' ->
                        rr!sNAME = (indexedElement tup')!sNAME -> rr!sTYPE <> CNAME)}
           (If (beq_RRecordType rr!sTYPE CNAME)
               Then count <- Count
               For
               (UnConstrQuery_In r_n Fin.F1
                                (fun tup => Where (rr!sNAME = tup!sNAME)
                                                  Return tup )%QueryImpl);
                  ret (beq_nat count 0) Else ret true).
Proof.
  intros; eapply refine_noDup_CNAME_check.
  intros; eapply (DropQSConstraints_AbsR_SatisfiesTupleConstraints _ _ H Fin.F1); eauto.
Qed.

Lemma is_empty_app {A} :
  forall (l l' : list A),
    is_empty (l ++ l') = andb (is_empty l) (is_empty l').
Proof.
  induction l; simpl; eauto.
Qed.

Lemma flatten_CompList_Prop {A}
  : forall (P : Ensemble A) (P_dec : DecideableEnsemble P) (As As' : list A),
    FlattenCompList.flatten_CompList (map (fun a : A => Where (P a)
                                                              Return a ) As) ↝ As'
    -> forall a, List.In a As' -> P a.
Proof.
  induction As; simpl; intros; computes_to_inv; subst; simpl in *; intuition.
  unfold Query_Where, Query_Return in H; computes_to_inv; intuition.
  destruct (dec a) eqn: ?.
  - rewrite dec_decides_P in Heqb.
    pose proof (H1 Heqb); computes_to_inv;
      subst; simpl in *; subst; intuition eauto.
    subst; eauto.
  - apply Decides_false in Heqb; apply H2 in Heqb; subst; simpl in *;
      eauto.
Qed.

Lemma flatten_CompList_Subset {A}
  : forall (P : Ensemble A) (P_dec : DecideableEnsemble P) (As As' : list A),
    FlattenCompList.flatten_CompList (map (fun a : A => Where (P a)
                                                              Return a ) As) ↝ As'
    -> forall a, List.In a As' -> List.In a As.
Proof.
  induction As; simpl; intros; computes_to_inv; subst; simpl in *; intuition.
  unfold Query_Where, Query_Return in H; computes_to_inv; intuition.
  destruct (dec a) eqn: ?.
  - rewrite dec_decides_P in Heqb.
    pose proof (H1 Heqb); computes_to_inv;
      subst; simpl in *; subst; intuition eauto.
  - apply Decides_false in Heqb; apply H2 in Heqb; subst; simpl in *;
      eauto.
Qed.

Lemma flatten_CompList_nil {A}
  : forall (P : Ensemble A) (P_dec : DecideableEnsemble P) (As : list A),
    FlattenCompList.flatten_CompList
      (map (fun a : A => Where (P a)
                               Return a ) As) ↝ nil
    -> forall a, List.In a As -> ~ P a.
Proof.
    induction As; simpl; intros; computes_to_inv; subst; simpl in *; intuition.
    unfold Query_Where, Query_Return in H; computes_to_inv; intuition.
    destruct (dec a) eqn: ?.
    - rewrite dec_decides_P in Heqb.
      apply H0 in Heqb; computes_to_inv;
        subst; simpl in *; subst; intuition eauto.
      discriminate.
    - subst; apply H0 in H1; computes_to_inv;
        subst; simpl in *; subst; intuition eauto.
      discriminate.
    - eapply IHAs; eauto.
      apply app_eq_nil in H''; intuition; subst; eauto.
Qed.

Lemma refine_ListComprehension {A}
  : forall (As : list A)
           (P Q : A -> Prop),
    (forall a, P a <-> Q a)
    -> refine (⟦element in As | P element ⟧)
              (⟦element in As | Q element ⟧).
Proof.
  induction As; simpl; intros; eauto.
  - reflexivity.
  - rewrite IHAs; eauto.
    f_equiv; intro.
    intros ? ?.
    computes_to_inv; destruct v0; simpl in *.
    + apply (@BindComputes _ _ _ _ true); eauto.
      computes_to_econstructor; simpl; eauto.
      apply H; assumption.
    + apply (@BindComputes _ _ _ _ false); eauto.
    computes_to_econstructor;
      simpl; unfold UpperBound; intros.
    intro; apply H0.
    apply H; eassumption.
Qed.

Lemma refine_FindUpperBound {A B}
  : forall (op : B -> B -> Prop)
           (op_trans : forall b b' b'', op b b' -> op b' b'' -> op b b'')
           (bound : B)
           (As As' : list A)
           (f : A -> B),
    (forall a, List.In a As' -> op (f a) bound)
    -> (exists a, List.In a As' /\ f a = bound)
    -> refine (⟦element in As | UpperBound (fun a a' => op (f a) (f a')) As' element ⟧)
              (⟦element in As | op bound (f element) ⟧).
Proof.
  intros.
  unfold UpperBound.
  apply refine_ListComprehension.
  split; intros.
  - destruct_ex; intuition eauto; subst; eauto.
  - eapply op_trans; eauto.
Qed.

Lemma refine_MaxElements {A B}
      {eqB : Query_eq B }
  : forall (op : B -> B -> Prop)
           (op_refl : forall b, op b b)
           (op_trans : forall b b' b'', op b b' -> op b' b'' -> op b b'')
           (op_dec : forall b, DecideableEnsemble (fun b' => op b' b))
           (op_irrefl : forall b b', op b b' -> op b' b -> b = b')
           (bound : B)
           (As : @IndexedEnsemble A)
           (f : A -> B),
    refine (MaxElements (fun a a' => op (f a) (f a'))
                        (As' <- {As' : list A | UnIndexedEnsembleListEquivalence As As'};
                           FlattenCompList.flatten_CompList (map (fun a => Where (op (f a) bound)
                                                                                 Return a) As')))
           (As' <- (As' <- {As' : list A | UnIndexedEnsembleListEquivalence As As'};
                      FlattenCompList.flatten_CompList (map (fun a => Where ((f a) = bound)
                                                                            Return a) As'));
              If negb (is_empty As') Then ret As' Else
                 (MaxElements (fun a a' => op (f a) (f a'))
                              (As' <- {As' : list A | UnIndexedEnsembleListEquivalence As As'};
                                 FlattenCompList.flatten_CompList (map (fun a => Where (op (f a) bound /\ (f a) <> bound)
                                                                                       Return a) As')))).
Proof.
  unfold MaxElements; intros; simplify with monad laws.
  setoid_rewrite refineEquiv_bind_bind.
  unfold refine; intros.
  computes_to_inv.
  destruct (is_empty v1) eqn: v1_eq; simpl in *; computes_to_inv; subst.
  - computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    assert (forall a', List.In a' v3 -> f a' <> bound).
    { intros; eapply Permutation_in in H0;
        eauto using (Permutation_UnIndexedEnsembleListEquivalence' H'' H).
      clear H.
      generalize dependent v1; generalize dependent v0; clear;
        induction v0; simpl; intros; intuition;
          computes_to_inv; subst.
      + unfold Query_Where, Query_Return in H'; computes_to_inv; subst.
        intuition; computes_to_inv; subst.
        simpl in v1_eq; discriminate.
      + eapply H0; eauto.
        rewrite is_empty_app, andb_true_iff in v1_eq.
        intuition.
    }
    generalize v2 H'''0 H0; clear; induction v3; simpl; intros;
      computes_to_inv; subst; intuition eauto.
    computes_to_econstructor.
    eapply refine_Query_Where_Cond in H'''0; eauto.
    intuition eauto.
    computes_to_econstructor.
    eapply IHv3; eauto.
    eauto.
  - computes_to_econstructor; eauto.
    assert (exists v',
               computes_to
                 (FlattenCompList.flatten_CompList (map (fun a : A => Where (op (f a) bound)
                                                                         Return a ) v0)) v').
    {
      revert op_dec; clear; induction v0; simpl; intros; eauto.
      destruct IHv0; eauto.
      destruct (dec (DecideableEnsemble := op_dec bound) (f a)) eqn:?.
      rewrite dec_decides_P in Heqb.
      eexists; computes_to_econstructor.
      computes_to_econstructor; split; intros.
      computes_to_econstructor.
      intuition.
      computes_to_econstructor; eauto.
      eexists; computes_to_econstructor.
      computes_to_econstructor; split; intros.
      apply Decides_false in Heqb.
      intuition.
      reflexivity.
      computes_to_econstructor; eauto.
    }
    destruct_ex; computes_to_econstructor; eauto.
    eapply (refine_FindUpperBound _ op_trans bound); eauto.
    intros.
    eapply flatten_CompList_Prop in H0; eauto.
    refine {| dec a := dec (f a) |}.
    intros; rewrite dec_decides_P; reflexivity.
    generalize dependent v; generalize dependent x; clear H.
    induction v0; simpl.
    + intros; computes_to_inv; subst; simpl in *; discriminate.
    + intros; computes_to_inv; subst; simpl; eauto.
      unfold Query_Where, Query_Return in H0, H'; computes_to_inv; subst.
      intuition; computes_to_inv; subst.
      destruct (A_eq_dec (f a) bound); subst.
      * specialize (H0 (eq_refl _)); computes_to_inv; subst.
        specialize (H (op_refl _)); computes_to_inv; subst.
        eexists; simpl; intuition eauto.
      * apply H2 in n; subst.
        simpl in v1_eq.
        destruct (IHv0 _ H0' _ H'' v1_eq); intuition.
        eexists; split; eauto.
        apply in_or_app; right; eauto.
    + generalize dependent v; generalize dependent x; clear H.
      induction v0; simpl.
      * intros; computes_to_inv; subst; simpl in *; discriminate.
      * intros; computes_to_inv; subst; simpl; eauto.
        unfold Query_Where, Query_Return in H0, H'; computes_to_inv; subst.
        intuition; computes_to_inv; subst.
        destruct (dec (DecideableEnsemble := op_dec bound) (f a)) eqn:?.
        rewrite dec_decides_P in Heqb; pose proof (H Heqb).
        computes_to_inv; subst; simpl.
        destruct (A_eq_dec (f a) bound); subst.
        pose proof (H0 (eq_refl _)); computes_to_inv; subst.
        destruct (is_empty v2) eqn: ?.
        apply (@BindComputes _ _ _ _ [ ]); eauto.
        { revert eqB op_dec op_irrefl Heqb0 H0' H''; clear; revert v4 v2; induction v0;
            simpl; intros; computes_to_inv; subst; simpl.
          computes_to_econstructor.
          unfold Query_Where, Query_Return in H0', H''; computes_to_inv; subst.
          intuition; computes_to_inv; subst.
          destruct (dec (DecideableEnsemble := op_dec (f a)) (f a0)) eqn: ?.
          - rewrite dec_decides_P in Heqb; pose proof (H Heqb).
            computes_to_inv; subst.
            simpl.
            destruct (A_eq_dec (f a0) (f a)).
            + apply H1 in e; computes_to_inv; subst.
              simpl in *; discriminate.
            + pose proof (H2 n); subst; simpl in *.
              computes_to_econstructor; eauto.
              apply (@BindComputes _ _ _ _ false); eauto.
              computes_to_econstructor; simpl.
              intuition.
          - apply Decides_false in Heqb.
            pose proof (H0 Heqb); subst; simpl.
            destruct (A_eq_dec (f a0) (f a)); subst.
            intuition; computes_to_inv; subst.
            simpl in Heqb0; discriminate.
            apply H2 in n; subst; eauto.
        }
        apply (@BindComputes _ _ _ _ true); eauto.
        destruct v2; simpl in *; try discriminate.
        computes_to_econstructor.
        computes_to_econstructor.
        eauto.
        apply (@BindComputes _ _ _ _ true); eauto.
        pose proof (H2 n); subst; simpl.
        simpl in v1_eq.
        computes_to_econstructor; eauto.
        apply (@BindComputes _ _ _ _ false); eauto.
        computes_to_econstructor; simpl.
        intro; eapply n; eauto.
        apply Decides_false in Heqb.
        pose proof (H1 Heqb); subst; simpl.
        destruct (A_eq_dec (f a) bound); subst.
        intuition.
        apply H2 in n; subst; eauto.
Qed.

Lemma Query_Where_And_Sym {ResultT}
  : forall (P Q : Prop)
           (body : Comp (list ResultT)),
    refine (Query_Where (P /\ Q) body)
           (Query_Where (Q /\ P) body).
Proof.
  intros; rewrite refine_Query_Where_Cond;
    try reflexivity; intuition.
Qed.

Ltac implement_insert'' :=
  implement_insert' ltac:(CombineCase5 StringPrefixIndexUse EqIndexUse)
         ltac:(CombineCase10 createEarlyStringPrefixTerm createEarlyEqualityTerm)
         ltac:(CombineCase7 createLastStringPrefixTerm createLastEqualityTerm)
         ltac:(CombineCase7 StringPrefixIndexUse_dep EqIndexUse_dep)
         ltac:(CombineCase11 createEarlyStringPrefixTerm_dep createEarlyEqualityTerm_dep)
         ltac:(CombineCase8 createLastStringPrefixTerm_dep createLastEqualityTerm_dep).

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
    eapply refineFueledFix.
    - finish honing.
    - intros.
      doOne ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      doAny ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
      setoid_rewrite H2.
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
      doAny ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
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

  hone representation using (@DecomposeRawQueryStructureSchema_AbsR _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) id
             id).
  { simplify with monad laws.
    refine pick val _.
    2: apply DecomposeRawQueryStructureSchema_empty_AbsR.
    finish honing.
  }
  {
    simplify with monad laws.
    drop_constraints_drill.
    rewrite (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0);
      finish honing.
    drop_constraints_drill.
    drop_constraints_drill.
    setoid_rewrite refine_Iterate_Equiv_QueryResultComp; try eassumption.
    (* simpl; unfold Tuple_DecomposeRawQueryStructure_inj; simpl. *)
    finish honing.
    finish honing.
    drop_constraints_drill.
    setoid_rewrite Query_Where_And_Sym.
    setoid_rewrite (refine_QueryIn_Where H0).
    simpl.
    unfold Tuple_DecomposeRawQueryStructure_inj; simpl.
    unfold GetAttribute, GetAttributeRaw at 2; simpl.
    unfold ilist2_hd; simpl.
    finish honing.
    rewrite !refine_if_If.
    rewrite !refine_If_Then_Else_Bind.
    drop_constraints_drill.
    drop_constraints_drill.
    simplify with monad laws.
    apply (DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq _ _ H0).
    clear; admit.
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
    drop_constraints_drill.
    drop_constraints_drill.
    drop_constraints_drill.
    eapply refineFueledFix.
    finish honing.
    intros.
    simplify with monad laws.
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))))
  ).
  Print DnsSchema.
  hone representation using (@DecomposeRawQueryStructureSchema_AbsR _ DnsSchema (Fin.FS (Fin.FS (Fin.FS Fin.F1))))


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
