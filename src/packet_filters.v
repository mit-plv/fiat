Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header.
Require Import Fiat.Narcissus.Examples.NetworkStack.TCP_Packet.
Require Import Bedrock.Word.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import IndexedEnsembles.
Require Import Fiat.Narcissus.Examples.IPTables.

Definition sINPUT := "Input".
Definition sHISTORY := "GlobalHistory".
Definition PacketHistorySchema :=
  Query Structure Schema
        [ relation sHISTORY has
                   schema < sINPUT :: input > ]
        enforcing [].


Definition StatefulFilterSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "Filter" : rep * input -> rep * (option result)
    }.


(**
we are 18.X.X.X
outside world is all other IP addresses
filter allows outside address to talk to us only if we have talked to it first
**)

Definition OutgoingRule :=
  iptables -A FORWARD --source 18'0'0'0/24.

Definition IncomingRule :=
  iptables -A FORWARD --destination 18'0'0'0/24.

Definition OutgoingToRule (dst: address) :=
  and_cf OutgoingRule (lift_condition in_ip4 (cond_dstaddr {| saddr := dst; smask := mask_of_nat 32 |})).

Lemma OutgoingToImpliesOutgoing:
  forall inp dst,
    (OutgoingToRule dst).(cf_cond) inp -> OutgoingRule.(cf_cond) inp.
Proof.
  intros. simpl in *. unfold combine_conditions in *. apply andb_prop in H. destruct H. rewrite H. constructor. Qed.

Opaque OutgoingRule.
Opaque IncomingRule.
Opaque OutgoingToRule.

Definition FilterMethod (r: QueryStructure PacketHistorySchema) (inp: input) : Comp (option result) :=
  if (OutgoingRule.(cf_cond) inp) then ret (Some ACCEPT)
  else if negb (IncomingRule.(cf_cond) inp) then ret None
  else b <- { b: bool | decides b (exists pre,
    IndexedEnsemble_In (GetRelation r Fin.F1) < sINPUT :: pre > /\
    ((OutgoingToRule inp.(in_ip4).(SourceAddress)).(cf_cond) pre = true)) };
    if b then ret (Some ACCEPT) else ret (Some DROP).

Definition FilterMethod_UnConstr (r: UnConstrQueryStructure PacketHistorySchema) (inp: input) : Comp (option result) :=
  if (OutgoingRule.(cf_cond) inp) then ret (Some ACCEPT)
  else if negb (IncomingRule.(cf_cond) inp) then ret None
  else b <- { b: bool | decides b (exists pre,
    IndexedEnsemble_In (GetUnConstrRelation r Fin.F1) < sINPUT :: pre > /\
    ((OutgoingToRule inp.(in_ip4).(SourceAddress)).(cf_cond) pre = true)) };
    if b then ret (Some ACCEPT) else ret (Some DROP).

Lemma UnConstrPreservesFilterMethod: forall r_o r_n inp res,
  DropQSConstraints_AbsR r_o r_n ->
  computes_to (FilterMethod r_o inp) res <->
  computes_to (FilterMethod_UnConstr r_n inp) res.
Proof.
  intros. unfold FilterMethod, FilterMethod_UnConstr in *.
  destruct (OutgoingRule.(cf_cond) inp) eqn:out. reflexivity.
  destruct (negb (IncomingRule.(cf_cond) inp)) eqn:inc. reflexivity.
  split; intros; apply Bind_inv in H0; destruct H0 as [b [Hbin Hbres]];
    unfold DropQSConstraints_AbsR in H; rewrite <- H in *; computes_to_econstructor;
    [rewrite GetRelDropConstraints; apply Hbin | apply Hbres
    | rewrite <- GetRelDropConstraints; apply Hbin | apply Hbres].
Qed.

Definition NoIncomingConnectionsFilter : ADT StatefulFilterSig :=
  Eval simpl in Def ADT {
    rep := QueryStructure PacketHistorySchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "Filter" (r: rep) (inp: input) : rep * option result :=
      res <- FilterMethod r inp;
      `(r, _) <- Insert (< sINPUT :: inp >) into r!sHISTORY;
      ret (r, res)
  }%methDefParsing.

Lemma simpl_in_bind:
  forall (T U: Type) (x v : T) (y: U),
    In T (`(r', _) <- ret (x, y); ret r') v -> x = v.
Proof.
  intros. apply Bind_inv in H. destruct H. destruct H. apply Return_inv in H. rewrite <- H in H0. simpl in H0. apply Return_inv in H0. assumption. Qed.

Definition UnIndexedEnsembleListEquivalence'
           (ElementType : Type)
           (ensemble : IndexedEnsemble)
           (l : list ElementType) :=
  sig (fun (l': list IndexedElement) =>
         map indexedElement l' = l /\
         (forall x : IndexedElement,
            In IndexedElement ensemble x <-> List.In x l') /\
         NoDup (map elementIndex l')).


Definition AllFinite {qs_schema} (r: UnConstrQueryStructure qs_schema) :=
  forall idx, {l: list RawTuple & UnIndexedEnsembleListEquivalence' _ (GetUnConstrRelation r idx) l}.

Definition FiniteTables_AbsR'
    {qs_schema}
    (r_o : UnConstrQueryStructure qs_schema)
    (r_n : { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n }) :=
  r_o = projT1 r_n.

Lemma QSEmptyIsFinite {qs_schema}: AllFinite (DropQSConstraints (QSEmptySpec qs_schema)).
Proof.
  unfold AllFinite. intros. exists []. exists [].
  split. reflexivity. split. split; intros.
(*  pose proof (FiniteEnsemble_QSEmptySpec idx) as Hfin. red in Hfin.
  destruct Hfin as [l Hl]. red in Hl. destruct Hl as [l' [Hmap [Heqv Hdup]]]. *)
  unfold In, GetUnConstrRelation, DropQSConstraints, QSEmptySpec in H. simpl in H.


  Coercion mycoer {qs_schema idx t}
           (y: @IndexedElement
                 (@RawTuple
                    (@GetNRelSchemaHeading
                       (numRawQSschemaSchemas
                          (QueryStructureSchemaRaw qs_schema))
                       (qschemaSchemas (QueryStructureSchemaRaw qs_schema)) idx))) :
    @IndexedRawTuple
      (rawSchemaHeading
         (@Vector.nth RawSchema (numQSschemaSchemas qs_schema) t idx)).
  Admitted.

  assert (Hscraw: qschemaSchemas qs_schema = Vector.map schemaRaw (QSschemaSchemas qs_schema)).
  { reflexivity. }

  replace x with (@mycoer _ _ (@Vector.map Schema RawSchema schemaRaw (numQSschemaSchemas _) (QSschemaSchemas _)) x) in H.
  rewrite <- Hscraw in H. rewrite <- ith_imap2 in H.
  Set Printing All. Check (Build_EmptyRelation_IsEmpty qs_schema idx). simpl in H. admit. admit.
  (*replace (fun ns: RawSchema => RawRelation ns) with RawRelation in H. rewrite Build_EmptyRelation_IsEmpty in H.*)
  inversion H. constructor.
Qed.
Unset Printing All.

Lemma FiniteTables_AbsR'_QSEmptySpec
      {qs_schema}
  :  FiniteTables_AbsR'
       (DropQSConstraints (QSEmptySpec qs_schema))
       (existT AllFinite (DropQSConstraints (QSEmptySpec qs_schema)) QSEmptyIsFinite).
Proof. reflexivity. Qed.

Lemma change_refine_form {X1 X2 Y Z} :
  forall (cx: Comp (X1 * X2)) (cy: X1 * X2 -> Comp Y) (f: Y -> Comp Z),
    refine
      (x <- cx;
       y <- cy x;
       f y)
      (x0 <- (x <- cx;
              y <- cy x;
              ret (y, snd x));
       f (fst x0)).
Proof.
  intros.
  unfold refine; intros.
  computes_to_inv; subst.
  eauto.
Qed.


Lemma insert_finite_helper:
  forall (qs_schema : RawQueryStructureSchema)
         (r_n: { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n })
         idx tup,
    UnConstrFreshIdx (GetUnConstrRelation (projT1 r_n) idx) (elementIndex tup) ->
    AllFinite (UpdateUnConstrRelation (projT1 r_n) idx
                 (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) idx))).
Proof.
  red; intros qsc r_n idx tup Hfresh idx'. destruct (Fin.eqb idx idx') eqn:idxeq.
  - apply Fin.eqb_eq in idxeq. subst idx'.
    destruct r_n as [r Hfin]. destruct (Hfin idx) as [l1 Hl1].
    destruct Hl1 as [l2 [Hmap [Hin Hdup]]].
    exists ((indexedElement tup) :: l1). cbn.
    rewrite get_update_unconstr_eq. red. exists (tup :: l2).
    
    split. simpl. rewrite <- Hmap. reflexivity. split.
    split; intros H; unfold EnsembleInsert, In in *;
      destruct H; simpl;
        [ left; symmetry; assumption
        | right; apply (Hin x); apply H
        | left; symmetry; assumption
        | right; apply (Hin x); apply H].
    
    simpl. apply NoDup_cons. red in Hfresh. simpl in Hfresh.
    assert (Hlist: forall (x: nat) l,
               (forall x', List.In x' l -> lt x' x) ->
               ~List.In x l).
    {
      intros x l Hx'. intro Hx. apply (Hx' x) in Hx.
      apply lt_irrefl in Hx. inversion Hx.
    }
    apply Hlist. apply forall_In_map. intros elem Helem.
    apply Hfresh. apply (Hin elem).
    assumption. assumption.
    
  - assert (Hidxeq: idx <> idx').
    { intro. apply Fin.eqb_eq in H. congruence. }
    destruct r_n as [r Hfin]. destruct (Hfin idx') as [l1 Hl1].
    exists l1. cbn. rewrite get_update_unconstr_neq.
    assumption. assumption.
Qed.

Lemma FiniteTables_AbsR'_Insert :
  forall (qs_schema : RawQueryStructureSchema) r_o r_n
         (idx : Fin.t (numRawQSschemaSchemas qs_schema)) tup,
    FiniteTables_AbsR' r_o r_n ->
    UnConstrFreshIdx (ith2 r_o idx) (elementIndex tup) ->
    forall (H: UnConstrFreshIdx (GetUnConstrRelation (projT1 r_n) idx) (elementIndex tup)),
    refine
      {r_n0 : { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n } |
       FiniteTables_AbsR'
         (UpdateUnConstrRelation r_o idx (EnsembleInsert tup (GetUnConstrRelation r_o idx))) r_n0}
      (ret (existT AllFinite
              (UpdateUnConstrRelation (projT1 r_n) idx
                 (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) idx)))
              (insert_finite_helper _ _ _ _ H))).
Proof.
  intros qsc r_o r_n idx tup Hrel Hfresho Hfreshn.
  unfold refine; intros r_n' Hr_n'. apply Return_inv in Hr_n'. subst r_n'.
  computes_to_econstructor. red; cbn. red in Hrel. subst r_o. reflexivity.
Qed.


Definition LessHistoryRelation (r_o r_n : sigT (@AllFinite PacketHistorySchema)) :=
  forall inp,
    (OutgoingRule.(cf_cond) inp) ->
    ((IndexedEnsemble_In (GetUnConstrRelation (projT1 r_n) Fin.F1) < sINPUT :: inp >)
     <-> IndexedEnsemble_In (GetUnConstrRelation (projT1 r_o) Fin.F1) < sINPUT :: inp >).

Lemma LessHistoryPreservesFilter:
  forall inp r_o r_n,
    LessHistoryRelation r_o r_n ->
    refine
      (FilterMethod_UnConstr (projT1 r_o) inp)
      (FilterMethod_UnConstr (projT1 r_n) inp).
Proof.
  red; intros. unfold FilterMethod_UnConstr in *.
  unfold LessHistoryRelation in H.
  destruct (cf_cond OutgoingRule inp) eqn:outrule;
    destruct (negb (cf_cond IncomingRule inp)) eqn:ninrule;
    simpl in *; try apply H0.
  inversion H0. destruct H1. computes_to_econstructor.
  destruct x eqn:truefalse.

  - instantiate (1 := x).
    computes_to_econstructor. unfold decides; simpl.
    destruct H1. destruct H1. exists x0. split.
    * apply (H x0).
      apply (OutgoingToImpliesOutgoing x0 (SourceAddress (in_ip4 inp))).
      assumption. assumption.
    * assumption.

  - computes_to_econstructor; unfold decides; simpl.
    unfold not; intros. destruct H1. destruct H3. destruct H1.
    exists x0. split.
    * apply (H x0).
      apply (OutgoingToImpliesOutgoing x0 (SourceAddress (in_ip4 inp))).
      assumption. assumption.
    * assumption.

  - assumption.
Qed.


Lemma LessHistoryRelationRefl:
  forall r_o, LessHistoryRelation r_o r_o.
Proof.
  unfold LessHistoryRelation; split; intros; assumption. Qed.

Definition IncrMaxFreshIdx (r: sigT (@AllFinite PacketHistorySchema)) :=
  S (fold_right (fun elem acc => max (elementIndex elem) acc) 0 (proj1_sig (projT2 ((projT2 r) Fin.F1)))).

Lemma IncrMaxFreshIdx_Refine:
  forall (r: sigT (@AllFinite PacketHistorySchema)),
    refine
      {idx: nat | UnConstrFreshIdx (GetUnConstrRelation (projT1 r) Fin.F1) idx}
      (ret (IncrMaxFreshIdx r)).
Proof.
  intros r. pose (proj2_sig (projT2 ((projT2 r) Fin.F1))) as Hl.
  destruct Hl as [Hmap [Heqv Hdup]].
  intro idx; intro Hidx; computes_to_econstructor;
    intro elem; intros Helem.
  apply Return_inv in Hidx. apply Heqv in Helem.
  unfold lt. rewrite <- Hidx. apply le_n_S.
  apply fold_right_max_is_max; apply Helem.
Qed.


Theorem SharpenNoIncomingFilter:
  FullySharpened NoIncomingConnectionsFilter.
Proof.
  start sharpening ADT.
  hone representation using (@DropQSConstraints_AbsR PacketHistorySchema).
  - apply Constructor_DropQSConstraints.
  - simplify with monad laws.
    unfold Bind2.
    simplify with monad laws.
    Transparent QSInsert.
    cbn.

    etransitivity.
    eapply refine_bind.
    reflexivity.
    unfold pointwise_relation.
    intros.

    etransitivity.
    apply change_refine_form.
    unfold QSInsert.
    rewrite QSInsertSpec_UnConstr_refine; eauto; cycle 1;
      try (refine pick val true; [reflexivity | cbv; intros; exact I]);
      try (cbv -[refine]; intros; refine pick val true;
        [simplify with monad laws; higher_order_reflexivity | eauto]).
      * simplify with monad laws.
        higher_order_reflexivity.
      * etransitivity. eapply refine_bind. red; intros v Htemp.
        apply (UnConstrPreservesFilterMethod r_o r_n d v H0). apply Htemp.
        unfold pointwise_relation; intros. higher_order_reflexivity.
        subst H. higher_order_reflexivity.

  - hone representation using (@FiniteTables_AbsR' PacketHistorySchema).
    + simplify with monad laws.
      refine pick val
        (existT _ (DropQSConstraints (QSEmptySpec _)) QSEmptyIsFinite).
      * subst H; higher_order_reflexivity.
      * apply FiniteTables_AbsR'_QSEmptySpec.
    + simplify with monad laws.
      eapply refine_bind.
      * red in H0; simpl in H0; rewrite H0.
        higher_order_reflexivity.
      * red; intros. red in H0. subst r_o.
        eapply refine_under_bind_both.
        apply IncrMaxFreshIdx_Refine.
        intros idx Hidx; cbn.
        rewrite FiniteTables_AbsR'_Insert; cbn; eauto.
        simplify with monad laws. higher_order_reflexivity.
        unfold FiniteTables_AbsR'. reflexivity.

    + hone representation using LessHistoryRelation;
        try simplify with monad laws.
      * refine pick val
          (existT _ (DropQSConstraints (QSEmptySpec _)) QSEmptyIsFinite).
        subst H; reflexivity. apply LessHistoryRelationRefl.
      * etransitivity. eapply refine_under_bind.
        intros res Hres. cbn. eapply refine_bind.

        Definition RefinedInsert
                   (r: sigT (@AllFinite PacketHistorySchema)) d H :=
          existT AllFinite (UpdateUnConstrRelation (projT1 r) Fin.F1
            (EnsembleInsert
               {| elementIndex := IncrMaxFreshIdx r;
                  indexedElement := icons2 d inil2 |}
               (GetUnConstrRelation (projT1 r) Fin.F1)))
            (insert_finite_helper PacketHistorySchema r Fin.F1
               {| elementIndex := IncrMaxFreshIdx r;
                  indexedElement := icons2 d inil2 |} H).
        
        refine pick val
               (if cf_cond OutgoingRule d
                then (RefinedInsert r_n d _)
                else r_n).
        reflexivity.

        destruct (cf_cond OutgoingRule d) eqn:outrule.
        red; intros inp Hinp. unfold RefinedInsert. split; intros.

        cbn in H1. rewrite get_update_unconstr_eq in H1. red in H1. destruct H1. destruct H1.
        { exists (IncrMaxFreshIdx r_o). cbn. red. rewrite get_update_unconstr_eq. red. left. inversion H1. reflexivity. }
        { cbn. rewrite get_update_unconstr_eq. red. unfold In. unfold EnsembleInsert. pose proof (H0 inp Hinp). unfold IndexedEnsemble_In in H2. unfold In in H2. assert (Hm: exists idx, GetUnConstrRelation (projT1 r_o) Fin.F1 {| elementIndex := idx; indexedElement := icons2 (value (ilist2_hd (icons2 (sINPUT :: inp)%Component inil2))) inil2 |}). { apply H2. exists x. apply H1. } destruct Hm. exists x0. right. apply H3. }

        cbn in H1. rewrite get_update_unconstr_eq in H1. red in H1. destruct H1. destruct H1.
        { exists (IncrMaxFreshIdx r_n). cbn. red. rewrite get_update_unconstr_eq. red. left. inversion H1. reflexivity. }
        { cbn. rewrite get_update_unconstr_eq. red. unfold In. unfold EnsembleInsert. pose proof (H0 inp Hinp). unfold IndexedEnsemble_In in H2. unfold In in H2. assert (Hm: exists idx, GetUnConstrRelation (projT1 r_n) Fin.F1 {| elementIndex := idx; indexedElement := icons2 (value (ilist2_hd (icons2 (sINPUT :: inp)%Component inil2))) inil2 |}). { apply H2. exists x. apply H1. } destruct Hm. exists x0. right. apply H3. }

        red; intros inp Hinp. split; intros.

        apply (H0 inp Hinp) in H1. cbn. rewrite get_update_unconstr_eq. red. red in H1. destruct H1. exists x. red. red. right. apply H1.

        cbn in H1; rewrite get_update_unconstr_eq in H1. red in H1. destruct H1. red in H1. red in H1. destruct H1. inversion H1. rewrite <- H4 in outrule. rewrite outrule in Hinp. inversion Hinp. apply (H0 inp Hinp). red; exists x; red. apply H1.


        red; intros. higher_order_reflexivity.
        simplify with monad laws. eapply refine_bind.
        apply (LessHistoryPreservesFilter d r_o r_n H0).
        red; intros. higher_order_reflexivity.


      * 
        


        
(*
Definition sID := "ID".
Definition sPACKET := "Packet".

Record Packet := packet
  { tcp_p: TCP_Packet;
    ip_h: IPv4_Packet; }.

Definition sHISTORY := "Packet History".

Definition PacketHistorySchema :=
  Query Structure Schema
    [ relation sHISTORY has
              schema < sID :: nat,
                       sPACKET :: Packet > ]
      enforcing [].

(* Definition Packet := TupleDef PacketHistorySchema sHISTORY.
 *)
Definition FilterSig : ADTSig :=
    ADTsignature {
        Constructor "Init" : rep,
        Method "Filter" : rep * Packet -> rep * bool
    }.

(** spec examples **)


(* Disallow all cross-domain SSH *)
(* --> if dst-port == 22 and src-domain != dst-domain, fail, else pass *)
Definition CrossDomain22FilterSpec : ADT FilterSig :=
    Eval simpl in Def ADT {
        rep := QueryStructure PacketHistorySchema,
        Def Constructor0 "Init" : rep := empty,,

        Def Method1 "Filter" (r: rep) (p: Packet) : rep * bool :=
            ret (r, (fail_if_all [
              weqb (port 22) p.(tcp_p).(DestPort) ;
              negb (weqb (domain_of p.(ip_h).(SourceAddress)) (domain_of p.(ip_h).(DestAddress)))
            ]))
    }%methDefParsing.


(* Allow FTP transfers from domain 3 to domains 1 and 2, but disallow FTP transfers from 1 and 2 to 3 *)
(* assuming this means domain 3 cannot initiate any FTP requests in 1 and 2 *)
(* --> if dst-port == 21 and src-domain == 3 and dst-domain == 1 or 2, fail, else pass *)
Definition Trusted21FilterSpec : ADT FilterSig :=
    Eval simpl in Def ADT {
        rep := QueryStructure PacketHistorySchema,
        Def Constructor0 "Init" : rep := empty,,

        Def Method1 "Filter" (r: rep) (p: Packet) : rep * bool :=
            ret (r, (fail_if_all [
              (weqb (p.(tcp_p).(DestPort)) (port 21)) ;
              (weqb (domain_of (p.(ip_h).(SourceAddress))) (domain 130)) ;
              (fail_if_any [
                (weqb (domain_of (p.(ip_h).(DestAddress))) (domain 110)) ;
                (weqb (domain_of (p.(ip_h).(DestAddress))) (domain 120))
              ])
            ]))
    }%methDefParsing.
*)

Record SimplePacket := 
  { id: nat }.

Definition SimpleFilterSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "Filter" : rep * SimplePacket -> rep * bool
  }.

Definition SimplePacketHistorySchema :=
  Query Structure Schema
    [ relation sHISTORY has
              schema < sPACKET :: SimplePacket > ]
      enforcing [].



Definition isIDHighest (r: QueryStructure SimplePacketHistorySchema) (p: SimplePacket) : Comp bool :=
(*     vals <- For (pac in r!sHISTORY) Return ((pac!sPACKET).(id)); *)
    { h: bool | decides h (forall pac, IndexedEnsemble_In ((DropQSConstraints r)!sHISTORY)%QueryImpl pac
        -> lt (pac!sPACKET).(id) p.(id)) }.

(* rephrase with Ensembles predicate, finiteness not necessary *)


Definition IncrementIDFilterSpec : ADT SimpleFilterSig :=
    Eval simpl in Def ADT {
        rep := QueryStructure SimplePacketHistorySchema,
        Def Constructor0 "Init" : rep := empty,,

        Def Method1 "Filter" (r: rep) (p: SimplePacket) : rep * bool :=
            isHighest <- isIDHighest r p;
            `(r, _) <- Insert (< sPACKET :: p >) into r!sHISTORY;
            ret (r, isHighest)
    }%methDefParsing.


Theorem SharpenedIncrementIDFilter:
  FullySharpened IncrementIDFilterSpec.
Proof.

  Definition repHighestID (oldrep: QueryStructure SimplePacketHistorySchema) (newrep: option nat) :=
    match newrep with
    | Some n =>
      (forall pac, IndexedEnsemble_In (((DropQSConstraints oldrep)!sHISTORY)%QueryImpl) pac -> le (pac!sPACKET).(id) n)
      /\ (exists pac, IndexedEnsemble_In (((DropQSConstraints oldrep)!sHISTORY)%QueryImpl) pac /\ (pac!sPACKET).(id) = n)
    | None => oldrep = QSEmptySpec SimplePacketHistorySchema
    end.
  
  Lemma isIDHighestCompute:
    forall r_o r_n p, (repHighestID r_o r_n) ->
      computes_to (isIDHighest r_o p)
        (match r_n with
         | Some n => (Nat.ltb n p.(id))
         | None => true
         end).
  Proof.
    intros. destruct r_n.
    - eapply PickComputes. unfold decides, If_Then_Else.
      destruct (n <? id p) eqn:rnpid. 
      + intros. apply H in H0. apply Nat.ltb_lt in rnpid. intuition.
      + unfold not. intros. destruct H. apply Nat.ltb_ge in rnpid.
        assert (Hp: forall pac: RawTuple,
          IndexedEnsemble_In ((DropQSConstraints r_o)!sHISTORY)%QueryImpl pac ->
          (lt (id pac!sPACKET) n)). { intros. apply H0 in H2. apply (Nat.lt_le_trans _ _ _ H2 rnpid). }
        destruct H1 as [pac Hpac]. specialize (Hp pac). destruct Hpac as [HpacIn Hpacn].
        rewrite Hpacn in Hp. apply Hp, Nat.lt_neq in HpacIn. apply HpacIn. reflexivity.
    - eapply PickComputes. unfold decides, If_Then_Else. unfold repHighestID in H. subst.
      intros. unfold QSEmptySpec in H. compute in H. destruct H. inversion H.
  Qed.

  Lemma isIDHighestRefine:
    forall r_o r_n p, (repHighestID r_o r_n) ->
      refine (isIDHighest r_o p)
        (ret match r_n with
            | Some n => (Nat.ltb n p.(id))
            | None => true
            end).
  Proof.
    intros. unfold refine in *. intros. computes_to_inv. subst. apply isIDHighestCompute, H.
  Qed.

(*  Definition findHighestID (r_o: UnConstrQueryStructure SimplePacketHistorySchema) : option nat.
    unfold UnConstrQueryStructure in r_o.
    pose (ilist2_hd r_o). simpl in y. Transparent RawUnConstrRelation. unfold RawUnConstrRelation in y. Check y!sPACKET.*)

  start sharpening ADT.
(*  hone representation using (@DropQSConstraints_AbsR SimplePacketHistorySchema); try simplify with monad laws; unfold refine.
  - intros. computes_to_econstructor. unfold DropQSConstraints_AbsR. unfold DropQSConstraints. simpl. Transparent computes_to. apply H0.
  - intros. computes_to_econstructor. apply isIDHighestCompute.*)

    
    hone representation using repHighestID; unfold repHighestID in *.
  - simplify with monad laws. refine pick val (@None nat). subst H. reflexivity. reflexivity.
  - simplify with monad laws. unfold refine. intros. computes_to_econstructor. apply isIDHighestCompute. apply H0. repeat computes_to_econstructor.
Abort.

(*
Definition SYNFloodFilterSpec : ADT FilterSig :=
    Eval simpl in Def ADT {
        rep := QueryStructure PacketHistorySchema,
        Def Constructor0 "Init" : rep := empty,,

        Def Method1 "Filter" (r: rep) (p: Packet) : rep * bool :=
            src_addr <- ret p.(ip_h)!SourceAddress;
            dst_addr <- ret p.(ip_h)!DestAddress;
            src_port <- ret p.(tcp_p)!SourcePort;
            dst_port <- ret p.(tcp_p)!DestPort;
            conns <- Count (For (pac in r!sHISTORY)
                            Where (src_addr = pac.(ip_h)!SourceAddress)
                            Where (dst_addr = pac.(ip_h)!DestAddress)
                            Where (dst_port = pac.(tcp_p)!DestPort)
                            Return ())
    }%methDefParsing.*)


(* spec a filter that ensures every packet has a higher id than previous
   specify concretely how we are ensuring this: get/put +1 *)
(* spec a filter for example #3 from email *)
(* break down master_plan and try to sharpen filter -- write a tactic, read master_plan *)
