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

Definition NoIncomingConnectionsFilter : ADT StatefulFilterSig :=
  Eval simpl in Def ADT {
    rep := QueryStructure PacketHistorySchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "Filter" (r: rep) (inp: input) : rep * option result :=
      res <- FilterMethod r inp;
      `(r, _) <- Insert (< sINPUT :: inp >) into r!sHISTORY;
      ret (r, res)
  }%methDefParsing.

Definition LessHistoryRelation (r_o r_n : QueryStructure PacketHistorySchema) :=
  forall inp,
    (OutgoingRule.(cf_cond) inp) ->
    ((IndexedEnsemble_In (GetRelation r_n Fin.F1) < sINPUT :: inp >)
     <-> IndexedEnsemble_In (GetRelation r_o Fin.F1) < sINPUT :: inp >).

Lemma LessHistoryPreservesFilter:
  forall inp r_o r_n val,
    LessHistoryRelation r_o r_n ->
    computes_to (FilterMethod r_o inp) val ->
    computes_to (FilterMethod r_n inp) val.
Proof.
  intros. unfold FilterMethod in *. unfold LessHistoryRelation in H.
  destruct (cf_cond OutgoingRule inp) eqn:outrule. apply H0.
  destruct (negb (cf_cond IncomingRule inp)) eqn:ninrule; simpl in *. apply H0.
  inversion H0. destruct H1. computes_to_econstructor. destruct x eqn:truefalse. assert (Hsol: computes_to { b: bool | decides b (exists pre: input, IndexedEnsemble_In (GetRelation r_n Fin.F1) (icons2 pre inil2) /\ cf_cond (OutgoingToRule (SourceAddress (in_ip4 inp))) pre = true) } true).
  { computes_to_econstructor. unfold decides; simpl. destruct H1. destruct H1. exists x0. split. apply (H x0). apply (OutgoingToImpliesOutgoing x0 (SourceAddress (in_ip4 inp))). apply H3. apply H1. apply H3. } apply Hsol.
  computes_to_econstructor; unfold decides; simpl. unfold not; intros. destruct H1. destruct H3. destruct H1. exists x0. split. apply (H x0). apply (OutgoingToImpliesOutgoing x0 (SourceAddress (in_ip4 inp))). apply H3. apply H1. apply H3.
  apply H2.
Qed.


Lemma LessHistoryRelationRefl:
  forall r_o, LessHistoryRelation r_o r_o.
Proof.
  unfold LessHistoryRelation; split; intros; assumption. Qed.

Lemma SimplInBind:
  forall (T U: Type) (x v : T) (y: U),
    In T (`(r', _) <- ret (x, y); ret r') v -> x = v.
Proof.
  intros. apply Bind_inv in H. destruct H. destruct H. apply Return_inv in H. rewrite <- H in H0. simpl in H0. apply Return_inv in H0. assumption. Qed.

Print FiniteTables_AbsR. Check QSInsertSpec_refine_opt.

Print LessHistoryRelation.

Lemma InsertIfOutgoingRefinesFilter:
  forall (r_o: QueryStructure PacketHistorySchema) d,
    refine
      (r <- QSInsert r_o Fin.F1 (icons2 d inil2);
       {r_n0 : QueryStructure PacketHistorySchema |
            LessHistoryRelation (fst r) r_n0})
      (r <- if cf_cond OutgoingRule d
                  then QSInsert r_o Fin.F1 (icons2 d inil2)
                  else ret (r_o, true);
       ret (fst r)).
Proof.
  intros. destruct (cf_cond OutgoingRule d) eqn:outd; unfold refine; intros.
  - inversion H. destruct H0. computes_to_econstructor. apply H0. computes_to_econstructor. rewrite H1. apply LessHistoryRelationRefl.
  - pose proof (SimplInBind _ _ r_o v _ H). rewrite <- H0. subst. computes_to_econstructor. apply QSInsertSpec_refine_opt. simpl. computes_to_econstructor. unfold UnConstrFreshIdx. computes_to_econstructor. intros. Admitted.
    


Theorem SharpenNoIncomingFilter:
  FullySharpened NoIncomingConnectionsFilter.
Proof.
  start sharpening ADT.
  hone representation using LessHistoryRelation; try simplify with monad laws.
  - refine pick val (QSEmptySpec PacketHistorySchema). unfold refine. intros. Transparent computes_to. apply H0. unfold LessHistoryRelation. intros. split; intros; inversion H1; inversion H2.
  - unfold Bind2. simplify with monad laws. cbn. Check InsertIfOutgoingRefinesFilter.
    


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
