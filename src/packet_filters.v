Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header.
Require Import Fiat.Narcissus.Examples.NetworkStack.TCP_Packet.
Require Import Bedrock.Word.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import IndexedEnsembles.
Require Import Fiat.Narcissus.Examples.Guard.IPTables.
Require Import Fiat.Narcissus.Examples.Guard.PacketFiltersLemmas.

Definition sINPUT := "Input".
Definition sHISTORY := "GlobalHistory".
Definition PacketHistorySchema :=
  Query Structure Schema
        [ relation sHISTORY has
                   schema < sINPUT :: input > ]
        enforcing [].
Definition myqidx:
  Fin.t (numRawQSschemaSchemas PacketHistorySchema).
  cbn. apply Fin.F1. Defined.

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

Definition LessHistoryRelation (r_o r_n : UnConstrQueryStructure PacketHistorySchema) :=
  forall inp,
    (OutgoingRule.(cf_cond) inp) ->
    ((IndexedEnsemble_In (GetUnConstrRelation r_n Fin.F1) < sINPUT :: inp >)
     <-> IndexedEnsemble_In (GetUnConstrRelation r_o Fin.F1) < sINPUT :: inp >).

Lemma LessHistoryPreservesFilter:
  forall inp r_o r_n,
    LessHistoryRelation r_o r_n ->
    refine
      (FilterMethod_UnConstr r_o inp)
      (FilterMethod_UnConstr r_n inp).
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


Definition UnConstrQuery_In {ResultT}
           {qsSchema}
           (qs : UnConstrQueryStructure qsSchema)
           (R : Fin.t _)
           (bod : RawTuple -> Comp (list ResultT))
  := QueryResultComp (GetUnConstrRelation qs R) bod.

Notation "( x 'in' r '%' Ridx ) bod" :=
  (let qs_schema : QueryStructureSchema := _ in
   let r' : UnConstrQueryStructure qs_schema := r in
   let Ridx' := ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames qs_schema) Ridx%string _)) in
   @UnConstrQuery_In _ qs_schema r' Ridx'
            (fun x : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx') => bod)) (at level 0, x at level 200, r at level 0, bod at level 0).

Definition FilterMethod_UnConstr_Comp (r: UnConstrQueryStructure PacketHistorySchema) (inp: input) : Comp (option result) :=
  if cf_cond OutgoingRule inp then ret (Some ACCEPT) else
  if negb (cf_cond IncomingRule inp) then ret None else
    c <- Count (For (t in r%sHISTORY)
                Where (cf_cond (OutgoingToRule (SourceAddress (in_ip4 inp))) (t!sINPUT))
                Return ());
    if 0 <? c then ret (Some ACCEPT) else ret (Some DROP).


Lemma permutation_length {A: Type}:
  forall (l1 l2 : list A),
    Permutation l1 l2 -> Datatypes.length l1 = Datatypes.length l2.
Proof.
  intros. induction H; simpl; congruence.
Qed.


(*
 H1 : fold_right
         (fun b a : Comp (list ()) =>
          l <- b;
          l' <- a;
          ret (l ++ l')%list) (ret [])
         (map
            (fun t : RawTuple =>
             {l : list () |
             (P t -> ret [()] ↝ l) /\ (~ P t -> l = [])}) ltup) l' *)

Lemma fold_comp_list_length:
  forall l l',
    fold_right
      (fun b a : Comp (list ()) =>
         l <- b;
         l' <- a;
         ret (l ++ l')%list) (ret [])
      l' l ->
    0 <? Datatypes.length l ->
    exists lin, List.In lin l' /\
                (exists lin', lin lin' /\ 0 <? Datatypes.length lin').
Proof.
  intros l l'. generalize dependent l. induction l'.
  - simpl. intros. inversion H. subst l. inversion H0.
  - simpl. intros. destruct H as [l1 [Hl1 Hl]]. red in Hl1. red in Hl.
    destruct Hl as [l2 [Hl2 Hl]]. red in Hl2. red in Hl. inversion Hl.
    destruct (0 <? Datatypes.length l2) eqn:Hlen2.
    * pose proof (IHl' l2 Hl2 Hlen2) as IH.
      destruct IH as [lin [Hlin1 Hlin2]]. exists lin. split.
      right; assumption. assumption.
    * apply Nat.ltb_ge in Hlen2. inversion Hlen2. rewrite <- H in H0.
      rewrite app_length in H0. rewrite H2 in H0. rewrite Nat.add_0_r in H0.
      exists a. split.
      left; reflexivity. exists l1. split. assumption. rewrite H2. apply H0.
Qed.

Lemma count_zero_iff:
  forall (r: UnConstrQueryStructure PacketHistorySchema)
         (P: @RawTuple _ -> bool) count,
    computes_to (Count (For (UnConstrQuery_In r myqidx
                        (fun t =>
                          Where (P t)
                          Return ())))) count ->
    ((0 <? count) <-> (exists inp, IndexedEnsemble_In (GetUnConstrRelation r myqidx) < sINPUT :: inp > /\ P < sINPUT :: inp >)).
Proof.
  Transparent Query_For. Transparent Count.
  unfold Count, Query_For, Query_Where, Query_Return, UnConstrQuery_In.
  Transparent QueryResultComp. unfold QueryResultComp, FlattenCompList.flatten_CompList.
  intros r P count Hcount. destruct Hcount as [l [Hcount Htmp]].
  unfold In in *. inversion Htmp. clear Htmp.
  destruct Hcount as [l' [Htmp Hperm]]. apply Pick_inv in Hperm.
  unfold In in *. destruct Htmp as [ltup [Hrel Hfold]].
  apply Pick_inv in Hrel. unfold In in *.
  pose proof (permutation_length l' l Hperm) as Hpermlen.
  rewrite <- Hpermlen in *. clear Hperm. clear Hpermlen. clear l.
  generalize dependent r. generalize dependent l'. induction ltup.

  - intros l Hfold Hcount r Hrel.
    simpl in Hfold. inversion Hfold. subst l.
    split; intros. inversion H.
    destruct H as [inp [Hinp1 Hinp2]]. red in Hinp1.
    destruct Hinp1 as [idx Hinp1]. unfold In in Hinp1.
    unfold UnIndexedEnsembleListEquivalence in Hrel.
    destruct Hrel as [l [Hmap [Heql Hdup]]]. apply Heql in Hinp1.
    assert (Hmapnil: forall (A B : Type) (l: list A) (f: A -> B),
               map f l = [] -> l = []).
    { intros. destruct l0. reflexivity. simpl in H. inversion H. }
    apply Hmapnil in Hmap. subst l. inversion Hinp1.

  - intros l Hfold Hcount r Hrel.
    simpl in Hfold. destruct Hfold as [lp [Hp Hfold]]. unfold In in *.
    inversion Hp. clear Hp.
    assert (H0': P a -> lp = [()]) by (intros H0'; apply H in H0';
                                       apply Return_inv in H0';
                                       symmetry; assumption).
    clear H.
    destruct Hfold as [lp' [Hfold Happ]]. unfold In in *. inversion Happ.
    clear Happ. rename H into Happ. split; intros.

    * rewrite app_length in H.
      unfold UnIndexedEnsembleListEquivalence in Hrel.
      destruct Hrel as [l' [Hmap [Heql Hdup]]].
      destruct (P a) eqn:Hpa.
    + unfold attrType.
      assert (Hmapex: forall (A B : Type) (l: list A) (f: A -> B) (a: B) a',
                 map f l = a :: a' -> exists b, f b = a /\ List.In b l).
      { intros. destruct l0. inversion H1. simpl in H1. inversion H1.
        exists a1. split. reflexivity. left. reflexivity. }
      pose proof (Hmapex _ _ l' _ a _ Hmap). destruct H1 as [b [Hb Hb']].

      (*exists (indexedElement b). split. red. exists (elementIndex b).
      unfold In. apply Heql.
      assert (Hbb: {| elementIndex := elementIndex b;
                      indexedElement := indexedElement b |} = b).
      { destruct b. reflexivity. }
      rewrite Hbb. apply Hb'. rewrite Hb. apply Hpa.
    + rewrite H0 in H. simpl in H. rewrite Nat.add_0_l in H.
      destruct l' as [|h' tl']. inversion Hmap.
      pose (EnsembleDelete (GetUnConstrRelation r myqidx)
                           (Singleton _ (indexedElement h'))) as r'.
      assert (Hrel: UnIndexedEnsembleListEquivalence
                       (GetUnConstrRelation r myqidx) (a :: ltup)).
      { red. exists (h' :: tl'). split. assumption. split; assumption. }

      assert (Hrel': UnIndexedEnsembleListEquivalence r' ltup).
      { red. exists tl'. split.
        inversion Hmap. reflexivity.
        split. split; intros.
        - inversion H1. apply Heql in H2. destruct H2 as [H2 | H2].
          * subst x. cbv in H3. exfalso. apply H3. reflexivity.
          * assumption.
        - red. subst r'. cbv. constructor. cbv.
          assert (Ht: (GetUnConstrRelation r myqidx) x).
          { apply Heql. simpl; right; assumption. }
          apply Ht.
          cbv. intros. inversion H2. destruct x as [xind xelem].
          destruct h' as [hind helem]. subst. admit.
        - inversion Hdup. assumption. }

      assert (Hd: Datatypes.length lp' = count).
      { rewrite <- Happ in Hcount.
      rewrite app_length in Hcount. rewrite H0 in Hcount.
      rewrite Nat.add_0_l in Hcount. apply Hcount. congruence. }
      Check IHltup.
      pose proof (IHltup lp' Hfold Hd ({| prim_fst := r'; prim_snd := () |}) Hrel').*)
Admitted.

Lemma CompPreservesFilterMethod:
  forall r inp,
    refine (FilterMethod_UnConstr r inp)
           (FilterMethod_UnConstr_Comp r inp).
Proof.
  unfold FilterMethod_UnConstr, FilterMethod_UnConstr_Comp. red; intros.
  destruct (cf_cond OutgoingRule inp) eqn:outrule. assumption.
  destruct (negb (cf_cond IncomingRule inp)) eqn:inrule. assumption.
  inversion H as [c Hc]. destruct Hc as [Hcount Hres]. unfold In in *.

  pose proof (count_zero_iff _ _ c Hcount) as Hcziff.
  computes_to_econstructor. computes_to_econstructor.
  instantiate (1:=(0 <? c)). red. destruct (0 <? c) eqn:Hzero; simpl.
  - rewrite <- Hzero in Hcziff. apply Hcziff in Hzero.
    destruct Hzero as [pre [Hin Hcond]].
    exists pre. split; assumption.
  - intro. rewrite <- Hzero in Hcziff. apply Hcziff in H0. inversion H0.
    rewrite H2 in Hzero. inversion Hzero.
  - apply Hres.
Qed.


Lemma LessHistoryRelationRefl:
  forall r_o, LessHistoryRelation r_o r_o.
Proof.
  unfold LessHistoryRelation; split; intros; assumption. Qed.


Theorem SharpenNoIncomingFilter:
  FullySharpened NoIncomingConnectionsFilter.
Proof.
  start sharpening ADT. Transparent QSInsert.
  drop_constraints_under_bind PacketHistorySchema ltac:(
    intro v; intros Htemp;
    match goal with
      [H: DropQSConstraints_AbsR _ _ |- _] =>
      apply (UnConstrPreservesFilterMethod _ _ _ _ H)
    end;
    apply Htemp).

  hone_finite_under_bind PacketHistorySchema myqidx.

  hone representation using (fun r_o r_n => LessHistoryRelation (projT1 r_o) (projT1 r_n));
    try simplify with monad laws.
  - refine pick val
      (existT _ (DropQSConstraints (QSEmptySpec _)) QSEmptyIsFinite).
    subst H; reflexivity. apply LessHistoryRelationRefl.
  - etransitivity. eapply refine_bind.
    eapply LessHistoryPreservesFilter. apply H0.
    intros res Hres. cbn. eapply refine_bind.

    Definition RefinedInsert
               (r: sigT (@AllFinite PacketHistorySchema)) d :=
      existT AllFinite (UpdateUnConstrRelation (projT1 r) Fin.F1
                                               (EnsembleInsert
                                                  {| elementIndex := IncrMaxFreshIdx r;
                                                     indexedElement := icons2 d inil2 |}
                                                  (GetUnConstrRelation (projT1 r) Fin.F1)))
             (insert_finite_helper r Fin.F1
                                   {| elementIndex := IncrMaxFreshIdx r;
                                      indexedElement := icons2 d inil2 |}
                                   (IncrMaxFreshIdx_Prop r)).
    
    refine pick val
           (if cf_cond OutgoingRule d
            then (RefinedInsert r_n d)
            else r_n).
    higher_order_reflexivity.

    destruct (cf_cond OutgoingRule d) eqn:outrule.
    red; intros inp Hinp. unfold RefinedInsert. split; intros.

    cbn in H1. rewrite get_update_unconstr_eq in H1. red in H1. destruct H1. destruct H1.
    { exists (@IncrMaxFreshIdx _ myqidx r_o). cbn. red. rewrite get_update_unconstr_eq. red. left. inversion H1. reflexivity. }
    { cbn. rewrite get_update_unconstr_eq. red. unfold In. unfold EnsembleInsert. pose proof (H0 inp Hinp). unfold IndexedEnsemble_In in H2. unfold In in H2. assert (Hm: exists idx, GetUnConstrRelation (projT1 r_o) Fin.F1 {| elementIndex := idx; indexedElement := icons2 (value (ilist2_hd (icons2 (sINPUT :: inp)%Component inil2))) inil2 |}). { apply H2. exists x. apply H1. } destruct Hm. exists x0. right. apply H3. }

    cbn in H1. rewrite get_update_unconstr_eq in H1. red in H1. destruct H1. destruct H1.
    { exists (@IncrMaxFreshIdx _ myqidx r_n). cbn. red. rewrite get_update_unconstr_eq. red. left. inversion H1. reflexivity. }
    { cbn. rewrite get_update_unconstr_eq. red. unfold In. unfold EnsembleInsert. pose proof (H0 inp Hinp). unfold IndexedEnsemble_In in H2. unfold In in H2. assert (Hm: exists idx, GetUnConstrRelation (projT1 r_n) Fin.F1 {| elementIndex := idx; indexedElement := icons2 (value (ilist2_hd (icons2 (sINPUT :: inp)%Component inil2))) inil2 |}). { apply H2. exists x. apply H1. } destruct Hm. exists x0. right. apply H3. }

    red; intros inp Hinp. split; intros.

    apply (H0 inp Hinp) in H1. cbn. rewrite get_update_unconstr_eq. red. red in H1. destruct H1. exists x. red. red. right. apply H1.

    cbn in H1; rewrite get_update_unconstr_eq in H1. red in H1. destruct H1. red in H1. red in H1. destruct H1. inversion H1. rewrite <- H4 in outrule. rewrite outrule in Hinp. inversion Hinp. apply (H0 inp Hinp). red; exists x; red. apply H1.


    red; intros. higher_order_reflexivity.
    simplify with monad laws. eapply refine_bind.
    reflexivity.
    red; intros. higher_order_reflexivity.

    
  - hone method "Filter"; try (simplify with monad laws; subst r_o).
    apply refine_bind.   
    apply CompPreservesFilterMethod.
    intro. eapply refine_bind. simpl. refine pick eq. reflexivity.
    intro. simpl. higher_order_reflexivity.


    hone representation using (fun r_o r_n => DelegateToBag_AbsR (projT1 r_o) r_n).
    * simplify with monad laws. unfold DelegateToBag_AbsR. simpl.
      Check GetIndexedRelation.
      Search DelegateToBag_AbsR.
    Locate finish_planning'.


    eapply FullySharpened_Finish.

    pose_headings_all.
    Set Printing Implicit.
    match goal with
      | |- context[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
      FullySharpenQueryStructure Schema Indexes
    end.


        
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
