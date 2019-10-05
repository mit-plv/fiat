Require Import
    Fiat.Narcissus.Examples.NetworkStack.IPv4Header
    Fiat.Narcissus.Examples.NetworkStack.TCP_Packet
    Bedrock.Word
    Coq.Arith.Arith
    Coq.Lists.List
    Fiat.QueryStructure.Automation.MasterPlan
    IndexedEnsembles
    Fiat.Narcissus.Examples.Guard.Core
    Fiat.Narcissus.Examples.Guard.IPTables
    Fiat.Narcissus.Examples.Guard.PacketFiltersLemmas
    Fiat.Narcissus.Examples.Guard.DropFields.
Import ListNotations.

(* TODO: Add a proper makefile target *)

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
  and_cf OutgoingRule (lift_condition in_ip4 (cond_dstaddr {| saddr := dst; smask := None |})).

Definition OutgoingToRule' (cur pre : input) : Prop :=
  (OutgoingToRule cur.(in_ip4).(ipv4_source)).(cf_cond) pre = true.

Opaque OutgoingRule IncomingRule OutgoingToRule OutgoingToRule'.

Definition FilterMethodGen {h T} cont
           (topkt: @Tuple h -> input)
           (totup: input -> @Tuple h)
           (r: T) (inp: input) :=
  If OutgoingRule.(cf_cond) inp
  Then <ACCEPT>
  Else (
      If negb (IncomingRule.(cf_cond) inp)
      Then ret None
      Else with r (cont totup),
                if historically (OutgoingToRule' inp) then <ACCEPT> else <DROP>).
Definition FilterMethod: FilterType. filter_gen @FilterMethodGen. Defined.
Definition FilterMethod_Count: FilterType. filter_count FilterMethod. Defined.

Transparent computes_to.

Notation IndexType sch :=
  (@ilist3 RawSchema (fun sch : RawSchema =>
                        list (string * Attributes (rawSchemaHeading sch)))
           (numRawQSschemaSchemas sch) (qschemaSchemas sch)).

(* This computes the set of columns to keep *)
Theorem DroppedFilterMethod : FilterAdapter (@FilterMethod).
Proof. solve_drop_fields @FilterMethod. Defined.

Definition IPFilterSchema :=
  Eval cbn in PacketHistorySchema (DroppedFilterMethod.(h _)).

(** Genpatcher hooks here **)

(* ‘columns’ is the list of columns available; this will vary depending on the filter *)

Definition columns :=
  Eval compute in (Vector.to_list (DroppedFilterMethod.(h _).(HeadingNames))).

Print columns.
(* columns = ["Chain"; "TransportLayerPacket"; "DestAddress"; "SourceAddress"]%list
     : list string *)

Open Scope list_scope.

(* Here are two examples *)

Definition SlowIndex : IndexType IPFilterSchema :=
  {| prim_fst := [];
     prim_snd := () |}.

Definition FastIndex :=
  {| prim_fst := [("EqualityIndex", "DestAddress" # "History" ## IPFilterSchema)]%list;
     prim_snd := () |}.

(* Genpatcher should mutate the following definition: *)
Definition Index : IndexType IPFilterSchema :=
  {| prim_fst := [];
     prim_snd := () |}.

(** End of GenPatcher hooks **)

Definition myh := (h _ DroppedFilterMethod).
Definition mytopkt := (topkt _ DroppedFilterMethod).
Definition mytotup := (totup _ DroppedFilterMethod).
Definition mythm := (thm _ DroppedFilterMethod).

Lemma CompPreservesFilterMethod:
  forall r inp,
    refine (FilterMethod myh mytopkt mytotup r inp)
           (FilterMethod_Count myh mytopkt mytotup r inp).
Proof. prove_count_refine. Qed.


Definition NoIncomingConnectionsFilter : ADT StatefulFilterSig :=
  Eval simpl in Def ADT {
    rep := QueryStructure Complete_PacketHistorySchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "Filter" (r: rep) (inp: input) : rep * option result :=
      res <- FilterMethodGen In_History_Constr Complete_topkt Complete_totup r inp;
      `(r, _) <- Insert (Complete_totup inp) into r!"History";
      ret (r, res)
  }%methDefParsing.

Ltac FindAttributeUses := EqExpressionAttributeCounter.
Ltac BuildEarlyIndex := ltac:(LastCombineCase6 BuildEarlyEqualityIndex).
Ltac BuildLastIndex := ltac:(LastCombineCase5 BuildLastEqualityIndex).
Ltac IndexUse := EqIndexUse.
Ltac createEarlyTerm := createEarlyEqualityTerm.
Ltac createLastTerm := createLastEqualityTerm.
Ltac IndexUse_dep := EqIndexUse_dep.
Ltac createEarlyTerm_dep := createEarlyEqualityTerm_dep.
Ltac createLastTerm_dep := createLastEqualityTerm_dep.
Ltac BuildEarlyBag := BuildEarlyEqualityBag.
Ltac BuildLastBag := BuildLastEqualityBag.
Ltac PickIndex := ltac:(fun makeIndex => let attrlist' := eval compute in FastIndex in makeIndex attrlist').

Arguments wand: simpl never.
Arguments Nat.ltb: simpl never.
Arguments N.land: simpl nomatch.
Arguments chain_beq: simpl never.
Arguments GetAttribute: simpl never.
Hint Unfold cf_cond combine_conditions cond_srcaddr cond_dstaddr cond_chain match_address : iptables.

(* Hint Rewrite -> wand_full_mask : iptables. *)
Hint Rewrite -> andb_true_iff andb_true_l andb_true_r : iptables.
Hint Rewrite -> internal_chain_dec_bl : iptables.
Hint Rewrite -> N.eqb_eq : iptables.
Hint Rewrite -> weqb_true_iff : iptables.

Theorem SharpenNoIncomingFilter:
  FullySharpened NoIncomingConnectionsFilter.
Proof.
  start sharpening ADT.

  Transparent QSInsert.
  drop_constraints_under_bind Complete_PacketHistorySchema ltac:(
    instantiate (1:=(FilterMethodGen In_History Complete_topkt Complete_totup r_n d));
    unfold FilterMethodGen; red; intros v Hv; red in Hv; red;

    repeat match goal with
    | [H: (If _ Then _ Else _) v |- (If ?cond Then _ Else _) v] =>
      destruct cond; [ apply H | cbn; cbn in H ]
    | [Hv: _ v |- _ v] => repeat comp_inv; apply Pick_inv in H1;
                          repeat computes_to_econstructor; [ | eassumption ]
    | [H: decides ?b _ |- _] => destruct b; cbn in *
    | [H: exists pre, ?A /\ ?B |- exists _, _ /\ _] =>
      destruct H as [pre [Ha Hb]]; exists pre; split; [ | assumption ]
    | [Hrel: DropQSConstraints_AbsR ?r_o ?r_n, Hhist: In_History _ _ _ |- _] =>
      unfold In_History, In_History_Constr, GetRelationBnd, GetUnConstrRelationBnd in *;
      rewrite <- (GetRelDropConstraints r_o); rewrite <- Hrel in Hhist; apply Hhist
    | [H: ~ _ |- ~ _] => intro; apply H
    | [Hrel: DropQSConstraints_AbsR ?r_o ?r_n, Hhist: In_History_Constr _ _ _ |- _] =>
      unfold In_History; rewrite <- Hrel; red in Hhist; unfold GetRelationBnd in Hhist;
      rewrite <- (GetRelDropConstraints r_o) in Hhist; apply Hhist
    end).

  hone representation using (Complete_Dropped_qs_equiv mytotup);
    try simplify with monad laws;
  [ refine pick val (DropQSConstraints (QSEmptySpec _));
    [ subst H; reflexivity
    | red; intros; split; intros Htmp; cbv in Htmp; inversion Htmp]
  | eapply refine_bind; [ apply mythm; apply H0 | intro res; cbn ];
    eapply refine_bind; [ apply (DropPreservesFreshIdx _ _ _ mytotup H0)
                        | intro idx; cbn ];
    apply refine_pair; apply refine_pick; intros qs Hins; comp_inv; subst qs;
    instantiate (1 := (UpdateUnConstrRelation r_n Fin.F1
                         (BuildADT.EnsembleInsert
                            {| elementIndex := idx;
                               indexedElement := mytotup d |}
                            (GetUnConstrRelation r_n Fin.F1))));

    red; intros oinp oidx; split; intros Hoinp; destruct Hoinp as [Hoinp | Hoinp];
    [ apply in_ensemble_insert_iff; left; inversion Hoinp; reflexivity
    | right; apply H0 in Hoinp; apply Hoinp
    | exists d; split; [ apply in_ensemble_insert_iff; left | ];
      inversion Hoinp; reflexivity
    | pose proof (H0 oinp oidx) as H0spec;
      destruct H0spec as [_ Hspec]; specialize (Hspec Hoinp);
      destruct Hspec as [inp' [H1 H2]]; exists inp'; split;
      [ apply in_ensemble_insert_iff; right; apply H1 | apply H2 ]
    ]
  | ].


 - hone method "Filter".
   subst r_o; refine pick eq; simplify with monad laws;
   apply refine_bind; [ apply CompPreservesFilterMethod; reflexivity | intro ];
   apply refine_bind; [ reflexivity | intro; simpl; higher_order_reflexivity ].

   PickIndex ltac:(fun attrlist =>
                     make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex).

   + plan CreateTerm EarlyIndex LastIndex makeClause_dep EarlyIndex_dep LastIndex_dep.
   + etransitivity. simplify with monad laws.
     eapply refine_bind; [ | intro ].

     { (* Filter *)
       unfold FilterMethod_Count.
       repeat lazymatch goal with
              | [  |- refine (if _ then _ else _) _ ] => eapply refine_If_Then_Else
              | [  |- context[UnConstrQuery_In] ] => idtac
              | _ => higher_order_reflexivity
              end.

       Transparent OutgoingToRule OutgoingToRule' OutgoingRule.
       Hint Unfold OutgoingToRule OutgoingToRule' OutgoingRule : iptables.

       repeat (autounfold with iptables; cbn).

       etransitivity; [ setoid_rewrite refine_UnConstrQuery_In | ].
       { reflexivity. }
       { intro.
         etransitivity; [apply refine_Query_Where_Cond | ].
         { autorewrite with iptables.
           repeat match goal with
                  | _ => rewrite and_assoc
                  | [  |- context[chain_beq ?x ?y = true /\ ?z] ] => rewrite (and_comm (chain_beq x y = true) z)
                  end.
           rewrite <- !and_assoc.
           reflexivity. }
         { higher_order_reflexivity. } }

       implement_Query IndexUse createEarlyTerm createLastTerm
       IndexUse_dep createEarlyTerm_dep createLastTerm_dep.
       simplify with monad laws.

       simpl; repeat first [ setoid_rewrite refine_bind_unit
                           | setoid_rewrite refine_bind_bind ].
       apply refine_bind; [ reflexivity | intro; simpl ].
       repeat rewrite ?map_length, ?app_nil_r.
       higher_order_reflexivity. }

     { (* Insertion *)
       unfold mytotup; simpl.
       etransitivity.
       insertion IndexUse createEarlyTerm createLastTerm IndexUse_dep createEarlyTerm_dep createLastTerm_dep.
       simplify with monad laws.
       higher_order_reflexivity. }

     simpl.
     subst H.
     higher_order_reflexivity.

   + Implement_Bags BuildEarlyBag BuildLastBag.
Defined.

Definition GuardImpl :=
  Eval simpl in projT1 SharpenNoIncomingFilter.

Definition guard_init : ComputationalADT.cRep GuardImpl :=
  Eval simpl in (CallConstructor GuardImpl "Init").

Definition guard_process_packet (bs: input) (rep: ComputationalADT.cRep GuardImpl) : (_ * option result) :=
  Eval simpl in CallMethod GuardImpl "Filter" rep bs.
