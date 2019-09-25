Require Import
    Fiat.Narcissus.Examples.NetworkStack.IPv4Header
    Fiat.Narcissus.Examples.NetworkStack.TCP_Packet
    Bedrock.Word
    Coq.Arith.Arith
    Coq.Lists.List
    Fiat.QueryStructure.Automation.MasterPlan
    IndexedEnsembles
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
  iptables -A FORWARD --source 18'0'0'0/24
           --destination (Build_address_spec dst (mask_of_nat 32)).

Definition OutgoingToRule' (cur pre : input) : Prop :=
  (OutgoingToRule cur.(in_ip4).(SourceAddress)).(cf_cond) pre = true.

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
Theorem DroppedFilterMethod : FilterAdapter (@FilterMethod).
Proof. solve_drop_fields @FilterMethod. Defined.
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
