Require Import Coq.Strings.String.
Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.Common.List.UpperBound.

Open Scope list.

(* This is an internet packet classifier example. We model a packet with its ip address and
   network protocol. The ADT has one relation (table) named [Rules], which contains classification rules *)

Section Packet.
  (* an Ip address is a list of ascii each of which represents a group *)
  Definition Ip := list ascii.

  (* a Protocol can be either tcp or udp *)
  Inductive Protocol := tcp | udp.

  Lemma Protocol_dec : forall a b : Protocol, {a = b} + {a <> b}.
  Proof. decide equality. Qed.

  Global Instance Query_eq_Protocol :
    Query_eq Protocol := {| A_eq_dec := Protocol_dec |}.

  (* a Policy of P is either enforcing some constant P, or accepting any *)
  Section Packet_Protocol.
    Variable (P : Type).
    Context {P_eq_dec : Query_eq P}.

    Inductive Policy :=
    | enforce : P -> Policy
    | wildcard.

    Definition FollowPolicy (p : Policy) (s : P) :=
      match p with
        | enforce p' => p' = s
        | wildcard => True
      end.

    Definition FollowPolicy_dec (p: Policy) (s : P) : {FollowPolicy p s} + {~ FollowPolicy p s}.
      refine (match p with
                | enforce p' =>
                  if A_eq_dec p' s then
                    left _
                  else
                    right _
                | wildcard => left _
              end); simpl; intuition eauto. Defined.

    Global Instance DecideableFollowPolicy {T} (f : T -> Policy) {n}
    : DecideableEnsemble (fun tup => FollowPolicy (f tup) n) :=
      {| dec n' :=  ?[FollowPolicy_dec (f n') n] |}. intuition; find_if_inside; intuition. Defined.
  End Packet_Protocol.

  (* a Packet consists of Ip and Protocol *)
  Record Packet :=
    { destination : Ip;
      protocol : Protocol }.

  (* a Response of a query can be accept, deny, or uncertain *)
  Inductive Response := Accept | Deny | Uncertain.
End Packet.

Section ADT.
  (* Rule schema *)
  Definition RULES := "Rules".
  Definition PRIORITY := "Priority".
  Definition DESTINATION := "Destination".
  Definition PROTOCOL := "Protocol".
  Definition ACTION := "Action".

  Definition RuleRecord :=
    @Tuple <PRIORITY :: nat,
            DESTINATION :: Ip,
            PROTOCOL :: Policy Protocol,
            ACTION :: bool>%Heading.

  Definition ClassifierSchema :=
  Query Structure Schema
        [ relation RULES has
                   schema <PRIORITY :: nat,
                           DESTINATION :: Ip,
                           PROTOCOL :: Policy Protocol,
                           ACTION :: bool> ]
        enforcing [ ].

  Definition ClassifierSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddRule" : rep x RuleRecord -> rep x bool,
      Method "DeletePrefix" : rep x Ip -> rep x list RuleRecord,
      Method "Classify" : rep x Packet -> rep x list RuleRecord
    }.

  Definition ClassifierSpec : ADT ClassifierSig :=
  QueryADTRep ClassifierSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddRule" (r : RuleRecord) : bool :=
      Insert r into RULES,

    update "DeletePrefix" (ip : Ip) : list RuleRecord :=
      Delete r from RULES where IsPrefix r!DESTINATION ip,

    query "Classify" (p : Packet) : list RuleRecord :=
      For (r in RULES)
            (* the rule's ip must be a prefix of the packet's ip *)
            Where (IsPrefix r!DESTINATION (destination p) /\
            (* the rule's protocol must match the packet's protocol *)
                   FollowPolicy r!PROTOCOL (protocol p))
            Return r
  }.

  Theorem ClassifierManual :
    MostlySharpened ClassifierSpec.
  Proof.

    partial_master_plan ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics).

    FullySharpenQueryStructure ClassifierSchema Index.

  (* 124 seconds *)
  Time Defined.

  Definition ClassifierImpl : SharpenedUnderDelegates ClassifierSig.
    (* 33 seconds *)
    Time let Impl := eval simpl in (projT1 ClassifierManual) in
             exact Impl.
  Defined.

End ADT.
