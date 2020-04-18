Require Import Fiat.QueryStructure.Automation.MasterPlan.

Open Scope list_scope.

(* This is an internet packet classifier example. We model a packet with its ip address and
   network protocol. The ADT has one relation (table) named [Rules], which contains classification rules *)

Section Packet.
  (* an Ip address is a list of ascii each of which represents a group *)
  Definition Ip := list nat.

  (* a Protocol can be either tcp or udp *)
  Inductive Protocol := tcp | udp.

  Lemma Protocol_dec : forall a b : Protocol, {a = b} + {a <> b}.
  Proof. decide equality. Defined.

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
      Constructor "Init" : rep,
      Method "AddRule" : rep * RuleRecord -> rep * bool,
      Method "Classify" : rep * Packet -> rep * (list RuleRecord)
    }.

  Definition ClassifierSpec : ADT ClassifierSig :=
    Def ADT {
      rep := QueryStructure ClassifierSchema,

    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "AddRule" (r : rep) (rule : RuleRecord) : rep * bool :=
      Insert rule into r!RULES,

    Def Method1 "Classify" (r : rep) (p : Packet) : rep * list RuleRecord :=
      rules <- For (rule in r!RULES)
            (* the rule's ip must be a prefix of the packet's ip *)
            Where (IsPrefix rule!DESTINATION (destination p) /\
            (* the rule's protocol must match the packet's protocol *)
                   FollowPolicy rule!PROTOCOL (protocol p))
            Return rule;
      ret (r, rules)
  }.

  Theorem SharpenedClassifier :
    FullySharpened ClassifierSpec.
  Proof.

    (* Uncomment this to see the mostly sharpened implementation *)
    (* partial_master_plan ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics).*)

    master_plan ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics).

  Time Defined.

  Time Definition ClassifierImpl : ComputationalADT.cADT ClassifierSig :=
    Eval simpl in (projT1 SharpenedClassifier).

  Print ClassifierImpl.
  Print ADTImplRep.

End ADT.
