Require Import Coq.Strings.String.
Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.QSImplementation.

Open Scope list.

(* This is an internet packet classifier example. We model a packet with its ip address and
   network protocol. The ADT has one relation (table) named [Rules], which contains classification rules *)

Section Packet.
  (* an Ip address is a list of ascii each of which represents a group *)
  Definition Ip := list nat.

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

  (* probably we should use typeclasses to solve this issue
  Definition priority_lt_dec :
          forall a b : RuleRecord, sumbool (b!PRIORITY <= a!PRIORITY) (~ b!PRIORITY <= a!PRIORITY)
    := rel_dec_comm _ (rel_dec_map _ le_dec (fun r : RuleRecord => r!PRIORITY)). *)

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

    update "AddRule" (r : rep, rule : RuleRecord) : bool :=
      Insert rule into r!RULES,

    update "DeletePrefix" (r : rep, ip : Ip) : list RuleRecord :=
      Delete rule from r!RULES where IsPrefix rule!DESTINATION ip,

    query "Classify" (r : rep, p : Packet) : list RuleRecord :=
      For (rule in r!RULES)
            (* the rule's ip must be a prefix of the packet's ip *)
            Where (IsPrefix rule!DESTINATION (destination p) /\
            (* the rule's protocol must match the packet's protocol *)
                   FollowPolicy rule!PROTOCOL (protocol p))
            Return rule
  }.

  Theorem ClassifierManual :
    FullySharpened ClassifierSpec.
  Proof.

    start_honing_QueryStructure.
    { GenerateIndexesForAll
        ltac:(CombineCase3 matchFindPrefixIndex matchEqIndex)
               ltac:(fun attrList =>
                       make_simple_indexes
                         attrList
                         ltac:(CombineCase6 BuildEarlyEqualityIndex
                                            ltac:(CombineCase6 BuildEarlyFindPrefixIndex
                                                               ltac:(fun _ _ _ _ _ _ => fail)))
                                ltac:(CombineCase5 BuildLastEqualityIndex
                                                   ltac:(CombineCase5
                                                           BuildLastFindPrefixIndex
                                                           ltac:(fun _ _ _ _ _ => fail)))).

      initializer.
      insertion ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
             ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
             ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
             ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
             ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).
      deletion ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
             ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
             ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
             ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
             ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).
      observer ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
             ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
             ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
             ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
             ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).

      pose_headings_all.

      match goal with
      | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
        FullySharpenQueryStructure Schema Indexes
      end.
    }

    { simpl; pose_string_ids; pose_headings_all;
      pose_search_term;  pose_SearchUpdateTerms.

      BuildQSIndexedBags' ltac:(CombineCase6 BuildEarlyTrieBag BuildEarlyEqualityBag)
                                 ltac:(CombineCase5 BuildLastTrieBag BuildLastEqualityBag).
    }

    higher_order_reflexivityT.
    (* 124 seconds *)
  Time Defined.

  Time Definition ClassifierImpl : ComputationalADT.cADT ClassifierSig :=
    Eval simpl in (projT1 ClassifierManual).

  Print ClassifierImpl.

End ADT.
