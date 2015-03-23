Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        ADTSynthesis.Common.List.Prefix.

Require Import Coq.Strings.Ascii.

Open Scope list.

Section Packet.
  (* an Ip address is a list of 8-bit integer *)
  Definition Ip := list ascii.

  Lemma Ip_dec : forall a b : Ip, {a = b} + {a <> b}.
  Proof. apply list_eq_dec; apply ascii_dec. Qed.

  Global Instance Query_eq_Ip :
    Query_eq Ip := {| A_eq_dec := Ip_dec |}.

  Global Instance DecideablePrefix_Ip_f {T : Type}
  : forall (f : T -> Ip) (n : Ip), DecideableEnsemble (fun tup => prefix_prop (f tup) n)
    := DecideablePrefix_f. apply ascii_dec. Defined.

  Global Instance DecideablePrefix_Ip_b {T : Type}
  : forall (f : T -> Ip) (n : Ip), DecideableEnsemble (fun tup => prefix_prop n (f tup))
    := DecideablePrefix_b. apply ascii_dec. Defined.
    
  (* a Protocol can be either tcp or udp *)
  Inductive Protocol := tcp | udp.

  Lemma Protocol_dec : forall a b : Protocol, {a = b} + {a <> b}.
  Proof. decide equality. Qed.

  Global Instance Query_eq_Protocol :
    Query_eq Protocol := {| A_eq_dec := Protocol_dec |}.

  (* a Policy of P is either enforcing some constant P, or accept any *)
  Section Packet_Protocol.
    Variable P : Type.
    Variable P_dec : forall a b : P, {a = b} + {a <> b}.
    
    Inductive Policy :=
    | enforce : P -> Policy
    | wildcard.
    
    Definition policy_prop (p : Policy) (s : P) :=
      match p with
        | enforce p' => p' = s
        | wildcard => True
      end.
    
    Definition policy_bool (p: Policy) (s : P) :=
      match p with
        | enforce p' => ?[P_dec p' s]
        | wildcard => true
      end.
    
    Lemma policy_bool_eq :
      forall p s, policy_bool p s = true <-> policy_prop p s.
    Proof.
      destruct p; simpl; split; try find_if_inside; intuition.
    Qed.
    
    Global Instance DecideablePolicy {T} (f : T -> Policy) {n}
    : DecideableEnsemble (fun tup => policy_prop (f tup) n) :=
      {| dec n' :=  policy_bool (f n') n;
         dec_decides_P n' := policy_bool_eq (f n') n|}.
  End Packet_Protocol.
  
  Global Instance DecideablePolicy_Protocol {T : Type}
  : forall (f : T -> Policy Protocol) (n : Protocol), DecideableEnsemble (fun tup => policy_prop (f tup) n) :=
    DecideablePolicy Protocol_dec.

  (* a `simple` Packet consists of only Ip and Protocol *)
  Record Packet :=
    { destination : Ip;
      protocol : Protocol }.

  (* a Response of a query can be accept, deny, or uncertain *)
  Inductive Response := Accept | Deny | Uncertain.
End Packet.

Section Upperbound.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Variable R_dec : forall a b, {R a b} + {~ R a b}.

  (* every element in xs is `rel` to x *)
  Definition upperbound  (x : A) (xs : list A) :=
    forall x', List.In x' xs -> R x x'.

  (* if you decide to pick some x', it must be the upperbound of the list *)
  Definition pick_upperbound (xs : list A) : Comp (option A) :=
    { x | forall x', x = Some x' -> List.In x' xs /\ upperbound x' xs }.

  (* an uninteresting way to implement pick_upperbound *)
  Definition choose_upperbound_boring (xs : list A) : option A := None.

  Theorem refine_pick_upperbound_boring :
    forall (xs : list A),
      refine (pick_upperbound xs) (ret (choose_upperbound_boring xs)).
  Proof.
    unfold pick_upperbound, choose_upperbound_boring; intuition;
    refine pick val None; [ reflexivity | intros; discriminate ].
  Qed.

  (* an inefficient but more interesting way to implement pick_upperbound *)
  Fixpoint check_upperbound_ineff (v : A) (xs : list A) : bool :=
    match xs with
      | [ ] => true
      | x :: xs' => ?[ R_dec v x ] && check_upperbound_ineff v xs'
    end.

  Fixpoint choose_upperbound_ineff' (xs : list A) (ys : list A) : option A :=
    match ys with
      | [ ] => None
      | y :: ys' => match choose_upperbound_ineff' xs ys' with
                      | None => if check_upperbound_ineff y xs
                                then Some y
                                else None
                      | Some v => Some v
                    end
    end.

  Definition choose_upperbound_ineff (xs : list A) : option A :=
    choose_upperbound_ineff' xs xs.

  Lemma choose_upperbound_ineff'_close :
    forall xs ys x, choose_upperbound_ineff' xs ys = Some x -> List.In x ys.
  Proof.
    induction ys; intuition; try discriminate; simpl in *;
    remember (choose_upperbound_ineff' xs ys) as c; destruct c;
    [ right | destruct (check_upperbound_ineff a xs); inversion H ]; intuition.
  Qed.

  Corollary choose_upperbound_ineff_close :
    forall xs x, choose_upperbound_ineff xs = Some x -> List.In x xs.
  Proof.
    unfold choose_upperbound_ineff; intuition;
    eapply choose_upperbound_ineff'_close; eauto.
  Qed.

  Lemma check_upperbound_ineff_sound :
    forall v xs, check_upperbound_ineff v xs = true -> upperbound v xs.
  Proof.
    unfold upperbound; induction xs; simpl in *; intuition;
    apply_in_hyp andb_true_iff; intuition; subst;
    find_if_inside; intuition.
  Qed.

  Lemma choose_upperbound_ineff'_is_upperbound :
    forall xs ys x, choose_upperbound_ineff' xs ys = Some x -> upperbound x xs.
  Proof.
    induction ys; intuition; try discriminate; simpl in *;
    remember (choose_upperbound_ineff' xs ys) as c; destruct c; [
      apply IHys |
      remember (check_upperbound_ineff a xs) as c'; destruct c'; inversion H;
      apply check_upperbound_ineff_sound; symmetry; subst ]; trivial.      
  Qed.

  Corollary choose_upperbound_ineff_is_upperbound :
    forall xs x, choose_upperbound_ineff xs = Some x -> upperbound x xs.
  Proof.
    unfold choose_upperbound_ineff; intuition;
    eapply choose_upperbound_ineff'_is_upperbound; eauto.
  Qed.

  Theorem refine_pick_upperbound_ineff :
    forall (xs : list A),
      refine (pick_upperbound xs)
             (ret (choose_upperbound_ineff xs)).
  Proof.
    unfold pick_upperbound, choose_upperbound_ineff; intuition;
    refine pick val _; try reflexivity; intuition;
    [ apply choose_upperbound_ineff_close | apply choose_upperbound_ineff_is_upperbound ]; trivial.
  Qed.

  Lemma rel_dec_map {X} :
    forall (f : X -> A), forall a b : X, {R (f a) (f b)} + {~ R (f a) (f b)}.
  Proof. intuition. Qed.

  Lemma rel_dec_comm :
    forall a b, {R b a} + {~ R b a}.
  Proof. intuition. Qed.
End Upperbound.

(* notation for upperbound *)
Notation "{ x 'in' xs | P 'forall' y }" := (pick_upperbound (fun x y => P) xs) (at level 70) : comp_scope.
Notation "{ x 'in' xs | P 'forall' y } : A" := (@pick_upperbound A (fun x y => P) xs) (at level 70) : comp_scope.

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

  Definition get_destination (r : RuleRecord) : Ip := r!DESTINATION.
  Definition get_destination' : @Tuple (GetHeading ClassifierSchema RULES) -> Ip := get_destination.

  (* probably we should use typeclasses to solve this issue *)
  Definition priority_lt_dec :
          forall a b : RuleRecord, sumbool (b!PRIORITY <= a!PRIORITY) (~ b!PRIORITY <= a!PRIORITY)
    := rel_dec_comm _ (rel_dec_map _ le_dec (fun r : RuleRecord => r!PRIORITY)).

  Definition ClassifierSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddRule" : rep x RuleRecord -> rep x bool,
      Method "Classify" : rep x Packet -> rep x Response
    }.

  Definition ClassifierSpec : ADT ClassifierSig :=
  QueryADTRep ClassifierSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddRule" (r : RuleRecord) : bool :=
      Insert r into RULES,

    query "Classify" (p : Packet) : Response :=
      rs <- For (r in RULES)
            (* the rule's ip must be a prefix of the packet's ip *)
            Where (prefix_prop r!DESTINATION (destination p) /\
            (* the rule's protocol must match the packet's protocol *)
                   policy_prop r!PROTOCOL (protocol p))
            Return r;
      (* try to choose one rule that has the highest priority *)
      r <- { r in rs | r'!PRIORITY <= r!PRIORITY forall r' } : RuleRecord;
      (* return its accept / deny if such rule exists, otherwise uncertain *)
      Ifopt
        r as r
      Then
        If
          r!ACTION
        Then
          ret Accept
        Else
          ret Deny
      Else
        ret Uncertain
    }.

  Theorem ClassifierManual :
    Sharpened ClassifierSpec.
  Proof.
    unfold ClassifierSpec.
    start honing QueryStructure.

    hone representation using
         (@DelegateToBag_AbsR ClassifierSchema
         (* using prefix index on field `DESTINATION` of table `RULES` *)
         (icons (@PrefixSearchUpdateTerm _ ascii_dec (GetHeading ClassifierSchema RULES) get_destination') (inil _))).

    hone constructor "Init".
    {
      simplify with monad laws.
      rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
      finish honing.
    }

    hone method "Classify".
    {
      simplify with monad laws.
      implement_Query' ltac:(fun _ _ _ _ => PrefixSearchTermFinder) ltac:(fun _ _ _ _ _ => idtac).
      simplify with monad laws.
      etransitivity.
      apply refine_under_bind; intros.
      - setoid_rewrite (refine_pick_upperbound_ineff _ priority_lt_dec).
        simplify with monad laws.
        apply refine_under_bind; intros.
        refine pick val _; eauto.
        simplify with monad laws.
        higher_order_1_reflexivity.
      - simpl.
        finish honing.
    }

    hone method "AddRule".
    {
      simplify with monad laws.
      insertion.
    }

    FullySharpenQueryStructure ClassifierSchema
    (icons (@PrefixSearchUpdateTerm _ ascii_dec (GetHeading ClassifierSchema RULES) get_destination')
           (inil
              (fun ns : NamedSchema =>
                 SearchUpdateTerms (schemaHeading (relSchema ns))))).

    implement_bag_methods.
    implement_bag_methods.
  Defined.
End ADT.