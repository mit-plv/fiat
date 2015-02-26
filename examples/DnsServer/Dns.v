Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT.
Require Import Coq.Vectors.Vector Ascii Bool Bvector List.

Section packet.
  (* TODO: Move this section into a seperate file for basic
     packet and DNS Record definitions. *)

  Definition name := list string.

  Definition beq_name (a b : name) : bool :=
    if (list_eq_dec string_dec a b) then true else false.

  Lemma beq_name_dec
  : forall (a b : name), beq_name a b = true <-> a = b.
  Proof.
    unfold beq_name; intros; find_if_inside; intuition; intros; congruence.
  Qed.

  Inductive RRecordType := A | CNAME | NS | MX.

  Definition beq_RRecordType (a b : RRecordType) :=
    match a, b with
      | A, A => true
      | CNAME, CNAME => true
      | NS, NS => true
      | MX, MX => true
      | _, _ => false
    end.

  Lemma RRecordType_dec
  : forall (a b : RRecordType), {a = b} + {a <> b}.
  Proof.
    destruct a; destruct b; simpl; intuition; intros;
    try first [right; discriminate | left; reflexivity].
  Qed.

  Lemma beq_RRecordType_sym :
    forall rrT rrT', beq_RRecordType rrT rrT' = beq_RRecordType rrT' rrT.
  Proof.
    destruct rrT; destruct rrT'; simpl; congruence.
  Qed.

  Lemma beq_RRecordType_dec :
    forall a b, ?[RRecordType_dec a b] = beq_RRecordType a b.
  Proof.
    intros; find_if_inside; subst.
    destruct b; simpl; reflexivity.
    destruct a; destruct b; simpl; congruence.
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordType :
    Query_eq RRecordType := {| A_eq_dec := RRecordType_dec |}.

  Inductive RRecordClass := IN | CH | HS.

  Definition beq_RRecordClass (a b : RRecordClass) :=
    match a, b with
      | IN, IN => true
      | CH, CH => true
      | HS, HS => true
      | _, _ => false
    end.
  Lemma RRecordClass_dec
  : forall (a b : RRecordClass), {a = b} + {a <> b}.
  Proof.
    destruct a; destruct b; simpl; intuition; intros;
    try first [right; discriminate | left; reflexivity ].
  Qed.

  (* Instances used in DecideableEnsemble. *)
  Global Instance Query_eq_RRecordClass :
    Query_eq RRecordClass := {| A_eq_dec := RRecordClass_dec |}.

  Record question :=
    { qname : name;
      qtype : RRecordType;
      qclass : RRecordClass }.

  Record answer :=
    { aname : name;
      atype : RRecordType;
      aclass : RRecordClass;
      ttl : nat;
      rdata : string }.

  Record packet :=
    { id : Bvector 16;
      flags : Bvector 16;
      questions : question; (* `list question` in case we can have multiple questions? *)
      answers : list answer;
      authority : list answer;
      additional : list answer }.

  Lemma zero_lt_sixteen : lt 0 16. omega. Qed.
  Definition buildempty (p : packet) :=
    {| id := id p;
       flags := replace_order (flags p) zero_lt_sixteen true; (* set QR bit *)
       questions := questions p;
       answers := [ ];
       authority := [ ];
       additional := [ ] |}.

  Definition sCOLLECTIONS := "Collections".
  Definition sNAME := "Name".
  Definition sTTL := "TTL".
  Definition sCLASS := "Class".
  Definition sTYPE := "Type".
  Definition sDATA := "Data".

  (* DNS Resource Records. *)
  Definition DNSRRecord :=
    @Tuple <sNAME :: name,
    sTYPE :: RRecordType,
    sCLASS :: RRecordClass,
    sTTL :: nat,
    sDATA :: string>%Heading.

  Definition toAnswer (t: DNSRRecord) :=
    {| aname := t!sNAME;
       atype := t!sTYPE;
       aclass := t!sCLASS;
       ttl := t!sTTL;
       rdata := t!sDATA |}.

  Definition addan (p : packet) (t : DNSRRecord) :=
    {| id := id p;
       flags := flags p;
       questions := questions p;
       answers := (toAnswer t) :: answers p;
       authority := authority p;
       additional := additional p |}.

  Definition addns (p : packet) (t : DNSRRecord) :=
    {| id := id p;
       flags := flags p;
       questions := questions p;
       answers := answers p;
       authority := (toAnswer t) :: (authority p);
       additional := additional p |}.

End packet.

Definition
  prefixProp (p s : name) := exists ps, p ++ ps = s.
Fixpoint prefixBool (p s : name) :=
  match p, s with
    | [ ], _ => true
    | p' :: ps', s' :: ss' => if string_dec p' s' then prefixBool ps' ss' else false
    | _, _ => false
  end.

Lemma prefixBool_eq :
  forall (p s : name),
    prefixBool p s = true <-> prefixProp p s.
Proof.
  unfold prefixProp; split; revert s; induction p; intros s H.
  - eexists s; reflexivity.
  - destruct s; simpl in H.
    + discriminate.
    + find_if_inside; [subst | discriminate].
      apply_in_hyp IHp; destruct_ex; eexists; subst; reflexivity.
  - simpl; reflexivity.
  - destruct s; simpl in *; destruct H.
    + discriminate.
    + injections; find_if_inside; intuition eauto.
Qed.

Global Instance DecideablePrefix {n}
: DecideableEnsemble (fun tup => prefixProp tup n) :=
  {| dec n' :=  prefixBool n' n;
     dec_decides_P n' := prefixBool_eq n' n|}.

Global Instance DecideablePrefix_sym {A} (f : A -> name) {n}
: DecideableEnsemble (fun tup => prefixProp n (f tup)) :=
  {| dec n' :=  prefixBool n (f n');
     dec_decides_P n' := prefixBool_eq n (f n')|}.

Definition upperbound {A} (f : A -> nat) (rs : list A) (r : A) :=
  forall r', List.In r' rs -> f r >= f r'.

Section FueledFix.
  (* TODO: Find a home for these more definitions in the Common folder. *)

  Variable A : Type. (* Argument Type *)
  Variable R : Type. (* Return Type *)

  Fixpoint FueledFix (fuel : nat) (base : Comp R)
                     (body : (A -> Comp R) -> A -> Comp R) (arg : A)
  : Comp R :=
    match fuel with
      | O => base
      | S fuel' => body (FueledFix fuel' base body) arg
    end.
End FueledFix.

(* Can rewrite under Fueled Fix at the moment,
as the condition on the body is not a proper relation. :p *)
(* TODO: figure out a definition for pointwise_refine that is a
   proper (i.e. reflexive and transitive) relation.
 *)
(*
Print respectful.

Definition pointwise_refine {A R}
  (f g : (A -> Comp R) -> A -> Comp R) :=
  forall (rec rec' : A -> Comp R) (a : A),
    pointwise_relation A (@refine R) rec rec'
    -> refine (f rec a) (g rec' a).

Lemma reflexive_pR {A R : Type} :
  forall A R, Reflexive (@pointwise_refine A R).
Proof.
  unfold Reflexive, pointwise_refine, pointwise_relation.
  intros.
  (* Doesn't work if x is (fun rec a => {r | ~ rec ~> r} :p *)
Admitted.

Lemma transitive_pR {A R : Type} :
  forall A R, Transitive (@pointwise_refine A R).
Proof.
  unfold Transitive, pointwise_refine, pointwise_relation; intros.
  etransitivity.
  apply H; eauto.
  apply H0. reflexivity.
Qed.

Add Parametric Morphism A R i
: (@FueledFix A R i)
    with signature
    ((@refine R)
       ==> (@pointwise_refine A R)
      ==> (@eq A)
      ==> (@refine R))
      as refineFix.
Proof.
  simpl; induction i; intros; simpl.
  - assumption.
  - unfold pointwise_refine, pointwise_relation, Proper, respectful in *.
    eapply H0.
    intros.
    generalize (IHi _ _ H _ _ H0 a); eauto.
Qed.
*)

(* TODO: Agree on a notation for our fueled fix function. *)
Notation "'Repeat' fuel 'initializing' a 'with' arg 'defaulting' rec 'with' base {{ bod }} " :=
  (FueledFix fuel base (fun rec a => bod) arg)
    (no associativity, at level 50,
     format "'Repeat' '[hv'  fuel  '/' 'initializing'  a  'with'  arg '/'  'defaulting'  rec  'with'  base  '/' {{ bod  }} ']' ").

Section FueledFixRefinements.
  (* TODO: Find a home for these refinements in the Computation folder. *)

  Variable A : Type. (* Argument Type *)
  Variable R : Type. (* Return Type *)

  (* TODO Lemmas for refining FueledFix. *)

  Lemma refine_FueledFix_Bind (B : Type) :
    forall fuel body (base : Comp R) (arg : A) (k k' : R -> Comp B),
      refine (r <- base; k r) (r <- base; k' r)
      -> (forall fuel',
            refine (a <- FueledFix fuel' base body arg; k a)
                   (a <- FueledFix fuel' base body arg; k' a)
            -> refine
                 (a <- FueledFix (S fuel') base body arg; k a)
                 (a <- FueledFix (S fuel') base body arg; k' a))
      ->  refine (a <- FueledFix fuel base body arg; k a)
                 (a <- FueledFix fuel base body arg; k' a).
  Proof.
    induction fuel; eauto.
  Qed.

End FueledFixRefinements.

Section FilteredList.

  Definition filtered_list {A}
             (xs : list A)
             (P : Ensemble A)
    := fold_right (fun (a : A) (l : Comp (list A)) =>
                     l' <- l;
                     b <- { b | decides b (P a) };
                     if b
                     then ret (a :: l')
                     else ret l'
                  ) (ret nil) xs.

End FilteredList.

(* Agree on this notation. *)
Notation "'unique' b , P ->> s 'otherwise' ->> s'" :=
  (b' <- {b' | forall b, b' = Some b <-> P};
   If_Opt_Then_Else b' (fun b => s) s') (at level 70).

Definition is_empty {A} (l : list A) :=
  match l with nil => true | _ => false end.

Definition get_name (r : DNSRRecord) : list string := r!sNAME.
Definition name_length (r : DNSRRecord) := List.length (get_name r).

Notation "[[ x 'in' xs | P ]]" := (filtered_list xs (fun x => P)) (at level 70) : comp_scope.

Definition DnsSchema :=
  Query Structure Schema
        [ relation sCOLLECTIONS has
                   schema <sNAME :: name,
          sTYPE :: RRecordType,
          sCLASS :: RRecordClass,
          sTTL :: nat,
          sDATA :: string>
          where (fun t t' => t!sNAME = t'!sNAME -> t!sTYPE <> CNAME) ]
        enforcing [ ].

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.
Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddData" (t : DNSRRecord) : bool :=
      Insert t into sCOLLECTIONS,

    query "Process" (p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 7 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
                                                                 
         {{ rs <- For (r in sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (prefixProp n r!sNAME) (* prefixed with [n] to [rs] *)
                  Return r;
            If (is_empty rs)        (* Are there any matching records? *)
            Then
              bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              if b                (* If the record's QNAME is an exact match  *)
              then
                unique b,
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ t <> CNAME ->>      (* and the query did not request a CNAME *)

                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                                                    (* ?? Shouldn't this use the sDATA ?? *)
                  ret (addan p' b)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                  ret (List.fold_left addan bfrs (buildempty p))
              else
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }} }.

(* Search Terms are pairs of prefixes and filter functions. *)
Record PrefixSearchTerm := { pst_name : name;
                             pst_filter : DNSRRecord -> bool }.
Definition PrefixSearchTermMatcher (search_term : PrefixSearchTerm)
           (t : DnsSchema # sCOLLECTIONS) :=
  prefixBool (pst_name search_term) (t!sNAME) && pst_filter search_term t.

Definition DnsSearchUpdateTerm :=
  {| BagSearchTermType := PrefixSearchTerm;
     BagMatchSearchTerm := PrefixSearchTermMatcher;
     BagUpdateTermType := DNSRRecord -> DNSRRecord;
     BagApplyUpdateTerm := fun f x => f x |}.

    Require Import ADTSynthesis.QueryStructure.Implementation.DataStructures.Bags.ListBags.

  Definition SharpenedPrefixBagImpl :
    Sharpened (@BagSpec _
                        (BagSearchTermType DnsSearchUpdateTerm)
                        (BagUpdateTermType DnsSearchUpdateTerm)
                        (BagMatchSearchTerm DnsSearchUpdateTerm)
                        (BagApplyUpdateTerm DnsSearchUpdateTerm)).
  Proof.
    eapply (SharpenedBagImpl (fun _ => true) (BagPlus := @ListAsBag
             _
             (BagSearchTermType DnsSearchUpdateTerm)
             (BagUpdateTermType DnsSearchUpdateTerm)
             {| pst_name := nil;
                pst_filter := fun _ => true |}
             (BagMatchSearchTerm DnsSearchUpdateTerm)
             (BagApplyUpdateTerm DnsSearchUpdateTerm) ) _
                             (RepInvPlus := fun _ => True)
                             (ValidUpdatePlus := fun _ => True)).
    eauto.
    Grab Existential Variables.
    eapply ListAsBagCorrect.
    simpl.
    apply (fun x => x).
    reflexivity.
  Defined.

(* Parade of admitted refinement lemmas. Should go in a DNS Refinements file. *)

Lemma foo1 :
  forall (n : DNSRRecord) (R : @IndexedEnsemble DNSRRecord),
    n!sTYPE <> CNAME
    -> refine {b |
               decides b
                       (forall tup' : IndexedTuple,
                          R tup' ->
                          n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}
              (ret true).
Proof.
  intros; econstructor; inversion_by computes_to_inv.
  subst; simpl; intros; assumption.
Qed.


    Lemma foo2 :
      forall (n : DNSRRecord) (R : @IndexedEnsemble DNSRRecord),
        n!sTYPE = CNAME
        -> refine {b |
                   decides b
                           (forall tup' : IndexedTuple,
                              R tup' ->
                              n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}
                  (b <- {b |
                        decides b
                                (exists tup' : IndexedTuple,
                                      R tup' /\
                                      n!sNAME = (indexedElement tup')!sNAME)};
                  ret (negb b)).
    Proof.
      intros; econstructor; inversion_by computes_to_inv;
      destruct v; simpl in *; unfold not in *; intros.
      - destruct x; simpl in H1; destruct H1; inversion H2; eauto.
      - destruct x; simpl in H1; destruct H1; inversion H2; eapply H0;
        intros; destruct H2 as [ tup [ H2 H3 ] ]; intuition eauto.
    Qed.

    Lemma foo4 :
      forall (n : DNSRRecord) (R : @IndexedEnsemble DNSRRecord),
        refine {b |
                   decides b
                           (forall tup' : IndexedTuple,
                              R tup' ->
                              (indexedElement tup')!sNAME = n!sNAME
                              -> (indexedElement tup')!sTYPE <> CNAME)}
                  (b <- {b |
                   decides b
                           (exists tup' : IndexedTuple,
                                 R tup' /\
                                 n!sNAME = (indexedElement tup')!sNAME
                                 /\ (indexedElement tup')!sTYPE = CNAME)};
                  ret (negb b)).
    Proof.
      intros; econstructor; inversion_by computes_to_inv;
      destruct v; simpl in *; unfold not in *; intros; destruct x;
      simpl in H1; inversion H1.
      - apply H0; exists tup'; intuition.
      - intros; destruct H0 as [ tup [ ? [ ? ? ] ] ]; eapply H; eauto.
    Qed.

Lemma foo3 :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}
           (If (beq_RRecordType n!sTYPE CNAME)
               Then count <- Count
               For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                     (fun tup : Tuple =>
                                        Where (n!sNAME = tup!sNAME)
                                              Return tup ));
            ret (beq_nat count 0) Else ret true).
Proof.
  intros; setoid_rewrite refine_pick_decides at 1;
  [ | apply foo2 | apply foo1 ].
  refine existence check into query.
  remember n!sTYPE; refine pick val (beq_RRecordType d CNAME); subst;
  [ | case_eq (beq_RRecordType n!sTYPE CNAME); intros;
      rewrite <- beq_RRecordType_dec in H; find_if_inside;
      unfold not; simpl in *; try congruence ].
  simplify with monad laws.
  setoid_rewrite refineEquiv_bind_bind.
  setoid_rewrite refineEquiv_bind_unit.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.


Lemma foo5 :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       (indexedElement tup')!sNAME = n!sNAME
                       -> (indexedElement tup')!sTYPE <> CNAME)}
           (count <- Count
                  For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                        (fun tup : Tuple =>
                                           Where (n!sNAME = tup!sNAME
                                                  /\ tup!sTYPE = CNAME )
                                                 Return tup ));
            ret (beq_nat count 0)).
Proof.
  intros; setoid_rewrite foo4.
  refine existence check into query.
  simplify with monad laws.
  setoid_rewrite negb_involutive; f_equiv.
Qed.

Lemma foo7 {heading}
: forall (R : Ensemble (@IndexedTuple heading))
         (P : Ensemble Tuple)
         (l : list Tuple),
    For (QueryResultComp
           R
           (fun tup => Where (P tup)
                             (Return tup))) ↝ l  ->
    forall (P' : Ensemble Tuple) (P'_dec : DecideableEnsemble P'),
      refine (For (QueryResultComp
                     R
                     (fun tup => Where (P tup /\ P' tup)
                                       (Return tup))))
             (ret (filter DecideableEnsembles.dec l)).
Proof.
  Local Transparent Query_For.
  unfold Query_For, QueryResultComp.
  (* induction? *)
  admit.
Qed.

Lemma foo8 {A}
: forall (c c' : bool) (t e e' : A),
    (c = true -> c' = true)
    -> (if c then (if c' then t else e) else e') = if c then t else e'.
Proof.
  intros; destruct c; destruct c'; try reflexivity.
  assert (true = true); [ reflexivity | apply H in H0; discriminate ].
Qed.

Lemma foo9 {A}
: forall (l : list A) (pred : A -> bool),
    beq_nat (Datatypes.length l) 0 = true
    ->  beq_nat (Datatypes.length (filter pred l)) 0 = true.
Proof.
  induction l; intros; simpl; try inversion H.
  reflexivity.
Qed.

Lemma foo10
: forall (a n : DNSRRecord),
    ?[list_eq_dec string_dec n!sNAME a!sNAME] =
    PrefixSearchTermMatcher
      {|
        pst_name := n!sNAME;
        pst_filter := fun tup : DNSRRecord =>
                        ?[list_eq_dec string_dec n!sNAME tup!sNAME] |} a.
Proof.
  intros a n; unfold PrefixSearchTermMatcher.
  case_eq (list_eq_dec string_dec n!sNAME a!sNAME); intros e H; simpl.
  - symmetry; apply andb_true_iff; split.
    + apply prefixBool_eq; setoid_rewrite e; eexists; apply app_nil_r.
    + find_if_inside; [ reflexivity | contradiction ].
  - symmetry; apply andb_false_iff.
    right; find_if_inside; [ contradiction | reflexivity ].
Qed.

Lemma foo11 {heading}
: forall l,
    map (ilist_hd (As:=cons heading nil ))
        (Build_single_Tuple_list l) = l.
Proof.
  induction l; simpl; congruence.
Qed.

    Lemma refine_filtered_list {A}
    : forall (xs : list A)
             (P : Ensemble A)
             (P_dec : DecideableEnsemble P),
        refine (filtered_list xs P)
               (ret (filter dec xs)).
    Proof.
      unfold filtered_list;
      induction xs; intros.
      - reflexivity.
      - simpl; setoid_rewrite IHxs.
        simplify with monad laws.
        destruct (dec a) eqn: eq_dec_a.
        + setoid_rewrite dec_decides_P in eq_dec_a.
          refine pick val true; auto.
          simplify with monad laws; reflexivity.
        + setoid_rewrite Decides_false in eq_dec_a.
          refine pick val false; auto.
          simplify with monad laws; reflexivity.
    Qed.

    Definition find_upperbound {A} (f : A -> nat) (ns : list A) : list A :=
      let max := fold_right
                   (fun n acc => max (f n) acc) O ns in
      filter (fun n => beq_nat max (f n)) ns.

    Lemma fold_right_max_is_max {A}
    : forall (f : A -> nat) ns n,
        In n ns -> f n <= fold_right (fun n acc => max (f n) acc) 0 ns.
    Proof.
      induction ns; intros; inversion H; subst; simpl;
      apply NPeano.Nat.max_le_iff; [ left | right ]; auto.
    Qed.

    Lemma fold_right_higher_is_higher {A}
    : forall (f : A -> nat) ns x,
        (forall r, In r ns -> f r <= x) ->
        fold_right (fun n acc => max (f n) acc) 0 ns <= x.
    Proof.
      induction ns; simpl; intros; [ apply le_0_n | ].
      apply NPeano.Nat.max_lub.
      apply H; left; auto.
      apply IHns; intros; apply H; right; auto.
    Qed.

    Lemma find_upperbound_highest_length {A}
    : forall (f : A -> nat) ns n,
        In n (find_upperbound f ns) -> forall n', In n' ns -> (f n) >= (f n').
    Proof.
      unfold ge, find_upperbound; intros.
      apply filter_In in H; destruct H; apply beq_nat_true_iff in H1.
      rewrite <- H1; clear H1 H n.
      apply fold_right_max_is_max; auto.
    Qed.

    Lemma find_upperbound_upperbound {A}
    : forall (f : A -> nat) ns n, In n (find_upperbound f ns) <->
                                    In n ns /\ upperbound f ns n.
    Proof.
      unfold upperbound, ge; intros; split; intros; try split.
      - unfold find_upperbound in H; apply filter_In in H; tauto.
      - apply find_upperbound_highest_length; auto.
      - destruct H; unfold find_upperbound.
        apply filter_In; split; try assumption.
        apply beq_nat_true_iff.
        pose proof (fold_right_max_is_max f _ _ H).
        pose proof (fold_right_higher_is_higher f _ H0).
        eapply le_antisym; eauto.
    Qed.

    Instance DecideableEnsembleUpperbound {A} (f : A -> nat) ns :
      DecideableEnsemble (upperbound f ns) :=
      let max := fold_right
                   (fun n acc => max (f n) acc) O ns in
      {| dec n := beq_nat max (f n) |}.
    Proof.
      admit.
    Defined.

    Corollary refine_find_upperbound {A}
    : forall (f : A -> nat) ns,
        refine ([[n in ns | upperbound f ns n]])
               (ret (find_upperbound f ns)).
    Proof.
      intros.
      setoid_rewrite refine_filtered_list with (P_dec := DecideableEnsembleUpperbound f ns).
      reflexivity.
    Qed.

    Lemma foo16 :
      forall ns s,
        (forall n', In n' ns -> prefixProp (get_name n') s)
        -> forall n n', In n (find_upperbound name_length ns)
                        -> In n' (find_upperbound name_length ns)
                        -> get_name n = get_name n'.
    Proof.
      unfold find_upperbound, name_length; intros ns s H0 n n' H H1.
      apply filter_In in H; destruct H; apply filter_In in H1; destruct H1.
      pose proof (H0 _ H); pose proof (H0 _ H1).
      apply beq_nat_true in H2; apply beq_nat_true in H3; rewrite H2 in H3.
      unfold prefixProp in *; destruct H4; destruct H5; rewrite <- H5 in H4.
      clear H H2 H0 H1 H5 s ns.
      remember (get_name n); remember (get_name n'); clear Heql Heql0.
      revert x0 l l0 H4 H3.
      induction x; destruct x0; intros.
      - repeat rewrite app_nil_r in H4; assumption.
      - apply f_equal with (f := @Datatypes.length string) in H4.
        repeat rewrite app_length in H4; subst; exfalso; simpl in *; omega.
      - apply f_equal with (f := @Datatypes.length string) in H4.
        repeat rewrite app_length in H4; subst; exfalso; simpl in *; omega.
      - rewrite app_comm_cons' with (As := l) in H4.
        rewrite app_comm_cons' with (As := l0) in H4.
        apply IHx in H4; [ apply app_inj_tail in H4; destruct H4; auto |
        repeat rewrite app_length; rewrite H3; reflexivity ].
    Qed.

    Ltac find_if_inside_eqn :=
      match goal with
        | [ |- context[if ?X then _ else _] ] => destruct X eqn: ?
        | [ H : context[if ?X then _ else _] |- _ ]=> destruct X eqn: ?
      end.

    (* Implement the check for an exact match *)
    Lemma foo19
    : forall ns s,
        (forall n', In n' ns -> prefixProp (get_name n') s) ->
        refine {b : bool |
                decides b
                        (~
                           (exists x : DNSRRecord,
                              In x (find_upperbound name_length ns) /\ s <> (get_name x)))}
               (ret match find_upperbound name_length ns with
                      | nil => true
                      | n' :: _ => ?[s == (get_name n')]
                    end).
    Proof.
      econstructor; simpl in H; intros; apply computes_to_inv in H0.
      subst; unfold decides; pose proof (foo16 ns H); clear H.
      remember (find_upperbound name_length ns) as l.
      find_if_inside_eqn.
      - unfold not; intros; repeat destruct H; apply H1; clear H1; destruct l;
        [ inversion H | subst; apply H0 with (n := d) in H ];
        [ find_if_inside; [ subst; auto | inversion Heqb ] | simpl; left; auto ].
      - unfold not; intros; apply H; clear H; destruct l; try inversion Heqb.
        exists d; split; [ simpl; left; auto | intros; rewrite <- H in Heqb ].
        find_if_inside; [ discriminate | unfold not in *; apply n; auto ].
    Qed.

    Lemma foo20
    : forall ns n s
        (HH : forall t t' n m,  n <> m
                           -> nth_error ns n =  Some t
                           -> nth_error ns m = Some t'
                           -> get_name t = get_name t' -> t!sTYPE <> CNAME),
        (forall n', In n' ns -> prefixProp (get_name n') s) ->
        refine {b' |
                forall b : Tuple,
                  b' = Some b <->
                  In b (find_upperbound name_length ns) /\
                  b!sTYPE = CNAME /\ n <> CNAME}
               (ret match (find_upperbound name_length ns) with
                      | nil => None
                      | n' :: _ => if CNAME == (n'!sTYPE)
                                   then if n == CNAME
                                        then None
                                        else Some n'
                                   else None
                    end).
    Proof.
      unfold refine; intros; pose proof (foo16 ns H); clear H.
      remember (find_upperbound name_length ns) as l; clear Heql.
      apply computes_to_inv in H0; econstructor; split; intros.
      - destruct l; [ subst; inversion H | ].
        repeat find_if_inside_eqn; subst; try inversion H; subst.
        repeat split; [ simpl; left | symmetry | ]; auto.
      - destruct H as [? [? ?] ]; destruct l; [ inversion H | subst ].
        admit.
    Qed.

    Lemma refine_If_Opt_Then_Else_ret {A B} :
      forall i (t : A -> B) (e : B),
        refine (@If_Opt_Then_Else A (Comp B) i (fun a => ret (t a)) (ret e))
               (ret (@If_Opt_Then_Else A B i t e)).
    Proof.
      destruct i; reflexivity.
    Qed.

    Lemma foo13 : forall l (a : DNSRRecord),
                prefixBool l (a!sNAME) =
                PrefixSearchTermMatcher
                  {|
                    pst_name := l;
                    pst_filter := fun _ : DNSRRecord => true |} a.
    Proof.
      symmetry; apply andb_true_r.
    Qed.

Lemma foo12 :
  forall l l' : name,
    prefixBool l l' = false ->
    ?[list_eq_dec string_dec l l'] = false.
Proof.
  induction l; simpl; destruct l'; intros; eauto.
  repeat find_if_inside; eauto; injections.
  rewrite <- (IHl _ H).
  clear; induction l'; simpl; eauto.
  find_if_inside; congruence.
  congruence.
Qed.

Lemma refine_decides_forall_In' :
  forall {A} l (P: A -> Prop) (P_Dec : DecideableEnsemble P),
    refine {b | decides b (forall (x: A), In x l -> P x)}
           {b | decides b (~ exists (x : A), In x l /\ ~ P x)}.
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  constructor.
  destruct v; simpl in *; intros.
  case_eq (dec x); intros; try rewrite <- (dec_decides_P); eauto.
  elimtype False; eapply H; eexists; intuition eauto.
  rewrite <- dec_decides_P in H2; congruence.
  unfold not in *; intros.
  eapply H; intros.
  destruct H1; intuition.
Qed.

Transparent FueledFix.

Theorem DnsManual :
  Sharpened DnsSpec.
Proof.
  unfold DnsSpec.
  start honing QueryStructure.

  (* Implement the constraint checks as queries. *)
  hone method "AddData".
  {
    setoid_rewrite foo3.
    setoid_rewrite foo5.
    simplify with monad laws.
    setoid_rewrite refine_If_Then_Else_Bind.
    setoid_rewrite Bind_refine_If_Then_Else.
    etransitivity.
    apply refine_If_Then_Else.
    - simplify with monad laws.
      apply refine_under_bind; intros.
      setoid_rewrite refine_Count; simplify with monad laws.
      apply refine_under_bind; intros.
      (* remove duplicate check *)
      setoid_rewrite foo7; eauto.
      simplify with monad laws.
      rewrite foo8 by apply foo9.
      higher_order_1_reflexivity.
    - simplify with monad laws.
      reflexivity.
    - finish honing.
  }

  hone representation using (@DelegateToBag_AbsR DnsSchema (icons DnsSearchUpdateTerm (inil _))).
  (* TODO: We should define a 'make simple indexes' tactic notation variant for
     lists of SearchUpdateTerms. *)

  hone constructor "Init".
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
  }

  hone method "Process".
  {
    simplify with monad laws.
    Focused_refine_Query.
    {
      implement_In.

      convert_Where_to_search_term.
      find_equivalent_search_term 0 ltac:(fun _ _ _ _ => idtac).
      { instantiate (1 := {| pst_name := qname (questions n);
                             pst_filter := fun tup => true |}).

        simpl.
        intros; apply foo13.
      }

      convert_filter_to_find.
      Implement_Aggregates.

      setoid_rewrite foo11.
      reflexivity.
    }
    (* Find the upperbound of the results. *)
    setoid_rewrite refine_find_upperbound.
    simplify with monad laws.
    etransitivity.
    (* Should Conditional honing under bind should be it's own tactic? *)
    apply refine_under_bind; intros.
    (* Should honing if branches also be their own tactic? *)
    etransitivity.
    setoid_rewrite refine_If_Then_Else_Bind.
    apply refine_If_Then_Else.
    - simplify with monad laws.

      rewrite refine_decides_forall_In'.

      setoid_rewrite foo19.
      simplify with monad laws.
      setoid_rewrite refine_if_If.
      setoid_rewrite refine_If_Then_Else_Bind.
      etransitivity.
      apply refine_If_Then_Else.
      simplify with monad laws.

      setoid_rewrite foo20.
      simplify with monad laws.
      setoid_rewrite refine_If_Opt_Then_Else_Bind.
     apply refine_If_Opt_Then_Else.
      unfold pointwise_relation; intros.
      rewrite refine_filtered_list.
      simplify with monad laws.
      simpl.
      refine pick val _; eauto.
      simplify with monad laws.
      higher_order_1_reflexivity.
      simplify with monad laws.
      refine pick val _; eauto.
      simplify with monad laws.
      reflexivity.
      rewrite refine_filtered_list.
      simplify with monad laws.
      refine pick val _; eauto.
      simplify with monad laws.
      reflexivity.
      reflexivity.
      eauto with typeclass_instances.
    - simplify with monad laws.
      refine pick val _; eauto.
      simplify with monad laws.
      simpl; reflexivity.
    - finish honing.
    - simpl. finish honing.
  }

  hone method "AddData".
  {
    etransitivity.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    - apply refine_If_Then_Else.
      + simplify with monad laws.
        Focused_refine_Query.
        {
          implement_In.
          convert_Where_to_search_term.
          (* TODO: Create a tactic that builds the search term to use
           in lieu of this idtac. *)
          find_equivalent_search_term 0 ltac:(fun _ _ _ _ => idtac).
          { instantiate (1 := {| pst_name := n!sNAME;
                                 pst_filter := fun tup => ?[list_eq_dec string_dec n!sNAME tup!sNAME] |}).
            intros; apply foo10.
          }

          convert_filter_to_find.
          Implement_Aggregates.

          setoid_rewrite foo11.
          reflexivity.
        }

        simplify with monad laws.
        setoid_rewrite refineEquiv_swap_bind.

        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
      + simplify with monad laws.

        Focused_refine_Query.
        { implement_In.

          convert_Where_to_search_term.
          (* TODO: Reuse tactic from above to build this search term. *)
          instantiate (1 := fun a => PrefixSearchTermMatcher {| pst_name := n!sNAME;
                                                                pst_filter := fun tup => ?[list_eq_dec string_dec n!sNAME tup!sNAME]
                                                                                          && (?[CNAME == (tup!sTYPE)]) |} (ilist_hd a)).
          { intro; unfold PrefixSearchTermMatcher; simpl.
            match goal
            with |- context [ prefixBool ?l ?l' ] => case_eq (prefixBool l l');
                   simpl end.
            intros; f_equal.
            repeat find_if_inside; simpl; try congruence.


            intros; rewrite foo12; simpl; eauto.
          }

          convert_filter_to_find.
          Implement_Aggregates.
          setoid_rewrite foo11.
          reflexivity.
        }

        simplify with monad laws.
        setoid_rewrite refineEquiv_swap_bind.

        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
    - reflexivity.
    - finish honing.
  }

  FullySharpenQueryStructure' DnsSchema
(icons DnsSearchUpdateTerm
       (inil
          (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns))))).

  {
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
    Implement_Bound_Bag_Call.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
    Implement_Bound_Bag_Call.
    Implement_AbsR_Relation.
    simpl; reflexivity.
    simplify with monad laws.
    simpl; Implement_AbsR_Relation.
    reflexivity.
    apply refine_If_Then_Else_ret.
    simplify with monad laws.
    Implement_Bound_Bag_Call.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
    Implement_Bound_Bag_Call.
    Implement_AbsR_Relation.
    reflexivity.
    simplify with monad laws.
    Implement_AbsR_Relation.
    reflexivity.
    apply refine_If_Then_Else_ret.
    etransitivity.
    apply refine_If_Then_Else_ret.
    higher_order_4_reflexivity''.
  }

  {
    simplify with monad laws.
    Implement_Bound_Bag_Call.

    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    setoid_rewrite refine_If_Opt_Then_Else_Bind.
    etransitivity.
    apply refine_If_Opt_Then_Else.
    intro; simplify with monad laws.
    simpl; Implement_AbsR_Relation.
    higher_order_1_reflexivity.
    intro; simplify with monad laws.
    simpl; Implement_AbsR_Relation.
    reflexivity.

    apply refine_If_Opt_Then_Else_ret.
    simplify with monad laws.
    simpl; Implement_AbsR_Relation.
    reflexivity.

    apply refine_If_Then_Else_ret.
    simplify with monad laws.
    simpl; Implement_AbsR_Relation.
    reflexivity.

    apply refine_If_Then_Else_ret.
  }
Defined.

  Definition foo :
    ComputationalADT.cADT
      (BagSig (DnsSchema # sCOLLECTIONS)
              (BagSearchTermType DnsSearchUpdateTerm)
              (BagUpdateTermType DnsSearchUpdateTerm)).
  Proof.
    refine (Sharpened_Implementation (projT1 SharpenedPrefixBagImpl) (fun _ => unit) _).
    intros; apply @BoundedIndex_nil with (A := string).
    unfold BoundedString in idx.
    unfold SharpenedPrefixBagImpl in idx.
    simpl in idx.
    exact idx.
  Defined.

  Definition bar
  : forall idx : BoundedString,
      ComputationalADT.pcADT
     (Build_IndexedQueryStructure_Impl_Sigs
        (icons DnsSearchUpdateTerm
           (inil
              (fun ns : NamedSchema =>
               SearchUpdateTerms (schemaHeading (relSchema ns))))) idx)
     (delegateeRep
        (nth_Bounded delegateeName
           [{|
            delegateeName := sCOLLECTIONS;
            delegateeSig := BagSig (DnsSchema # sCOLLECTIONS)
                              (BagSearchTermType DnsSearchUpdateTerm)
                              (BagUpdateTermType DnsSearchUpdateTerm);
            delegateeRep := projT1 foo |}] idx)).
  Proof.
    eapply Iterate_Dep_Type_BoundedIndex_equiv_1.
    unfold Build_IndexedQueryStructure_Impl_Sigs; simpl.
    split.
    pose (projT2 foo).
    simpl in p.
    apply p.
    constructor.
  Defined.

Definition DNSImpl : ComputationalADT.cADT DnsSig.
  let Impl := eval simpl in
  (Sharpened_Implementation (projT1 DnsManual)
                             _
                             bar) in
      exact Impl.
Defined.

Print DNSImpl.

Goal (DNSImpl = DNSImpl).
unfold DNSImpl at 1.
unfold Build_IndexedQueryStructure_Impl_cRep.


Print CallBagImplMethod.
