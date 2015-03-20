Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii Coq.Bool.Bool
        Coq.Bool.Bvector Coq.Lists.List.

Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        ADTExamples.DnsServer.packet.

Open Scope list.

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

Lemma prefixBool_reflexive :
  forall l, true = prefixBool l l.
Proof.
  induction l.
  - reflexivity.
  - simpl; rewrite string_dec_refl; assumption.
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
      Repeat 1 initializing n with qname (questions p)
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
          }}}.

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
  intros; refine pick val true; [ reflexivity | simpl; intros; assumption ].
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
   repeat match goal with
    | _ : _ ↝ _ |- _ => computes_to_inv
    | _ : negb ?v = _ |- _ => destruct v; simpl in *; subst
    | _ : ex _ |- _ => destruct_ex
    | _ => progress first [ intro | computes_to_econstructor | simpl; intuition; eauto ]
          end.
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
  repeat match goal with
    | _ : _ ↝ _ |- _ => computes_to_inv
    | _ : negb ?v = _ |- _ => destruct v; simpl in *; subst
    | _ : ex _ |- _ => destruct_ex
    | _ => progress first [ intro | computes_to_econstructor | simpl; intuition; eauto ]
         end.
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
  (* refine existence check into query. *)
  match goal with
      |- context[{b | decides b
                              (exists tup : @IndexedTuple ?heading,
                                 (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
      =>
      let H1 := fresh in
      let H2 := fresh in
      makeEvar (Ensemble (@Tuple heading))
               ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                     [unfold Same_set, Included, Ensembles.In;
                       split; [intros x H; pattern (indexedElement x);
                               match goal with
                                   |- ?P'' (indexedElement x) => unify P' P'';
                                     simpl; eauto
                               end
                              | eauto]
                     |
                     assert (DecideableEnsemble P') as H2;
                       [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                       | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  remember n!sTYPE; refine pick val (beq_RRecordType d CNAME); subst;
  [ | case_eq (beq_RRecordType n!sTYPE CNAME); intros;
      rewrite <- beq_RRecordType_dec in H; find_if_inside;
      unfold not; simpl in *; try congruence ].
  simplify with monad laws.
  autorewrite with monad laws.
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
  (*refine existence check into query. *)
  match goal with
      |- context[{b | decides b
                              (exists tup : @IndexedTuple ?heading,
                                 (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
      =>
      let H1 := fresh in
      let H2 := fresh in
      makeEvar (Ensemble (@Tuple heading))
               ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                     [unfold Same_set, Included, Ensembles.In;
                       split; [intros x H; pattern (indexedElement x);
                               match goal with
                                   |- ?P'' (indexedElement x) => unify P' P'';
                                     simpl; eauto
                               end
                              | eauto]
                     |
                     assert (DecideableEnsemble P') as H2;
                       [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                       | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  (* apply @DecideableEnsemble_And.  apply DecideableEnsemble_EqDec.
  apply Query_eq_list. apply DecideableEnsemble_EqDec. apply Query_eq_RRecordType.
  Print Instances DecideableEnsemble. *)
  simplify with monad laws.
  setoid_rewrite negb_involutive; f_equiv.
Qed.

Lemma foo7 {heading}
: forall (R : Ensemble (@IndexedTuple heading))
         (P : Ensemble Tuple) (P_dec : DecideableEnsemble P)
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
  unfold Query_For, QueryResultComp, Query_Return;
    intros; computes_to_inv.
  refine pick val _; eauto.
  simplify with monad laws.
  unfold refine; intros; computes_to_inv; computes_to_econstructor.
  instantiate (1 := (filter (@dec _ _ P'_dec) v)).
  - clear H0 H H' v1; generalize dependent v; induction v0.
    + simpl; intros; computes_to_inv; subst; reflexivity.
    + simpl; intros; computes_to_inv; subst; apply IHv0 in H'0'; clear IHv0.
      destruct (@dec _ P' P'_dec a) eqn: dec_a; unfold Query_Where in *; destruct H'0.
      * pose proof dec_a as dec_a'; apply dec_decides_P in dec_a.
        repeat computes_to_inv; repeat computes_to_econstructor.
        intuition eauto. eauto.
        apply eq_ret_compute; destruct (@dec _ P P_dec a) eqn: dec__a.
        apply dec_decides_P in dec__a; apply H in dec__a;
        computes_to_inv; subst; simpl; rewrite dec_a'; reflexivity.
        apply Decides_false in dec__a; apply H0 in dec__a; subst; reflexivity.
      * pose proof dec_a as dec_a'; apply Decides_false in dec_a.
        repeat computes_to_inv; repeat computes_to_econstructor.
        intuition eauto. eauto.
        apply eq_ret_compute; destruct (@dec _ P P_dec a) eqn: dec__a.
        apply dec_decides_P in dec__a; apply H in dec__a;
        computes_to_inv; subst; simpl; rewrite dec_a'; reflexivity.
        apply Decides_false in dec__a; apply H0 in dec__a; subst; reflexivity.
  - refine pick val _; auto; subst.
    apply filter_permutation_morphism; [ reflexivity | assumption ].
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

Lemma andb_implication_preserve :
  forall a b, (a = true -> b = true) -> a = b && a.
Proof.
  intros; destruct a; destruct b; symmetry; auto.
Qed.
Lemma andb_permute :
  forall a b c, a && (b && c) = b && (a && c).
  intros.
  repeat rewrite andb_assoc.
  replace (a && b) with (b && a) by apply andb_comm.
  reflexivity.
Qed.
Ltac PrefixSearchTermFinderEqSolve :=
  intros; unfold PrefixSearchTermMatcher; simpl;
   apply andb_implication_preserve; find_if_inside; intros;
   match goal with
     | H : _ = _ |- _ =>
       setoid_rewrite H;
         erewrite prefixBool_reflexive; reflexivity
     | _ => erewrite prefixBool_reflexive; reflexivity
     | _ => discriminate
   end.
Ltac PrefixSearchTermNormalizer idx :=
  generalize dependent idx;
  let a' := fresh in
  let ha := fresh in
  match goal with
    | |- forall a, _ = PrefixSearchTermMatcher ?st (@?h a) =>
      intros a'; remember (h a') as ha; generalize ha
  end.
Ltac PrefixSearchTermFinder' idx :=
  PrefixSearchTermNormalizer idx;
  match goal with
    (* case prefix match *)
    | |- forall a, prefixBool ?n a!sNAME && @?f a = PrefixSearchTermMatcher ?st a =>
      instantiate (1 := {| pst_name := n; pst_filter := f |}); reflexivity
    (* case equality *)
    | |- forall a, ?[list_eq_dec string_dec ?n a!sNAME] && @?f a =
                   PrefixSearchTermMatcher ?st a =>
      instantiate
        (1 := {| pst_name := n;
                 pst_filter := fun a => ?[list_eq_dec string_dec n a!sNAME] && f a |});
        PrefixSearchTermFinderEqSolve
    | |- forall a, ?[list_eq_dec string_dec a!sNAME ?n] && @?f a =
                   PrefixSearchTermMatcher ?st a =>
      instantiate
        (1 := {| pst_name := n;
                 pst_filter := fun a => ?[list_eq_dec string_dec a!sNAME n] && f a |});
        PrefixSearchTermFinderEqSolve
  end.
Ltac AdjustAndRec terminal term :=
  let aterm := fresh in
  first [
      (* if we get the exact match, we're done !*)
      assert (aterm : terminal = term) by reflexivity; clear aterm |
      match term with
        | ?left && ?right =>
          first [
              (* if the left term is the exact match, also done! *)
              assert (aterm : left = terminal) by reflexivity; clear aterm |
              (* if the right term is the exact match, just need to switch! *)
              assert (aterm : right = terminal) by reflexivity; clear aterm;
                replace (left && right) with
                (right && left) by apply andb_comm |
              (* now try recursively on the left term *)
              (AdjustAndRec terminal left);
                match goal with
                  | |- context [ (terminal && ?rem) && right ] =>
                    replace ((terminal && rem) && right) with
                    (terminal && (rem && right)) by apply andb_assoc
                end |
              (* and now the righ term *)
              (AdjustAndRec terminal right);
                match goal with
                  | |- context [ left && (terminal && ?rem) ] =>
                    replace (left && (terminal && rem)) with
                    (terminal && (left && rem)) by apply andb_permute
                end ]
      end ].
Ltac AdjustAnd terminal ensure_and :=
  match goal with
    | |- ?filter = _ => AdjustAndRec terminal filter
  end;
  match ensure_and with
    | true =>
      match goal with
        | |- _ && _ = _ => idtac
        | |- ?x = _ => rewrite <- (andb_true_r x)
      end
    | false => idtac
  end.
Ltac PrefixSearchTermFinder :=
  let idx := fresh in
  intros idx;
  match goal with
    | |- context [ prefixBool ?n ?n' ] =>
      AdjustAnd (prefixBool n n') true; PrefixSearchTermFinder' idx
    (* ensure_and can be false, but need some more thought *)
    | |- context [ ?[list_eq_dec string_dec ?n ?n'] ] =>
      AdjustAnd (?[list_eq_dec string_dec n n']) true; PrefixSearchTermFinder' idx
    | |- _ => PrefixSearchTermNormalizer idx;
        match goal with
          (* catch all case; ignore search term, use only the filter *)
          (* only when wildcard is idtac, when this tactic gets used *)
          | |- forall a, @?f a = PrefixSearchTermMatcher ?st a =>
            instantiate (1 := {| pst_name := nil; pst_filter := f |}); reflexivity
        end
  end.

Lemma foo10
: forall (n : DNSRRecord) (b c d e : bool), exists st, forall (a : DNSRRecord * nat),
    ?[list_eq_dec string_dec (fst a)!sNAME n!sNAME] =
    PrefixSearchTermMatcher st (fst a).
Proof.
  eexists.
  PrefixSearchTermFinder.
Qed.
Print foo10.
Lemma foo10' : forall n : DNSRRecord, forall b c d, exists st, forall (a : DNSRRecord * nat),
    b && ( c && d ) && (?[list_eq_dec string_dec (fst a)!sNAME n!sNAME]) && (?[RRecordType_dec (fst a)!sTYPE CNAME]) =
    PrefixSearchTermMatcher st (fst a).
Proof.
  eexists; PrefixSearchTermFinder.
Qed.
Print foo10'.
Lemma foo13
: forall n : DNSRRecord, exists st, forall a : DNSRRecord,
    prefixBool (n!sNAME) (a!sNAME)  =
    PrefixSearchTermMatcher st a.
Proof.
  eexists; PrefixSearchTermFinder.
Qed.
Print foo13.

Lemma foo12 :
  forall l l' : name,
    prefixBool l l' = false ->
    ?[list_eq_dec string_dec l l'] = false.
Proof.
  intros; find_if_inside; subst;
  [ rewrite <- prefixBool_reflexive in H | ]; auto.
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
      unfold filtered_list; induction xs; intros.
      - reflexivity.
      - simpl; setoid_rewrite IHxs.
        simplify with monad laws.
        destruct (dec a) eqn: eq_dec_a;
          [ setoid_rewrite dec_decides_P in eq_dec_a; refine pick val true |
            setoid_rewrite Decides_false in eq_dec_a; refine pick val false ];
          auto; simplify with monad laws; reflexivity.
    Qed.

    Definition find_upperbound {A} (f : A -> nat) (ns : list A) : list A :=
      let max := fold_right
                   (fun n acc => max (f n) acc) O ns in
      filter (fun n => NPeano.leb max (f n)) ns.

    Lemma fold_right_max_is_max {A}
    : forall (f : A -> nat) ns n,
        List.In n ns -> f n <= fold_right (fun n acc => max (f n) acc) 0 ns.
    Proof.
      induction ns; intros; inversion H; subst; simpl;
      apply NPeano.Nat.max_le_iff; [ left | right ]; auto.
    Qed.

    Lemma fold_right_higher_is_higher {A}
    : forall (f : A -> nat) ns x,
        (forall r, List.In r ns -> f r <= x) ->
        fold_right (fun n acc => max (f n) acc) 0 ns <= x.
    Proof.
      induction ns; simpl; intros; [ apply le_0_n | ].
      apply NPeano.Nat.max_lub.
      apply H; left; auto.
      apply IHns; intros; apply H; right; auto.
    Qed.

    Lemma find_upperbound_highest_length {A}
    : forall (f : A -> nat) ns n,
        List.In n (find_upperbound f ns) -> forall n', List.In n' ns -> (f n) >= (f n').
    Proof.
      unfold ge, find_upperbound; intros.
      apply filter_In in H; destruct H; apply NPeano.leb_le in H1.
      rewrite <- H1; clear H1 H n.
      apply fold_right_max_is_max; auto.
    Qed.

    (* Lemma find_upperbound_upperbound {A}
    : forall (f : A -> nat) ns n, List.In n (find_upperbound f ns) <->
                                    List.In n ns /\ upperbound f ns n.
    Proof.
      unfold upperbound, ge; intros; split; intros; try split.
      - unfold find_upperbound in H; apply filter_List.In in H; tauto.
      - apply find_upperbound_highest_length; auto.
      - destruct H; unfold find_upperbound.
        apply filter_List.In; split; try assumption.
        apply NPeano.leb_le.
        pose proof (fold_right_max_is_max f _ _ H).
        pose proof (fold_right_higher_is_higher f _ H0).
        auto.
    Qed. *)

    Instance DecideableEnsembleUpperbound {A} (f : A -> nat) ns :
      DecideableEnsemble (upperbound f ns) :=
      {| dec n := NPeano.leb (fold_right (fun n acc => max (f n) acc) O ns) (f n) |}.
    Proof.
      unfold upperbound, ge; intros; rewrite NPeano.leb_le; intuition.
      - remember (f a); clear Heqn; subst; eapply le_trans;
        [ apply fold_right_max_is_max; apply H0 | assumption ].
      - eapply fold_right_higher_is_higher; eauto.
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
        (forall n', List.In n' ns -> prefixProp (get_name n') s)
        -> forall n n', List.In n (find_upperbound name_length ns)
                        -> List.In n' (find_upperbound name_length ns)
                        -> get_name n = get_name n'.
    Proof.
      unfold find_upperbound, name_length; intros ns s H0 n n' H H1.
      apply filter_In in H; destruct H; apply filter_In in H1; destruct H1.
      pose proof (H0 _ H); pose proof (H0 _ H1).
      apply NPeano.leb_le in H2; apply NPeano.leb_le in H3.
      pose proof (fold_right_max_is_max name_length ns n H) as H2'.
      pose proof (fold_right_max_is_max name_length ns n' H1) as H3'.
      unfold name_length in *.
      apply (le_antisym _ _ H2') in H2; apply (le_antisym _ _ H3') in H3.
      rewrite <- H2 in H3.
      unfold prefixProp in *; destruct H4; destruct H5; rewrite <- H5 in H4.
      clear H2' H3' H H2 H0 H1 H5 s ns.
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
        (forall n', List.In n' ns -> prefixProp (get_name n') s) ->
        refine {b : bool |
                decides b
                        (~
                           (exists x : DNSRRecord,
                              List.In x (find_upperbound name_length ns) /\ s <> (get_name x)))}
               (ret match find_upperbound name_length ns with
                      | nil => true
                      | n' :: _ => ?[s == (get_name n')]
                    end).
    Proof.
      computes_to_econstructor; simpl in H; intros; computes_to_inv.
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

    Lemma in_list_exists {A}
    : forall (xs : list A) x, List.In x xs -> exists n, nth_error xs n = Some x.
    Proof.
      intros; induction xs; inversion H; subst.
      exists 0; reflexivity.
      apply IHxs in H0; destruct_ex; exists (1 + x0); auto.
    Qed.

    Lemma in_list_preserve_filter {A}
    : forall (f : A -> bool) xs x, List.In x (filter f xs) -> List.In x xs.
    Proof.
      intros; apply (filter_In f x xs) in H; tauto.
    Qed.

    Lemma foo20
    : forall ns n s
             (HH : forall t t' n n', n <> n'
                                     -> nth_error ns n =  Some t
                                     -> nth_error ns n' = Some t'
                                     -> get_name t = get_name t'
                                     -> t!sTYPE <> CNAME),
        (forall n', List.In n' ns -> prefixProp (get_name n') s) ->
        refine {b' |
                forall b : Tuple,
                  b' = Some b <->
                  List.In b (find_upperbound name_length ns) /\
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
      unfold refine, not; intros; pose proof (foo16 ns H); clear H.
      remember (find_upperbound name_length ns) as l.
      computes_to_inv; computes_to_econstructor; split; intros.
      - destruct l; [ subst; inversion H | ].
        repeat find_if_inside_eqn; subst; try inversion H; subst.
        repeat split; [ simpl; left | symmetry | ]; auto.
      - destruct H as [? [? ?] ]; destruct l; [ inversion H | subst ].
        inversion H; unfold not in *.
        + repeat find_if_inside; subst; auto; exfalso; auto.
        + assert (d = b).
          * pose proof (in_eq d l).
            pose proof H; rewrite Heql in H5; pose proof (in_list_preserve_filter _ ns b H5); clear H5.
            pose proof H4; rewrite Heql in H5; pose proof (in_list_preserve_filter _ ns d H5); clear H5.
            pose proof (in_list_exists ns b H6); pose proof (in_list_exists ns d H7); destruct_ex; pose proof (H1 d b H4 H).
            destruct (beq_nat x0 x) eqn: eq; [ rewrite beq_nat_true_iff in eq; subst; rewrite H8 in H5; inversion H5; auto | ].
            rewrite beq_nat_false_iff in eq; symmetry in H9.
            pose proof (HH b d x0 x eq H5 H8 H9); exfalso; auto.
          * repeat find_if_inside; subst; [ exfalso; apply H3 | | exfalso; apply n0 ]; auto.
    Qed.

    Lemma refine_If_Opt_Then_Else_ret {A B} :
      forall i (t : A -> B) (e : B),
        refine (@If_Opt_Then_Else A (Comp B) i (fun a => ret (t a)) (ret e))
               (ret (@If_Opt_Then_Else A B i t e)).
    Proof.
      destruct i; reflexivity.
    Qed.

Lemma refine_decides_forall_In' :
  forall {A} l (P: A -> Prop) (P_Dec : DecideableEnsemble P),
    refine {b | decides b (forall (x: A), List.In x l -> P x)}
           {b | decides b (~ exists (x : A), List.In x l /\ ~ P x)}.
Proof.
  unfold refine; intros; computes_to_inv.
  computes_to_constructor.
  destruct v; simpl in *; intros.
  case_eq (dec x); intros; try rewrite <- (dec_decides_P); eauto.
  elimtype False; eapply H; eexists; intuition eauto.
  rewrite <- dec_decides_P in H2; congruence.
  unfold not in *; intros.
  eapply H; intros.
  destruct H1; intuition.
Qed.

Transparent FueledFix.
Opaque Query_For.

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
    setoid_rewrite refine_If_Then_Else_Bind.
    setoid_rewrite Bind_refine_If_Then_Else.
    etransitivity.
    apply refine_If_Then_Else.
    - simplify with monad laws.
      apply refine_under_bind; intros.
      setoid_rewrite refine_Count; simplify with monad laws.
      apply refine_under_bind; intros.
      (* remove duplicate check *)Check foo7.
      setoid_rewrite foo7; eauto.
      simplify with monad laws.
      rewrite foo8 by apply foo9.
      higher_order_1_reflexivity.
      eauto with typeclass_instances.
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
    implement_Query' ltac:(fun _ _ _ _ => PrefixSearchTermFinder) ltac:(fun _ _ _ _ _ => idtac).
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

      rewrite (@refine_decides_forall_In' _ _ _ _).

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
      simplify with monad laws.
      refine pick val _; eauto.
      simplify with monad laws.
      higher_order_1_reflexivity.
      simplify with monad laws.
      simpl.
      refine pick val _; eauto.
      simplify with monad laws.
      reflexivity.
      idtac.
      clear H.
      admit.
      simpl.
      intros.
      instantiate (1 := qname (questions n)).
      clear H.
      admit.
      simplify with monad laws.
      setoid_rewrite (@refine_filtered_list _ _ _ _).
      simplify with monad laws.
      refine pick val _; eauto.
      simplify with monad laws.
      reflexivity.
      reflexivity.
      intro.
      rewrite map_app, map_map; simpl.
      clear H.
      admit.
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
        implement_Query' ltac:(fun _ _ _ _ => PrefixSearchTermFinder) ltac:(fun _ _ _ _ _ => idtac).
        simplify with monad laws.
        setoid_rewrite refineEquiv_swap_bind.
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
      + simplify with monad laws.
        implement_Query' ltac:(fun _ _ _ _ => PrefixSearchTermFinder) ltac:(fun _ _ _ _ _ => idtac).
        simplify with monad laws.
        setoid_rewrite refineEquiv_swap_bind.
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
    - reflexivity.
    - finish honing.
  }
  FullySharpenQueryStructure DnsSchema
  (icons DnsSearchUpdateTerm
       (inil
          (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns))))).
  - implement_bag_methods.
  - implement_bag_methods.
Time Defined.

    Definition DnsDelegateReps
    : ilist (fun ns => Type) (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact (list (@Tuple
           <sNAME :: name, sTYPE :: RRecordType, sCLASS :: RRecordClass,
              sTTL :: nat, sDATA :: string>%Heading)).
    Defined.

    Definition DnsDelegateSearchUpdateTerms
    : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
             (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact  DnsSearchUpdateTerm.
    Defined.

    Require Import ADTSynthesis.QueryStructure.Automation.QSImplementation.

    Definition DnsDelegateImpls
    : i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                   (Rep : Type) =>
                 ComputationalADT.pcADT
                   (BagSig (@Tuple (schemaHeading (relSchema ns)))
                           (BagSearchTermType SearchTerm)
                           (BagUpdateTermType SearchTerm))
                   Rep)
              DnsDelegateSearchUpdateTerms
              DnsDelegateReps.
      simpl; econstructor; [ | econstructor ].
      let p := eval simpl in (projT2 (BagADTImpl (fun _ => true)
                         (@ListAsBag
                            _
                            (BagSearchTermType DnsSearchUpdateTerm)
                            (BagUpdateTermType DnsSearchUpdateTerm)
                            {| pst_name := nil;
                               pst_filter := fun _ => true |}
                            (BagMatchSearchTerm DnsSearchUpdateTerm)
                            (BagApplyUpdateTerm DnsSearchUpdateTerm) ))) in
          exact p.
    Defined.

    Definition DnsImpl : SharpenedUnderDelegates DnsSig.
      Time let
          Impl := eval simpl in (projT1 DnsManual) in exact Impl.
    Defined.

    Print DnsImpl.
    Definition ExtractWorthyDNSImpl : ComputationalADT.cADT DnsSig.
      let s := eval unfold DnsImpl in DnsImpl in
          let Impl := eval simpl in
          (Sharpened_Implementation s
                                    (LookupQSDelegateReps DnsDelegateReps)
                                    (LookupQSDelegateImpls DnsDelegateImpls)) in exact Impl.
    Defined.

    Print ExtractWorthyDNSImpl.

    Extraction "bar.ml" ExtractWorthyDNSImpl.
