Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindSuffixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.packet.

Open Scope list.


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
(* -------------------------------------------------------------------------------------- *)

(* Refinement lemmas *)

(* First, lemmas that help with honing the AddData method in DnsManual. They're related to implementing the data constraint (on DnsSchema) as a query. *)


(* if the record's type isn't CNAME, there's no need to check against the other records;
it's independent of the other records *)
Lemma refine_not_CNAME__independent :
  forall (n : DNSRRecord) (R : @IndexedEnsemble DNSRRecord),
    n!sTYPE <> CNAME
    -> refine {b |
               decides b
                       (forall tup' : IndexedTuple,
                          R tup' ->
                          n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}

              (ret true).
Proof.
  (* where are pick and val from? *)
  intros; refine pick val true; [ reflexivity | simpl; intros; assumption ].
Qed.

(* if the record's type *is* CNAME, then refine the forall check against other records into
an existential (exists a record with the same name), and return the opposite *)
Lemma refine_is_CNAME__forall_to_exists :
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

(* very similar to refine_is_CNAME__forall_to_exists;
they start with the same set, but refine_forall_to_exists refines it with an extra end condition. changes the (forall x, ~P x) check into (exists x, P x) and returns !x, adding the condition in the forall *)
Lemma refine_forall_to_exists :
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
Proof.                          (* same proof as refine_is_CNAME__forall_to_exists *)
  repeat match goal with
    | _ : _ ↝ _ |- _ => computes_to_inv
    | _ : negb ?v = _ |- _ => destruct v; simpl in *; subst
    | _ : ex _ |- _ => destruct_ex
    | _ => progress first [ intro | computes_to_econstructor | simpl; intuition; eauto ]
         end.
Qed.


(* implement the DNS record constraint check as code that counts the number of occurrences of
the constraint being broken (refines the boolean x1 in AddData) *)
Lemma refine_count_constraint_broken :
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
  [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
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

Hint Resolve refine_count_constraint_broken.

(* in AddData, simplifies x1 from large For/Where/Return expression to [ret (filter dec a0)] *)

(* refine a check into a filter, given the results of a sub-check
uses P' decision procedure invisibly in DecideableEnsembles.dec by the magic of typeclasses
(try Set Printing Implicit) *)
Lemma refine_subcheck_to_filter {heading}
: forall (R : Ensemble (@IndexedTuple heading))
         (P : Ensemble Tuple) (P_dec : DecideableEnsemble P)
         (l : list Tuple),
    For (QueryResultComp
           R
           (fun tup => Where (P tup) (* tuple is in P *)
                             (Return tup))) ↝ l  ->
    forall (P' : Ensemble Tuple) (P'_dec : DecideableEnsemble P'),
      refine
        (* assumption: subexpression with only [P tup] computes to l *)
        (* note: P, P' are sets of tuples *)
        (For (QueryResultComp
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

(* uses refine_forall_to_exists; refines x2 in AddData 
very similar to refine_count_constraint_broken; comments below are relative to refine_count_constraint_broken *)

(* implement the DNS record constraint check as code that counts the number of occurrences of
the constraint being broken (refines the boolean x1 in AddData) *)
(* TODO [autorewrite with monad laws] breaks in this file *)

(*
Lemma refine_count_constraint_broken :
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
  [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
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
*)

(* uses refine_forall_to_exists; refines x2 in AddData
very similar to refine_count_constraint_broken; comments below are relative to refine_count_constraint_broken *)

Definition bCOLLECTIONS : Fin.t _ :=
  ibound (indexb (@Build_BoundedIndex string (numQSschemaSchemas DnsSchema)
                                      (QSschemaNames DnsSchema) sCOLLECTIONS _)).

Lemma refine_count_constraint_broken' :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (GetUnConstrRelation r bCOLLECTIONS) tup' ->
                       (indexedElement tup')!sNAME = n!sNAME (* switched *)
                       -> (indexedElement tup')!sTYPE <> CNAME)} (* indexedElement tup', not n *)
           (* missing the If/Then statement *)
           (count <- Count
                  For (UnConstrQuery_In r bCOLLECTIONS
                                        (fun tup : Tuple =>
                                           Where (n!sNAME = tup!sNAME
                                                  /\ tup!sTYPE = CNAME ) (* extra /\ condition *)
                                                 Return tup ));
            ret (beq_nat count 0)).
Proof.
  intros; setoid_rewrite refine_forall_to_exists.
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

(* clear_nested_if, using filter_nil_is_nil, clear the nested if/then in honing AddData *)
Lemma clear_nested_if {A}
: forall (c c' : bool) (t e e' : A),
    (c = true -> c' = true)
    -> (if c then (if c' then t else e) else e') = if c then t else e'.
Proof.
  intros; destruct c; destruct c'; try reflexivity.
  assert (true = true); [ reflexivity | apply H in H0; discriminate ].
Qed.

(* if a list is empty, the result of filtering the list with anything will still be empty *)
Lemma filter_nil_is_nil {A}
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

(*Ltac PrefixSearchTermFinderEqSolve :=
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
    ?[IsPrefix_dec l l'] = false ->
    ?[list_eq_dec string_dec l l'] = false.
Proof.
  intros; find_if_inside; subst.
  [ rewrite <- prefix_reflexive in H | ]; auto.
Qed.

Lemma foo11 {heading}
: forall l,
    map (ilist_hd (As:=cons heading nil ))
        (Build_single_Tuple_list l) = l.
Proof.
  induction l; simpl; congruence.
Qed. *)

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

    Lemma eqListA_eq {A}:
      forall l l0 : list A,
        SetoidList.eqlistA eq l l0 <-> l = l0.
    Proof.
      induction l; split; intros; inversion H; subst; eauto.
      - f_equal; eapply IHl; eauto.
      - f_equiv.
    Qed.

    (* used in refine_check_one_longest_prefix_s and refine_check_one_longest_prefix_CNAME *)
    Lemma all_longest_prefixes_same :
      forall (ns : list DNSRRecord) (s : list string),
        (* the name (list string) of every record in the list is a prefix
           of the given name (list string) *)
        (* e.g. [com.google, com.google.us, com.google.us.scholar] with s = com.google.us.scholar *)
        (forall (n' : DNSRRecord), List.In n' ns -> IsPrefix (get_name n') s)

        (* for two records, if they both have the longest names in the list of records
           (AND as before, they are prefixes of s)
         then their names must be the same *)
        -> forall n n' : DNSRRecord, List.In n (find_upperbound name_length ns)
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
      unfold IsPrefix in *; destruct H4; destruct H5; rewrite <- H5 in H4.
      clear H2' H3' H H2 H0 H1 H5 s ns.
      remember (get_name n); remember (get_name n'); clear Heql Heql0.
      (* if 2 lists have the same length and are both prefixes of some list, they are the same list *)
      apply eqListA_eq in H4.
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

    (* ------------------ *)

    (* These 3 lemmas relating to prefixes help hone the Process method in DnsManual *)

    (* Implement the check for an exact match *)
    (* uses all_longest_prefixes_same *)
    Lemma refine_check_one_longest_prefix_s
    : forall (ns : list DNSRRecord) (s : list string),
        (* the name (list string) of every record in the list is a prefix
           of the given name (list string) *)
        (forall n' : DNSRRecord, List.In n' ns -> IsPrefix (get_name n') s) ->

        (* there exists no record such that it is one of the longest prefixes of the name
           AND is not the name itself -- refines to a computation that just checks the first
           the name against the first longest prefix found. it's ok to just check the first
           due to all_longest_prefixes_same: all longest prefixes must be the same *)
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
      subst; unfold decides; pose proof (all_longest_prefixes_same ns H); clear H.
      remember (find_upperbound name_length ns) as l.
      unfold If_Then_Else.
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

    Lemma exists_in_list {A}
    : forall (xs : list A) x, (exists n, nth_error xs n = Some x) -> List.In x xs.
    Proof.
      intros. revert x H.
      induction xs; intros.
      - destruct H. destruct x0; inversion H.
      - simpl in *. destruct H. destruct x0.
        * left. inversion H. auto.
        * right. apply IHxs. eexists. apply H.
    Qed.

    Lemma in_list_preserve_filter {A}
    : forall (f : A -> bool) xs x, List.In x (filter f xs) -> List.In x xs.
    Proof.
      intros; apply (filter_In f x xs) in H; tauto.
    Qed.

    (* uses all_longest_prefixes_same; very similar to refine_check_one_longest_prefix_s but with an extra condition/Tuple type *)
    Lemma refine_check_one_longest_prefix_CNAME
    : forall (ns : list DNSRRecord) (n : RRecordType) (s : list string)
             (HH : forall (t t' : DNSRRecord) (n n' : nat),
                 n <> n'
                 -> nth_error ns n  = Some t
                 -> nth_error ns n' = Some t'
                 -> get_name t      = get_name t'
                 -> t!sTYPE <> CNAME),
        (* forall HH? *)

        (* as before, the name (list string) of every record in the list is a prefix
           of the given name (list string) *)
        (forall n' : DNSRRecord, List.In n' ns -> IsPrefix (get_name n') s) ->

        (* Tuple type instead of record?
        all "records" that contain the longest prefixes and are not CNAME, and n isn't CNAME  *)
        (* this should be generalized to {b | List in ... /\ P} => match (...) with (P first one) *)
        refine {b' : option Tuple |
                forall b : Tuple,
                  b' = Some b <->
                  List.In b (find_upperbound name_length ns) /\
                  b!sTYPE = CNAME /\ n <> CNAME}
               (* refines to just checking the condition (with booleans) on the first longest prefix
                using all_longest_prefixes_same *)
               (ret match (find_upperbound name_length ns) with
                      | nil => None
                      | n' :: _ => if CNAME == (n'!sTYPE)
                                   then if n == CNAME
                                        then None
                                        else Some n'
                                   else None
                    end).
    Proof.
      unfold refine, not; intros; pose proof (all_longest_prefixes_same ns H); clear H.
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
            (* HH instantiated here *)
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

(* ------------------------------ *)

Ltac inv H := inversion H; clear H; try subst.

(* Helper lemmas for tuples_in_relation_satisfy_constraint_specific *)

Lemma flatmap_permutation : forall heading l1 (l2 : list (@RawTuple heading)),
    In _ (FlattenCompList.flatten_CompList
            (map (fun r : @RawTuple heading => Return r) l2)) l1
    -> Permutation l1 l2.
Proof.
  intros. revert l1 H.
  induction l2; intros; destruct l1; intros; simpl in *;
  try reflexivity; inv H; (inv H0; inv H1; inv H0; inv H2; inv H).
  - inv H3.
  - rewrite app_singleton. auto.
Qed.

Lemma flatmap_permutation' : forall heading (l : list (@RawTuple heading)),
    In _ (@FlattenCompList.flatten_CompList (@RawTuple heading)
     (@map (@RawTuple heading) (Comp (list (@RawTuple heading)))
        (fun r : @RawTuple heading => @Query_Return (@RawTuple heading) r) l))
     l.
Proof.
  intros.
  induction l; simpl. Transparent ret.
  - unfold ret. apply In_singleton.
  - Transparent Bind.
    unfold Bind in *.
    unfold In in *.
    eexists.
    split.
    * unfold Query_Return in *.
      unfold ret.
      apply In_singleton.
    * exists l.
      split.
      + auto.
      + unfold ret.
        rewrite app_singleton.
        apply In_singleton.
        Opaque ret. Opaque Bind.
Qed.

Definition UnIndexedEnsembleListExists
           (ElementType : Type) (ensemble : @IndexedEnsemble ElementType) :=
  exists lIndexed : list (@IndexedElement ElementType),
    exists lElems : list ElementType,
      map indexedElement lIndexed = lElems /\
      (forall x : IndexedElement, In IndexedElement ensemble x <-> List.In x lIndexed) /\
      NoDup (map elementIndex lIndexed).

Lemma nth_error_map' {A B}
  : forall (f : A -> B) l m b,
    nth_error (map f l) m = Some b ->
    exists a, nth_error l m = Some a /\ f a = b.
Proof.
  induction l; destruct m; simpl; intros; try discriminate;
  injections; eauto.
Qed.

Lemma unindexed_OK_exists_index' heading :
  forall x lIndexed (t t' : @Tuple heading) n n',
      n <> n'
      -> nth_error x n = Some t
      -> nth_error x n' = Some t'
      -> Permutation x (map indexedElement lIndexed)
      -> exists m m' idx idx',
          m <> m'
          /\ nth_error lIndexed m = Some {| elementIndex := idx; indexedElement := t |}
          /\ nth_error lIndexed m' = Some {| elementIndex := idx'; indexedElement := t' |}.
Proof.
  intros.
  eapply PermutationFacts.permutation_map_base in H2; intuition eauto.
  destruct_ex; intuition; subst.
  revert t t' n n' H H0 H1; induction H4; intros.
  - destruct n; simpl in *; discriminate.
  - destruct n; destruct n'; simpl in *.
    + intuition.
    + assert (exists m', nth_error (map indexedElement l') m' = Some t') by
          (eapply in_list_exists; rewrite <- H4; eapply exists_in_list; eauto).
      destruct H2.
      eapply nth_error_map' in H2; destruct_ex; intuition.
      injections.
      eexists 0, (S x0), (elementIndex x), (elementIndex x1); intuition; simpl; eauto.
      destruct x; eauto.
      rewrite H3; destruct x1; eauto.
    + assert (exists m, nth_error (map indexedElement l') m = Some t) by
          (eapply in_list_exists; rewrite <- H4; eapply exists_in_list; eauto).
      destruct H2.
      eapply nth_error_map' in H2; destruct_ex; intuition.
      injections.
      eexists (S x0), 0, (elementIndex x1), (elementIndex x); intuition; simpl; eauto.
      rewrite H3; destruct x1; eauto.
      destruct x; eauto.
    + destruct (IHPermutation t t' n n') as [m [m' [idx [idx' ?] ] ] ]; eauto.
      eexists (S m), (S m'), idx, idx'; simpl; intuition eauto.
  - eapply nth_error_map' in H0; destruct_ex; intuition.
    eapply nth_error_map' in H1; destruct_ex; intuition.
    rewrite <- H3, <- H4; destruct x0; destruct x1; simpl in *.
    destruct n as [ | [ | n ] ];  destruct n' as [ | [ | n' ] ];
    injections; simpl in *.
    + intuition.
    + eexists 1, 0, _, _; simpl; eauto.
    + eexists 1, (S (S n')), _, _; simpl; repeat split; try eassumption; omega.
    + eexists 0, 1, _, _; simpl; eauto.
    + intuition.
    + eexists 0, (S (S n')), _, _; simpl; repeat split; try eassumption; omega.
    + eexists (S (S n)), 1, _, _; simpl; repeat split; try eassumption; omega.
    + eexists (S (S n)), 0, _, _; simpl; repeat split; try eassumption; omega.
    + eexists (S (S n)), (S (S n')), _, _; simpl; repeat split; try eassumption; omega.
  -  destruct (IHPermutation1 _ _ _ _ H H0 H1) as [m [m' [idx [idx' ?] ] ] ];
    intuition.
     clear H.
     eapply IHPermutation2; eauto.
     eapply map_nth_error with (f := indexedElement) in H2; simpl in *; eauto.
     eapply map_nth_error with (f := indexedElement) in H5; simpl in *; eauto.
Qed.

Check QueryResultComp.

Lemma In_Where_Intersection heading
  : forall R P (P_dec : DecideableEnsemble P) x,
    computes_to
      (QueryResultComp R (fun r => Where (P r)
                                         Return r)) x ->
    computes_to
      (QueryResultComp (Intersection (@IndexedRawTuple heading) R
                                      (fun r => (P (indexedElement r)))) (fun r => Return r)) x.
Proof.
  unfold In, QueryResultComp; intros.
  repeat computes_to_inv.
  revert R x H H'.
  induction v; simpl in *; intros; computes_to_inv; subst.
  - repeat computes_to_econstructor.
    instantiate (1 := @nil RawTuple); simpl.
    inversion H; intuition; subst.
    econstructor; split; eauto.
    repeat split; intros; eauto.
    eapply H0; inversion H2; subst; eauto.
    eapply H0; eauto.
    eapply in_map with (f := indexedElement) in H2; rewrite H1 in H2; destruct H2.
    computes_to_econstructor.
  - inversion H; destruct x; simpl in *; intuition;
    try discriminate; injections.
    assert (UnIndexedEnsembleListEquivalence
              (fun t : IndexedRawTuple => elementIndex t <> elementIndex i
                                       /\ R t) (map indexedElement x)).
    { econstructor; intuition eauto.
      inversion H1; subst.
      apply H0 in H4; intuition.
      subst; intuition eauto.
      econstructor; intros; subst.
      inversion H3; subst.
      apply H6; eapply in_map_iff.
      eexists; split; eauto.
      eapply H0; eauto.
      inversion H3; subst; eauto.
    }
    pose proof (IHv _ _ H1 H''); clear IHv; computes_to_inv.
    inversion H'; subst.
    refine pick val (v0 ++ v).
    econstructor; intuition; eauto.
    rewrite map_app; eapply FlattenCompList.flatten_CompList_app; eauto.
    case_eq (dec (indexedElement i)); intros.
    apply dec_decides_P in H6; apply H4 in H6; inversion H6; subst.
    repeat computes_to_econstructor.
    eapply Decides_false in H6; apply H5 in H6; subst; simpl;
    computes_to_econstructor.
    inversion H2; subst; intuition.
    case_eq (dec (indexedElement i)); intros.
    + apply dec_decides_P in H8; pose proof (H4 H8) as H'''; inversion H'''; subst.
      econstructor 1.
      instantiate (1 := [i] ++ x0); simpl; intuition eauto.
      inversion H4; subst; apply H0 in H10; intuition.
      right; eapply H6; econstructor; unfold In; eauto.
      split; eauto; intros; subst.
      inversion H3; subst; intuition eauto.
      apply H15; eapply in_map_iff.
      eexists; eauto.
      eapply H0; eauto.
      subst.
      econstructor.
      eapply H0; eauto.
      unfold In; eauto.
      econstructor; unfold In in *; eauto.
      eapply H0; eauto.
      rewrite <- H6 in H10; inversion H10; subst; unfold In in *; intuition.
      eapply H0 in H13; eauto.
      rewrite <- H6 in H10; inversion H10; subst; unfold In in *; intuition.
      inversion H3; subst; econstructor; eauto.
      intro; rewrite in_map_iff in H4; destruct_ex; intuition eauto.
      apply H11; rewrite in_map_iff; destruct_ex; intuition eauto.
      eexists; intuition eauto.
      eapply H6 in H13; inversion H13; subst.
      unfold In in H13.
      inversion H13; subst.
      inversion H15; subst; intuition.
    + eapply Decides_false in H8; pose proof (H5 H8); subst; simpl.
      inversion H2; subst; intuition.
      econstructor 1.
      instantiate (1 := x1); intuition eauto.
      eapply H7.
      repeat econstructor; eauto.
      destruct H5; subst.
      apply H0 in H5; intuition.
      subst; intuition.
      inversion H3; subst.
      apply H17; apply in_map_iff; eexists; eauto.
      destruct H5; eauto.
      destruct H5; eauto.
      eapply H7 in H5; destruct H5; destruct H5.
      econstructor; eauto.
Qed.

Theorem IsSuffix_string_dec :
  forall l1 l2 : list string, IsPrefix l1 l2 \/ ~ IsPrefix l1 l2.
Proof.
  intros.
  destruct (IsPrefix_dec l1 l2); eauto.
Qed.

(* Main lemma -- TODO generalize *)

(* but Exc = option? broke because I changed the type of sDATA in DNSRRecord? *)
(* Set Printing All. *)

Lemma tuples_in_relation_satisfy_constraint_specific :
  forall (a : list RawTuple) (n : packet) (r_n : QueryStructure DnsSchema),
(* TODO *)
    For (r in r_n!sCOLLECTIONS)
        (Where (IsPrefix r!sNAME (qname (questions n)))
               Return r ) ↝ a ->
  forall (t t' : DNSRRecord) (n0 n' : nat),
    n0 <> n' ->
    nth_error a n0 = Some t -> (* this isn't right? *)
    nth_error a n' = Some t' ->
    get_name t = get_name t' ->
    t!sTYPE <> CNAME.
Proof.
  intros. inversion H. inv H4.

  assert (forall l,
             In (list RawTuple)
                (let qs_schema := DnsSchema in
                 let r' := r_n in
                 Query_In r' bCOLLECTIONS
                          (fun r : RawTuple =>
                             Return r )) l
             ->  List.incl x l).
  {
  (* need to use the main H5 too, with the filter
this is because x is a list of tuples that all came from r *)
  clear t t' n0 H0 H1 H2 H3 H n'.
  remember H5 as inFilter. clear HeqinFilter H5.
  intros l inRelation.
  inversion inFilter.
  inv H.
  simpl in *.

  inv H0.
  (* H : x0 (new) is x1 without indices, and all indices in x1 are unique, and
     forall x2 (new) : indexedelement, it's in sCOLLECTIONS if and only if it's in x1, the list of indexed elements  *)

  inv H.
  inv H2.
  remember (map elementIndex x1) as x0.

  inversion inRelation.
  inversion H2. clear H2. inversion H3. clear H3.
  inversion H2. clear H2. inversion H5. clear H5.
  simpl in *.             (* TODO ltac for these inversions and reasoning about them *)

  unfold incl.
  subst. (* optional *)

  intros filterElem filterH.
  remember (map indexedElement x3) as x3elems.

  assert (exists feIndex,
     List.In {| elementIndex := feIndex; indexedElement := filterElem |} x1).
  {
  remember (map indexedElement x1) as x1elems.

  (* this is the real nub of the proof *)
  assert (List.incl x x1elems).
  {
    unfold incl.
    intros xElem. intro.
    match type of H1 with
    | appcontext[map (fun r : @RawTuple ?H => (Where (@?H1 r) _))] =>
      pose proof (In_flatten_CompList H1) as in_flatten
    end.

    assert ((exists a' : IndexedElement,
                 List.In a' x1 /\ indexedElement a' = xElem) -> List.In xElem x1elems).
    {
    intros.
    inversion H5. clear H5.
    inversion H8. clear H8.
    rewrite <- H9.
    rewrite Heqx1elems.
    apply in_map_iff.
    eexists.
    split.
    reflexivity.
    auto. }

    apply H5. clear H5.

    eapply in_flatten; eauto using IsSuffix_string_dec.

    rewrite Heqx1elems in H1.
    rewrite List.map_map in H1.
    unfold In in H1.
    apply H1.
  }

  unfold incl in H3.
  specialize (H3 filterElem).

  (* alternate version *)
  assert (List.In filterElem x1elems ->
          exists index, List.In {| elementIndex := index; indexedElement := filterElem |} x1).
  {
  intros.
  rewrite Heqx1elems in H5.
  apply in_map_iff in H5.
  destruct H5.
  destruct H5.

  destruct x0.
  simpl in *.
  rewrite H5 in H8.
  exists elementIndex.
  apply H8. }

  specialize (H3 filterH).
  specialize (H5 H3).
  destruct H5 as [index].
  exists index.
  apply H5.
  }

  (* ------------------------ *)

  destruct H3 as [feIndex].                  (* new *)

  remember (Build_IndexedElement feIndex filterElem) as indexedFilterElem.
  specialize (H2 indexedFilterElem).
  specialize (H indexedFilterElem).

  inversion H. clear H.
  inversion H2. clear H2.

  specialize (H8 H3).
  specialize (H H8).

  clear H5 H8 H9.

  eapply Permutation_in.
  apply Permutation_sym.
  apply flatmap_permutation; eauto.

  (* there's probably something I can do with indices to remove this step *)
  assert (List.In indexedFilterElem x3 -> List.In filterElem (map indexedElement x3)) as H5.
  { intros.
    apply in_map_iff.
    exists indexedFilterElem.
    split.
    - rewrite HeqindexedFilterElem. reflexivity.
    - auto. }

  rewrite <- Heqx3elems in *.
  apply H5. apply H.
 }                              (* ends List.incl x l *)
(* ------------------------------------------------------------------------------------ *)

  assert (Permutation a x) by (symmetry; apply H6).

(* prove that everything in a is in sCOLLECTIONS *)
  assert (forall l,
             In (list RawTuple)
                (let qs_schema := DnsSchema in
                 let r' := r_n in
                 Query_In r' bCOLLECTIONS (fun r : RawTuple => Return r)) l ->
             incl a l).
  {
    (* x \subset sCOLLECTIONS, and Permutation a x *)
    intros allTuplesInRelation inRelation.

    unfold incl.
    intros aTuple inA.
    unfold incl in H4.

    clear H H5. clear t t' n0 n' H0 H1 H2 H3.

    specialize (H4 allTuplesInRelation inRelation aTuple).
    apply H4.
    eapply Permutation_in.
    apply H7. auto.
  }

(* use the proof that the constraints hold on everything in sC, therefore on a *)
(* t and t' are in a, therefore the constraint must hold on them *)
  (* this is the top-level goal  *)

  assert (List.In t a).
  { apply exists_in_list. exists n0. auto. }
  assert (List.In t' a).
  { apply exists_in_list. exists n'. auto. }

  assert (List.In t x).
  { eapply Permutation_in. apply H7. auto. }
  assert (List.In t' x).
  { eapply Permutation_in. apply H7. auto. }

  eapply In_Where_Intersection in H5; eauto with typeclass_instances.
  unfold QueryResultComp in H5; computes_to_inv.
  destruct H5 as [x' [Equiv [Equiv' Equiv''] ] ].
  rewrite <- Equiv in *.
  eapply flatmap_permutation in H5'; rewrite H5' in H7.
  destruct (unindexed_OK_exists_index' _ _ H0 H1 H2 H7) as [m [m' [idx [idx' ?] ] ] ];
    intuition.

  pose proof (rawTupleconstr (ith2 (rawRels r_n) (Fin.F1 ))) as
      constraint_in_relation_OK; simpl in *.
  apply (constraint_in_relation_OK {| elementIndex := idx; indexedElement := t |}
                                   {| elementIndex := idx'; indexedElement := t' |});
    simpl; try eassumption.

  eapply map_nth_error with (f := elementIndex) in H5.
  eapply map_nth_error with (f := elementIndex) in H16.
  {
    revert m m' H5 H16 H14 Equiv''; clear; unfold Tuple; simpl; induction (map elementIndex x').
  - destruct m; destruct m'; simpl; intros; try discriminate.
  - destruct m; destruct m'; simpl; intros; try discriminate.
    + intuition.
    + inversion Equiv''; subst.
      intro; subst; apply H1; injections; apply exists_in_list; eauto.
    + inversion Equiv''; subst.
      intro; subst; apply H1; injections; apply exists_in_list; eauto.
    + inversion Equiv''; eauto.
}

assert (List.In {| elementIndex := idx; indexedElement := t |} x').
  { eapply exists_in_list; eauto. }
  apply Equiv' in H15; destruct H15; apply H15.
  assert (List.In {| elementIndex := idx'; indexedElement := t' |} x').
  { eapply exists_in_list; eauto. }
  apply Equiv' in H15; destruct H15;  apply H15.
Qed.
(* -------------------------------------------------------------------------------------- *)

(* TODO: more general lemmas (hard to state w/ implicits; do later) *)
(*
  [for?] ((x in R) return x ~> l) ->
  forall n0 n1, nth n0 l = tup0 -> nth n0 l = tup1 ->
  tuple_constr tup0 tup1 *)

(*Lemma tuples_in_relation_satisfy_constraint :
    True.
Proof.

Admitted. *)

(* general lemma to prove, #2: deal with [where]
  (since [where] is just filtering/taking a subset, it should
  preserve the constraint/relation stuff)
  ([for?] (x in R)
      [WHERE (P x)]
  return x ~> l) ->
  forall n0 n1, nth n0 l = tup0 -> nth n0 l = tup1 ->
  tuple_constr tup0 tup1 *)

Lemma tuples_in_relation_filtered_satisfy_constraint :
  True.
Proof.

Admitted.


Lemma computes_to_in_specific : forall a n r_n,
 @computes_to
         (list
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute)))))))))
         (@Query_For
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute))))))))
            (@Query_In
               (@Tuple
                  (BuildHeading
                     (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sTYPE RRecordType)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sCLASS RRecordClass)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTTL nat)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sDATA string)
                                    (@Datatypes.nil Attribute))))))))
               (@Build_QueryStructureHint DnsSchema r_n)
               (@Build_BoundedIndex string
                  (@Datatypes.cons string sCOLLECTIONS
                     (@Datatypes.nil string)) sCOLLECTIONS
                  (@Build_IndexBound string sCOLLECTIONS
                     (@Datatypes.cons string sCOLLECTIONS
                        (@Datatypes.nil string)) O
                     (@eq_refl (option string) (@Some string sCOLLECTIONS))))
               (fun
                  r : @Tuple
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) =>
                @Query_Where
                  (@Tuple
                     (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute))))))))
                  (@IsSuffix string (qname (questions n))
                     (@GetAttribute
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) r
                        (@Build_BoundedIndex string
                           (@Datatypes.cons string sNAME
                              (@Datatypes.cons string sTYPE
                                 (@Datatypes.cons string sCLASS
                                    (@Datatypes.cons string sTTL
                                       (@Datatypes.cons string sDATA
                                          (@Datatypes.nil string)))))) sNAME
                           (@Build_IndexBound string sNAME
                              (@Datatypes.cons string sNAME
                                 (@Datatypes.cons string sTYPE
                                    (@Datatypes.cons string sCLASS
                                       (@Datatypes.cons string sTTL
                                          (@Datatypes.cons string sDATA
                                             (@Datatypes.nil string)))))) O
                              (@eq_refl (option string) (@Some string sNAME))))))
                  (@Query_Return
                     (@Tuple
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute)))))))) r))))
         a
 ->
   forall n' : DNSRRecord, 
   @List.In DNSRRecord n' a -> @IsPrefix string (get_name n') (qname (questions n)).
Proof.
  intros. 
  eapply For_computes_to_In in H; try eauto.
  inv H.
  + eauto. 
  + pose proof IsSuffix_string_dec. intros. auto.
Qed.

