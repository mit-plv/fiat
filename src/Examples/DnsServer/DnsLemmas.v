Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.Computation.ListComputations
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation
        Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.DecomposeSumField
        Fiat.Computation.FoldComp
        Fiat.Examples.DnsServer.AuthoritativeDNSSchema.

Open Scope list_scope.

Lemma beq_OurRRecordType_dec :
  forall rr rr', ?[OurRRecordType_dec rr rr'] = beq_OurRRecordType rr rr'.
Proof.
  intros; find_if_inside; subst.
  symmetry; apply (fin_beq_refl rr').
  symmetry; eapply fin_beq_neq_dec; eauto.
Qed.

(* Instances used in DecideableEnsemble. *)
Global Instance Query_eq_OurRRecordType :
  Query_eq OurRRecordType := {| A_eq_dec := OurRRecordType_dec |}.


Lemma beq_RRecordType_dec :
  forall rr rr', ?[RRecordType_dec rr rr'] = beq_RRecordType rr rr'.
Proof.
  intros; find_if_inside; subst.
  symmetry; apply (fin_beq_refl rr').
  symmetry; eapply fin_beq_neq_dec; eauto.
Qed.

(* Instances used in DecideableEnsemble. *)
Global Instance Query_eq_RRecordType :
  Query_eq RRecordType := {| A_eq_dec := RRecordType_dec |}.

Global Instance Query_eq_name :
  Query_eq DomainName := {| A_eq_dec := string_dec |}.

Lemma beq_QType_dec :
  forall a b, ?[QType_dec a b] = beq_QType a b.
Proof.
  intros; find_if_inside; subst.
  eauto using fin_beq_refl.
  symmetry; eapply fin_beq_neq_dec; eauto.
Qed.

(* Instances used in DecideableEnsemble. *)
Global Instance Query_eq_QType :
  Query_eq QType := {| A_eq_dec := QType_dec |}.

Global Instance Query_eq_RRecordClass :
  Query_eq RRecordClass := {| A_eq_dec := RRecordClass_dec |}.

Global Instance Query_eq_QClass :
  Query_eq QClass := {| A_eq_dec := QClass_dec |}.

Global Instance Query_eq_ResponseCode :
  Query_eq ResponseCode := {| A_eq_dec := ResponseCode_dec |}.

Global Instance Query_eq_OpCode :
  Query_eq OpCode := {| A_eq_dec := OpCode_dec |}.

(* Refinement lemmas *)

(* First, lemmas that help with honing the AddData method in DnsManual. They're related to implementing the data constraint (on DnsSchema) as a query. *)

(* if the record's type isn't CNAME, there's no need to check against the other records;
it's independent of the other records *)

Lemma refine_not_CNAME__independent :
  forall (n : resourceRecord) (R : @IndexedEnsemble resourceRecord),
    RDataTypeToRRecordType (n!sRDATA) <> CNAME
    -> refine {b |
               decides b
                       (forall tup' : IndexedTuple,
                           R tup' ->
                           n!sNAME= (indexedElement tup')!sNAME -> RDataTypeToRRecordType (n!sRDATA) <> CNAME)}

              (ret true).
Proof.
  (* where are pick and val from? *)
  intros; refine pick val true; [ reflexivity | simpl; intros; assumption ].
Qed.

Lemma refine_forall_to_exists {A}
  : forall (P Q : A -> Prop)
           (R : @IndexedEnsemble A)
           (P_dec : DecideableEnsemble P),
    refine {b |
            decides b
                    (forall tup' : @IndexedElement A,
                        R tup'
                        -> Q (indexedElement tup')
                        -> P (indexedElement tup'))}
           (b <- {b |
                  decides b
                          (exists tup' : @IndexedElement A,
                              R tup' /\
                              Q (indexedElement tup')
                              /\ ~ P (indexedElement tup'))};
              ret (negb b)).
Proof.
  unfold refine; intros; computes_to_inv; subst.
  destruct v0; simpl in *;
    computes_to_econstructor; simpl; unfold not; intros.
  - destruct_ex; intuition.
  - destruct (dec (indexedElement tup')) eqn: ?.
    rewrite dec_decides_P in Heqb; eauto.
    rewrite Decides_false in Heqb.
    elimtype False; eauto.
Qed.

Lemma refine_forall_to_exists_independent {A}
  : forall n (P P' Q : A -> Prop) (R : @IndexedEnsemble A),
    (P' n -> ~ P n)
    -> P n
    -> refine {b |
               decides b
                       (forall tup' : @IndexedElement A,
                           R tup' ->
                           Q (indexedElement tup') -> P' n)}
              (b <- {b |
                     decides b
                             (exists tup' : @IndexedElement A,
                                 R tup' /\
                                 Q (indexedElement tup'))};
                 ret (negb b)).
Proof.
  intros.
  rewrite (@refine_forall_to_exists _ (fun _ => P' n)).
  unfold refine; intros; computes_to_inv; subst.
  refine pick val v0.
  computes_to_econstructor; eauto.
  destruct v0; simpl in *.
  - destruct_ex; eexists; intuition eauto.
  - intro; apply H1; destruct_ex; eexists; intuition eauto.
  - eapply Build_DecideableEnsemble with (fun _ => false);
      split; intros; eauto.
    + discriminate.
    + intuition.
Qed.

(* if the record's type *is* CNAME, then refine the forall check against other records into
an existential (exists a record with the same name), and return the opposite *)
Lemma refine_is_CNAME__forall_to_exists :
  forall (n : resourceRecord) (R : @IndexedEnsemble resourceRecord),
    RDataTypeToRRecordType (n!sRDATA) = CNAME
    -> refine {b |
               decides b
                       (forall tup' : IndexedTuple,
                           R tup' ->
                           n!sNAME = (indexedElement tup')!sNAME -> RDataTypeToRRecordType (n!sRDATA) <> CNAME)}
              (b <- {b |
                     decides b
                             (exists tup' : IndexedTuple,
                                 R tup' /\
                                 n!sNAME = (indexedElement tup')!sNAME)};
                 ret (negb b)).
Proof.
  intros; eapply (@refine_forall_to_exists_independent
                    _ n (fun n => RDataTypeToRRecordType (n!sRDATA) = CNAME)
                    (fun n => RDataTypeToRRecordType (n!sRDATA) <> CNAME)
                    (fun tup' => n!sNAME = tup'!sNAME) R); eauto.
Qed.

(* very similar to refine_is_CNAME__forall_to_exists;
they start with the same set, but refine_forall_to_exists refines it with an extra end condition. changes the (forall x, ~P x) check into (exists x, P x) and returns !x, adding the condition in the forall *)
Lemma refine_forall_to_exists' :
  forall (n : resourceRecord) (R : @IndexedEnsemble resourceRecord),
    refine {b |
            decides b
                    (forall tup' : IndexedTuple,
                        R tup' ->
                        (indexedElement tup')!sNAME = n!sNAME
                        -> RDataTypeToRRecordType (indexedElement tup')!sRDATA <> CNAME)}
           (b <- {b |
                  decides b
                          (exists tup' : IndexedTuple,
                              R tup' /\
                              n!sNAME = (indexedElement tup')!sNAME
                              /\ RDataTypeToRRecordType (indexedElement tup')!sRDATA = CNAME)};
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

Instance Query_eq_DomainName :
  Query_eq DomainName.
unfold DomainName, Label;
  auto with typeclass_instances.
Qed.

Lemma UnConstrQuery_In_Where_Map {resultT}:
  forall (qs_schema : RawQueryStructureSchema) (idx : Fin.t (numRawQSschemaSchemas qs_schema))
         (r_o : UnConstrQueryStructure qs_schema) (P : Ensemble RawTuple)
         (f : _ -> resultT),
    refine (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (P r)
                                                                Return (f r)))
           (results <- UnConstrQuery_In r_o idx (fun r : RawTuple => Where (P r)
                                                                           Return r);
              ret (map f results)).
Proof.
  Local Transparent QueryResultComp.
  intros; unfold UnConstrQuery_In, QueryResultComp.
  rewrite refineEquiv_bind_bind; f_equiv; intro.
  induction a; simpl; autorewrite with monad laws.
  - reflexivity.
  - setoid_rewrite IHa.
    autorewrite with monad laws.
    unfold Query_Where, Query_Return; f_equiv.
    intros ? ?.
    apply Bind_inv in H; destruct_ex; intuition.
    refine pick val (map f x).
    computes_to_inv; subst.
    rewrite map_app; computes_to_econstructor; intuition eauto.
    computes_to_inv; intuition eauto;
    computes_to_inv; subst; eauto.
Qed.

Lemma Map_UnConstrQuery_In_Where {resultT}:
  forall (qs_schema : RawQueryStructureSchema) (idx : Fin.t (numRawQSschemaSchemas qs_schema))
         (r_o : UnConstrQueryStructure qs_schema) (P : Ensemble RawTuple)
         (f : _ -> resultT) (P_dec : DecideableEnsemble P),
    refine (results <- UnConstrQuery_In r_o idx (fun r : RawTuple => Where (P r)
                                                                           Return r);
              ret (map f results))
           (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (P r)
                                                                Return (f r))).
Proof.
  intros; unfold UnConstrQuery_In, QueryResultComp.
  rewrite refineEquiv_bind_bind; f_equiv; intro.
  induction a; simpl; autorewrite with monad laws.
  - reflexivity.
  - setoid_rewrite <- IHa.
    autorewrite with monad laws.
    unfold Query_Where, Query_Return; f_equiv.
    intros ? ?.
    apply Bind_inv in H; destruct_ex; intuition.
    refine pick val (if dec a then [a] else nil).
    + destruct (dec a) eqn: Heq_a.
      * rewrite dec_decides_P in Heq_a.
        computes_to_inv; subst.
        setoid_rewrite map_app; computes_to_econstructor; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_inv; subst; computes_to_econstructor.
      * computes_to_inv; subst.
        setoid_rewrite map_app; computes_to_econstructor; intuition eauto.
        rewrite Decides_false in Heq_a; apply H2 in Heq_a; subst.
        computes_to_econstructor; eauto.
    + destruct (dec a) eqn: Heq_a.
      * rewrite dec_decides_P in Heq_a; intuition.
      * rewrite Decides_false in Heq_a; intuition.
Qed.

Local Opaque QueryResultComp.

Lemma refine_under_bind_both_ambivalent {A A' B}
  : forall (c : Comp A)
           (c' : Comp A')
           (x : A -> Comp B)
           (y : A' -> Comp B),
    (forall (a' : A'),
        c' ↝ a' ->
        exists a,
          c ↝ a /\
          refine (x a) (y a'))
    -> refine (a <- c;
                 x a)
              (a <- c';
                 y a).
Proof.
  unfold refine; intros; computes_to_inv.
  apply H in H0; destruct_ex; intuition.
  computes_to_econstructor; eauto.
Qed.

Corollary refine_Count_map :
  forall (qs_schema : RawQueryStructureSchema) (idx : Fin.t (numRawQSschemaSchemas qs_schema))
         (r_o : UnConstrQueryStructure qs_schema)
         (P : Ensemble RawTuple)
         (P_dec : DecideableEnsemble P),
    refine (Count For (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (P r)
                                                                           Return r)))
           (Count For (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (P r)
                                                                           Return ()))).
Proof.
  Local Transparent Count.
  Local Transparent Query_For.
  unfold Count, Query_For; intros.
  rewrite !refineEquiv_bind_bind.
  eapply refine_under_bind_both_ambivalent; intros.
  apply Map_UnConstrQuery_In_Where in H.
  simpl in H; computes_to_inv; subst.
  eexists; split; eauto.
  eapply refine_under_bind_both_ambivalent; intros.
  simpl in H; computes_to_inv; subst.
  symmetry in H0.
  eexists v; split; eauto.
  apply Permutation_length in H0.
  rewrite H0.
  rewrite map_length; reflexivity.
  assumption.
  Local Opaque Count.
  Local Opaque Query_For.
Qed.

Lemma refine_count_constraint_broken :
  forall (n : resourceRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedRawTuple (GetHeading DnsSchema sRRecords),
                        (r!sRRecords)%QueryImpl tup' ->
                        n!sNAME = (indexedElement tup')!sNAME -> RDataTypeToRRecordType (n!sRDATA) <> CNAME)}
           (If (beq_RRecordType (RDataTypeToRRecordType (n!sRDATA)) CNAME)
               Then count <- Count
               For (tup in r!sRRecords)
               (Where (n!sNAME = tup!sNAME)
                      Return () )%QueryImpl;
              ret (beq_nat count 0) Else ret true).
Proof.
  (* intros; setoid_rewrite refine_pick_decides at 1. *)
  (* - Check refine_is_CNAME__forall_to_exists. apply refine_is_CNAME__forall_to_exists. *)
  (* [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ]. *)

  intros; setoid_rewrite refine_pick_decides at 1;
    [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
  (* refine existence check into query. *)

  match goal with
    |- context[{b | decides b
                            (exists tup : @IndexedTuple ?heading,
                                (@GetUnConstrRelationBnd ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
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
                             [ simpl; auto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                             | setoid_rewrite (@refine_constraint_check_into_query' qs_schema (ibound (indexb tbl)) qs P P' H2 H1); clear H2 H1 ] ]) end.
  remember ((n!sRDATA)); refine pick val (beq_RRecordType (RDataTypeToRRecordType d) CNAME); subst;
    [ | case_eq (beq_RRecordType (RDataTypeToRRecordType (n!sRDATA)) CNAME); intros;
        rewrite <- beq_RRecordType_dec in H; find_if_inside;
        unfold not; simpl in *; try congruence ].
  intros; simplify with monad laws; simpl.
  autorewrite with monad laws.
  setoid_rewrite negb_involutive.
  apply refine_If_Then_Else; try reflexivity.
  intros.
  rewrite (@refine_Count_map DnsSchema Fin.F1).
  reflexivity.
  apply DecideableEnsemble_EqDec.
  eauto with typeclass_instances.
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
  Local Transparent Query_For QueryResultComp.
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
      * pose proof dec_a as dec_a'; rewrite dec_decides_P in dec_a.
        repeat computes_to_inv; repeat computes_to_econstructor.
        intuition eauto. eauto.
        apply eq_ret_compute; destruct (@dec _ P P_dec a) eqn: dec__a.
        rewrite dec_decides_P in dec__a; apply H in dec__a;
          computes_to_inv; subst; simpl; rewrite dec_a'; reflexivity.
        apply Decides_false in dec__a; apply H0 in dec__a; subst; reflexivity.
      * pose proof dec_a as dec_a'; apply Decides_false in dec_a.
        repeat computes_to_inv; repeat computes_to_econstructor.
        intuition eauto. eauto.
        apply eq_ret_compute; destruct (@dec _ P P_dec a) eqn: dec__a.
        rewrite dec_decides_P in dec__a; apply H in dec__a;
          computes_to_inv; subst; simpl; rewrite dec_a'; reflexivity.
        apply Decides_false in dec__a; apply H0 in dec__a; subst; reflexivity.
  - refine pick val _; auto; subst.
    apply List.ListMorphisms.filter_permutation_morphism; [ reflexivity | assumption ].
Qed.

Definition bCOLLECTIONS : Fin.t _ :=
  ibound (indexb (@Build_BoundedIndex string (numQSschemaSchemas DnsSchema)
                                      (QSschemaNames DnsSchema) sRRecords _)).

Lemma refine_count_constraint_broken' :
  forall (n : resourceRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sRRecords),
                        (GetUnConstrRelation r bCOLLECTIONS) tup' ->
                        (indexedElement tup')!sNAME = n!sNAME (* switched *)
                        -> RDataTypeToRRecordType (indexedElement tup')!sRDATA <> CNAME)} (* indexedElement tup', not n *)
           (* missing the If/Then statement *)
           (count <- Count
                  For (UnConstrQuery_In r bCOLLECTIONS
                                        (fun tup : Tuple =>
                                           Where (n!sNAME = tup!sNAME
                                                  /\ RDataTypeToRRecordType tup!sRDATA = CNAME ) (* extra /\ condition *)
                                                 Return () ));
              ret (beq_nat count 0)).
Proof.
  intros; setoid_rewrite refine_forall_to_exists'.
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
                             [ simpl (* Discharge DecideableEnsemble w/ intances. *)
                             | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  apply @DecideableEnsemble_And.  apply DecideableEnsemble_EqDec.
  auto with typeclass_instances.
  apply DecideableEnsemble_EqDec. apply Query_eq_RRecordType.
  simplify with monad laws.
  setoid_rewrite negb_involutive; f_equiv.
  apply refine_Count_map.
  apply DecideableEnsemble_And.
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

(* used in refine_check_one_longest_prefix_s and refine_check_one_longest_prefix_CNAME *)
Lemma all_longest_prefixes_same :
  forall (ns : list resourceRecord) (s : DomainName),
    (* the name (list string) of every record in the list is a prefix
           of the given name (list string) *)
    (* e.g. [com.google, com.google.us, com.google.us.scholar] with s = com.google.us.scholar *)
    (forall (n' : resourceRecord), List.In n' ns -> prefix (get_name n') s)

    (* for two records, if they both have the longest names in the list of records
           (AND as before, they are prefixes of s)
         then their names must be the same *)
    -> forall n n' : resourceRecord, List.In n (find_UpperBound name_length ns)
                                     -> List.In n' (find_UpperBound name_length ns)
                                     -> get_name n = get_name n'.
Proof.
  unfold find_UpperBound, name_length; intros ns s H0 n n' H H1.
  apply filter_In in H; destruct H; apply filter_In in H1; destruct H1.
  pose proof (H0 _ H); pose proof (H0 _ H1).
  apply NPeano.leb_le in H2; apply NPeano.leb_le in H3.
  pose proof (fold_right_max_is_max name_length ns n H) as H2'.
  pose proof (fold_right_max_is_max name_length ns n' H1) as H3'.
  unfold name_length in *.
  apply (le_antisym _ _ H2') in H2; apply (le_antisym _ _ H3') in H3.
  rewrite <- H2 in H3.
  repeat unfold is_true in *.
  rewrite prefix_correct in H4, H5.
  rewrite <- H3 in H4; rewrite H4 in H5.
  eauto.
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
  : forall (ns : list resourceRecord) (s : DomainName),
    (* the name (list string) of every record in the list is a prefix
           of the given name (list string) *)
    (forall n' : resourceRecord, List.In n' ns -> prefix (get_name n') s) ->

    (* there exists no record such that it is one of the longest prefixes of the name
           AND is not the name itself -- refines to a computation that just checks the first
           the name against the first longest prefix found. it's ok to just check the first
           due to all_longest_prefixes_same: all longest prefixes must be the same *)
    refine {b : bool |
            decides b
                    (~
                       (exists x : resourceRecord,
                           List.In x (find_UpperBound name_length ns) /\ s <> (get_name x)))}

           (ret match find_UpperBound name_length ns with
                | nil => true
                | n' :: _ => ?[s == (get_name n')]
                end).
Proof.
  computes_to_econstructor; simpl in H; intros; computes_to_inv.
  subst; unfold decides; pose proof (all_longest_prefixes_same ns _ H); clear H.
  remember (find_UpperBound name_length ns) as l.
  unfold If_Then_Else.
  find_if_inside_eqn.
  - unfold not; intros; repeat destruct H; apply H1; clear H1; destruct l;
      [ inversion H | subst; apply H0 with (n := r) in H ];
      [ find_if_inside; [ subst; auto | inversion Heqb ] | simpl; left; auto ].
  - unfold not; intros; apply H; clear H; destruct l; try inversion Heqb.
    exists r; split; [ simpl; left; auto | intros; rewrite <- H in Heqb ].
    find_if_inside; [ discriminate | unfold not in *; apply n; auto ].
Qed.

(* uses all_longest_prefixes_same; very similar to refine_check_one_longest_prefix_s but with an extra condition/Tuple type *)
Lemma refine_check_one_longest_prefix_CNAME
  : forall (ns : list resourceRecord) (n : RRecordType) (s : DomainName)
           (HH : forall (t t' : resourceRecord) (n n' : nat),
               n <> n'
               -> nth_error ns n  = Some t
               -> nth_error ns n' = Some t'
               -> get_name t      = get_name t'
               -> RDataTypeToRRecordType (t!sRDATA) <> CNAME),
    (* forall HH? *)

    (* as before, the name (list string) of every record in the list is a prefix
           of the given name (list string) *)
    (forall n' : resourceRecord, List.In n' ns -> prefix (get_name n') s) ->

    (* Tuple type instead of record?
        all "records" that contain the longest prefixes and are not CNAME, and n isn't CNAME  *)
    (* this should be generalized to {b | List in ... /\ P} => match (...) with (P first one) *)
    refine {b' : option Tuple |
            forall b : Tuple,
              b' = Some b <->
              List.In b (find_UpperBound name_length ns) /\
              RDataTypeToRRecordType (b!sRDATA) = CNAME /\ n <> CNAME}
           (* refines to just checking the condition (with booleans) on the first longest prefix
                using all_longest_prefixes_same *)
           (ret match (find_UpperBound name_length ns) with
                | nil => None
                | n' :: _ => if CNAME == (RDataTypeToRRecordType (n'!sRDATA))
                             then if n == CNAME
                                  then None
                                  else Some n'
                             else None
                end).
Proof.
  unfold refine, not; intros; pose proof (all_longest_prefixes_same ns _ H); clear H.
  remember (find_UpperBound name_length ns) as l.
  computes_to_inv; computes_to_econstructor; split; intros.
  - destruct l; [ subst; inversion H | ].
    repeat find_if_inside_eqn; subst; try inversion H; subst.
    repeat split; [ simpl; left | symmetry | ]; auto.
  - destruct H as [? [? ?] ]; destruct l; [ inversion H | subst ].
    inversion H; unfold not in *.
    + repeat find_if_inside; subst; auto; exfalso; auto.
    + assert (r = b).
      * pose proof (in_eq r l).
        pose proof H; rewrite Heql in H5; pose proof (in_list_preserve_filter _ ns b H5); clear H5.
        pose proof H4; rewrite Heql in H5; pose proof (in_list_preserve_filter _ ns r H5); clear H5.
        pose proof (in_list_exists ns b H6); pose proof (in_list_exists ns r H7); destruct_ex; pose proof (H1 r b H4 H).
        destruct (beq_nat x0 x) eqn: eq; [ rewrite beq_nat_true_iff in eq; subst; rewrite H8 in H5; inversion H5; auto | ].
        rewrite beq_nat_false_iff in eq; symmetry in H9.
        (* HH instantiated here *)
        pose proof (HH b r x0 x eq H5 H8 H9); exfalso; auto.
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

Theorem IsPrefix_string_dec :
  forall l1 l2 : list string, IsPrefix l1 l2 \/ ~ IsPrefix l1 l2.
Proof.
  intros.
  destruct (IsPrefix_dec l1 l2); eauto.
Qed.

Lemma refine_For_List': forall (ResultT : Type) (bod : Comp (list ResultT)),
    refine
      (result <- bod;
         {l : list ResultT | Permutation result l})
      (For bod).
Proof.
  Local Transparent Query_For.
  unfold Query_For; intros; reflexivity.
  Local Opaque Query_For.
Qed.

Lemma flatten_CompList_Return' {A : Type}
  : forall (l : list A),
    refine (ret l) (FlattenCompList.flatten_CompList (map Query_Return l)).
Proof.
  induction l; simpl; try reflexivity.
  unfold Query_Return at 1; rewrite refineEquiv_bind_unit.
  setoid_rewrite <- IHl; rewrite refineEquiv_bind_unit.
  simpl; reflexivity.
Qed.

(* Main lemma -- TODO generalize *)

Lemma tuples_in_relation_satisfy_constraint {qs_schema}:
  forall (r_n : QueryStructure qs_schema)
         Ridx P l (P_dec : DecideableEnsemble P),
    (* TODO *)
    For (Query_In r_n Ridx
                  (fun r => Where (P r) (* Where Predicate ... *)
                                  Return r )) ↝ l ->
    forall (t t' : _ ) (n0 n' : nat),
      n0 <> n' ->
      nth_error l n0 = Some t -> (* this isn't right? *)
      nth_error l n' = Some t' ->
      SatisfiesTupleConstraints Ridx t t'.
Proof.
  intros.
  apply refine_For_List' in H; computes_to_inv.
  assert (forall l',
             computes_to
               (let qs_schema := DnsSchema in
                let r' := r_n in
                Query_In r' Ridx
                         (fun r : RawTuple =>
                            Return r )) l'
             ->  List.incl l l').
  { intros.
    unfold Query_In, QueryResultComp, In in *; computes_to_inv.
    unfold incl; intros.
    apply flatten_CompList_Return' in H3'; computes_to_inv; subst.
    pose proof (Permutation_UnIndexedEnsembleListEquivalence' H H3).
    rewrite <- H5.
    eapply flatten_CompList_Subset in H'0; eauto.
    rewrite H'; assumption.
  }
  (* ------------------------------------------------------------------------------------ *)

  assert (Permutation l v) by (symmetry; apply H').

  (* prove that everything in a is in sRRecords *)
  assert (forall l',
             In (list RawTuple)
                (let qs_schema := DnsSchema in
                 let r' := r_n in
                 Query_In r' Ridx (fun r : RawTuple => Return r)) l' ->
             incl l l').
  {
    (* x \subset sRRecords, and Permutation a x *)
    intros allTuplesInRelation inRelation.

    unfold incl.
    intros aTuple inA.
    unfold incl in H4.

    eapply (H3 allTuplesInRelation inRelation aTuple); eauto.
  }

  (* use the proof that the constraints hold on everything in sC, therefore on a *)
  (* t and t' are in a, therefore the constraint must hold on them *)
  (* this is the top-level goal  *)

  assert (List.In t l).
  { apply exists_in_list. exists n0. auto. }
  assert (List.In t' l).
  { apply exists_in_list. exists n'. auto. }

  simpl in H5.
  eapply refine_Intersection_Where in H.
  unfold QueryResultComp in H; computes_to_inv.
  destruct H as [x' [Equiv [Equiv' Equiv''] ] ].
  rewrite <- Equiv in *.
  eapply flatmap_permutation in H'0; rewrite H'0 in H4.
  destruct (unindexed_OK_exists_index' _ H0 H1 H2 H4) as [m [m' [idx [idx' ?] ] ] ];
    intuition.

  pose proof (rawTupleconstr (ith2 (rawRels r_n) (Ridx ))) as
      constraint_in_relation_OK; simpl in *.
  unfold GetNRelSchema.
  destruct (tupleConstraints (Vector.map schemaRaw (QSschemaSchemas qs_schema))[@Ridx]); eauto;
    apply (constraint_in_relation_OK {| elementIndex := idx; indexedElement := t |}
                                     {| elementIndex := idx'; indexedElement := t' |});
    simpl; try eassumption.

  eapply map_nth_error with (f := elementIndex) in H.
  eapply map_nth_error with (f := elementIndex) in H10.
  {
    revert m m' H H10 H8 Equiv''; clear; unfold Tuple; simpl; induction (map elementIndex x').
    - destruct m; destruct m'; simpl; intros; try discriminate.
    - destruct m; destruct m'; simpl; intros; try discriminate.
      + intuition.
      + inversion Equiv''; subst.
        intro; subst; apply H2; injections; apply exists_in_list; eauto.
      + inversion Equiv''; subst.
        intro; subst; apply H2; injections; apply exists_in_list; eauto.
      + inversion Equiv''; eauto.
  }

  assert (List.In {| elementIndex := idx; indexedElement := t |} x').
  { eapply exists_in_list; eauto. }
  apply Equiv' in H9; destruct H9; apply H9.
  assert (List.In {| elementIndex := idx'; indexedElement := t' |} x').
  { eapply exists_in_list; eauto. }
  apply Equiv' in H9; destruct H9;  apply H9.
  eauto.
Qed.

Lemma tuples_in_relation_satisfy_constraint_specific :
  forall (a : list RawTuple)
         name
         (r_n : QueryStructure DnsSchema),
    For (r in r_n!sRRecords)
        (Where (prefix r!sNAME name) (* Where Predicate ... *)
               Return r ) ↝ a ->
    forall (t t' : resourceRecord) (n0 n' : nat),
      n0 <> n' ->
      nth_error a n0 = Some t -> (* this isn't right? *)
      nth_error a n' = Some t' ->
      get_name t = get_name t' ->
      RDataTypeToRRecordType t!sRDATA <> CNAME.
Proof.
  intros.
  eapply (@tuples_in_relation_satisfy_constraint DnsSchema) in H; try eassumption.
  simpl in *; intuition.
  apply DecideableEnsemble_bool.
Qed.

Lemma refine_beq_RRecordType_dec v :
  forall (rr : resourceRecord),
    refine {b | decides b (RDataTypeToRRecordType rr!sRDATA = v)}
           (ret (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) v)).
Proof.
  intros; rewrite <- beq_RRecordType_dec.
  intros; refine pick val _.
  finish honing.
  find_if_inside; simpl; eauto.
Qed.

Lemma refine_noDup_CNAME_check :
  forall (rr : resourceRecord)
         (R : @IndexedEnsemble resourceRecord),
    (forall tup tup' : IndexedElement,
        elementIndex tup <> elementIndex tup' ->
        R tup ->
        R tup' ->
        (indexedElement tup)!sNAME = (indexedElement tup')!sNAME
        -> RDataTypeToRRecordType (indexedElement tup)!sRDATA <> CNAME)
    -> refine {b |
               decides b
                       (forall tup',
                           R tup' ->
                           rr!sNAME = (indexedElement tup')!sNAME -> RDataTypeToRRecordType rr!sRDATA <> CNAME)}
              (If (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) CNAME)
                  Then count <- Count
                  For
                  (QueryResultComp R
                                   (fun tup => Where (rr!sNAME = tup!sNAME)
                                                     Return tup )%QueryImpl);
                 ret (beq_nat count 0) Else ret true).
Proof.
  intros.
  intros; setoid_rewrite refine_pick_decides at 1;
    [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
  setoid_rewrite refine_beq_RRecordType_dec; simplify with monad laws.
  apply refine_If_Then_Else; eauto.
  setoid_rewrite refine_constraint_check_into_QueryResultComp with (P := fun tup => rr!sNAME = tup!sNAME).
  rewrite refineEquiv_bind_bind.
  f_equiv.
  unfold pointwise_relation; intros; simplify with monad laws;
    rewrite <- negb_involutive_reverse; reflexivity.
  auto with typeclass_instances.
  intuition.
  reflexivity.
Qed.

Corollary refine_noDup_CNAME_check_dns :
  forall (rr : resourceRecord) r_o r_n,
    @DropQSConstraints_AbsR DnsSchema r_o r_n
    -> refine {b |
               decides b
                       (forall tup',
                           (GetUnConstrRelation r_n Fin.F1) tup' ->
                           rr!sNAME = (indexedElement tup')!sNAME -> (RDataTypeToRRecordType rr!sRDATA) <> CNAME)}
              (If (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) CNAME)
                  Then count <- Count
                  For
                  (UnConstrQuery_In r_n Fin.F1
                                    (fun tup => Where (rr!sNAME = tup!sNAME)
                                                      Return () )%QueryImpl);
                 ret (beq_nat count 0) Else ret true).
Proof.
  intros; rewrite refine_noDup_CNAME_check.
  setoid_rewrite (@refine_Count_map DnsSchema Fin.F1 r_n).
  reflexivity.
  auto with typeclass_instances.
  intros; eapply (DropQSConstraints_AbsR_SatisfiesTupleConstraints H Fin.F1); eauto.
Qed.

Lemma refine_decides_Equiv_Ensemble' {A}:
  forall (P P' : Ensemble A),
    ((forall idx : A, P idx) <-> (forall idx' : A, P' idx')) ->
    refine {b : bool | decides b (forall idx : A, P idx)} {b : bool | decides b (forall idx : A, P' idx)}.
Proof.
  intros; eapply refineEquiv_pick_pick.
  intro; destruct x; simpl; split; intros; intuition eauto.
Qed.

Lemma refine_no_usurp_authority_check :
  forall (rr : resourceRecord)
         (R : @IndexedEnsemble resourceRecord),
    (forall tup tup' : IndexedElement,
        elementIndex tup <> elementIndex tup' ->
        R tup ->
        R tup' ->
        (indexedElement tup)!sNAME = (indexedElement tup')!sNAME
        -> RDataTypeToRRecordType (indexedElement tup)!sRDATA = NS
        -> RDataTypeToRRecordType (indexedElement tup')!sRDATA <> NS
        -> prefix (indexedElement tup)!sNAME (indexedElement tup')!sNAME
        -> (indexedElement tup)!sNAME = (indexedElement tup')!sNAME)
    -> refine {b |
               decides b
                       (forall tup',
                           R tup'
                           -> RDataTypeToRRecordType rr!sRDATA = NS
                           -> RDataTypeToRRecordType (indexedElement tup')!sRDATA <> NS
                           -> prefix rr!sNAME (indexedElement tup')!sNAME
                           -> rr!sNAME = (indexedElement tup')!sNAME)}
              (If (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) NS)
                  Then count <- Count
                  For
                  (QueryResultComp R
                                   (fun tup => Where (rr!sNAME <> tup!sNAME
                                                      /\ RDataTypeToRRecordType tup!sRDATA <> NS
                                                      /\ prefix (rr!sNAME) (tup!sNAME))
                                                     Return tup )%QueryImpl);
                 ret (beq_nat count 0) Else ret true).
Proof.
  intros.
  let p := constr:(RDataTypeToRRecordType (rr!sRDATA : RDataType) = NS) in
  intros; setoid_rewrite refine_pick_decides with (P := p) at 1.
  setoid_rewrite refine_beq_RRecordType_dec; simplify with monad laws.
  finish honing.
  { intros.
    erewrite refine_decides_Equiv_Ensemble' with (P' := fun tup' => R tup' ->
                                                                    (_ (indexedElement tup') /\
                                                                     _ (indexedElement tup'))
                                                                    -> rr!sNAME = (indexedElement tup')!sNAME).
    Focus 2.
    split; intros.
    apply H1.
    eassumption.
    eassumption.
    pattern (indexedElement idx'). apply (proj1 H3).
    pattern (indexedElement idx'). apply (proj2 H3).
    eauto.
    pose proof (@refine_forall_to_exists _
                                         (fun idx => rr!sNAME = idx!sNAME)
                                         (fun tup =>
                                            (fun r : resourceRecord => RDataTypeToRRecordType r!sRDATA <> NS /\
                                                                       is_true (prefix rr!sNAME r!sNAME)) tup)
                                         R _);  simpl in *; erewrite H1.
    setoid_rewrite refine_constraint_check_into_QueryResultComp.
    simplify with monad laws.
    setoid_rewrite <- negb_involutive_reverse.
    finish honing.
    apply DecideableEnsemble_And.
    unfold Same_set, Included, In; intuition.
  }
  intros; refine pick val _.
  finish honing.
  simpl; intros; intuition.
Qed.

Corollary refine_no_usurp_authority_check_dns :
  forall (rr : resourceRecord) r_o r_n,
    @DropQSConstraints_AbsR DnsSchema r_o r_n
    -> refine {b |
               decides b
                       (forall tup',
                           (GetUnConstrRelation r_n Fin.F1) tup'
                           -> RDataTypeToRRecordType rr!sRDATA = NS
                           -> RDataTypeToRRecordType (indexedElement tup')!sRDATA <> NS
                           -> prefix rr!sNAME (indexedElement tup')!sNAME
                           -> rr!sNAME = (indexedElement tup')!sNAME)}
              (If (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) NS)
                  Then count <- Count
                  For (UnConstrQuery_In r_n Fin.F1
                                        (fun tup => Where (rr!sNAME <> tup!sNAME
                                                           /\ RDataTypeToRRecordType tup!sRDATA <> NS
                                                           /\ prefix (rr!sNAME) (tup!sNAME))
                                                          Return () )%QueryImpl);
                 ret (beq_nat count 0) Else ret true).
Proof.
  intros; rewrite refine_no_usurp_authority_check.
  setoid_rewrite (@refine_Count_map DnsSchema Fin.F1 r_n).
  reflexivity.
  apply DecideableEnsemble_And.
  intros; eapply (DropQSConstraints_AbsR_SatisfiesTupleConstraints H Fin.F1); eauto.
Qed.

Lemma refine_no_usurp_authority_check' :
  forall (rr : resourceRecord)
         (R : @IndexedEnsemble resourceRecord),
    (forall tup tup' : IndexedElement,
        elementIndex tup <> elementIndex tup' ->
        R tup ->
        R tup' ->
        (indexedElement tup)!sNAME = (indexedElement tup')!sNAME
        -> RDataTypeToRRecordType (indexedElement tup)!sRDATA = NS
        -> RDataTypeToRRecordType (indexedElement tup')!sRDATA <> NS
        -> prefix (indexedElement tup)!sNAME (indexedElement tup')!sNAME
        -> (indexedElement tup)!sNAME = (indexedElement tup')!sNAME)
    -> refine {b |
               decides b
                       (forall tup' : IndexedElement,
                           R tup' ->
                           RDataTypeToRRecordType (indexedElement tup')!sRDATA = NS ->
                           RDataTypeToRRecordType rr!sRDATA <> NS ->
                           prefix (indexedElement tup')!sNAME rr!sNAME -> (indexedElement tup')!sNAME = rr!sNAME)}
              (If (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) NS) Then
                  (ret true)
                  Else
                  (count <- Count
                         For
                         (QueryResultComp R
                                          (fun tup => Where (RDataTypeToRRecordType tup!sRDATA = NS
                                                             /\ prefix (tup!sNAME) (rr!sNAME)
                                                             /\ tup!sNAME <> rr!sNAME)
                                                            Return tup )%QueryImpl);
                     ret (beq_nat count 0))).
Proof.
  intros.
  let p := constr:(RDataTypeToRRecordType (rr!sRDATA : RDataType) = NS) in
  intros; setoid_rewrite refine_pick_decides with (P := p) at 1.
  setoid_rewrite refine_beq_RRecordType_dec; simplify with monad laws.
  finish honing.
  - intros; refine pick val _.
    finish honing.
    simpl; intros; intuition.
  - intros.
    erewrite refine_decides_Equiv_Ensemble' with (P' := fun tup' => R tup' ->
                                                                    (_ (indexedElement tup') /\
                                                                     _ (indexedElement tup'))
                                                                    -> (indexedElement tup')!sNAME = rr!sNAME).
    Focus 2.
    split; intros.
    apply H1.
    eassumption.
    pattern (indexedElement idx'). apply (proj1 H3).
    eassumption.
    pattern (indexedElement idx'). apply (proj2 H3).
    eauto.
    pose proof (@refine_forall_to_exists _
                                         (fun idx => idx!sNAME = rr!sNAME)
                                         (fun tup =>
                                            (fun r : resourceRecord =>
                                               RDataTypeToRRecordType r!sRDATA = NS
                                               /\ is_true (prefix r!sNAME rr!sNAME )) tup)
                                         R _);  simpl in *; erewrite H1.
    setoid_rewrite refine_constraint_check_into_QueryResultComp.
    simplify with monad laws.
    setoid_rewrite <- negb_involutive_reverse.
    finish honing.
    apply DecideableEnsemble_And.
    unfold Same_set, Included, In; intuition.
Qed.

Corollary refine_no_usurp_authority_check'_dns :
  forall (rr : resourceRecord) r_o r_n,
    @DropQSConstraints_AbsR DnsSchema r_o r_n
    ->
    refine {b |
            decides b
                    (forall tup' : IndexedElement,
                        (GetUnConstrRelation r_n Fin.F1) tup' ->
                        RDataTypeToRRecordType (indexedElement tup')!sRDATA = NS ->
                        RDataTypeToRRecordType rr!sRDATA <> NS ->
                        prefix (indexedElement tup')!sNAME rr!sNAME -> (indexedElement tup')!sNAME = rr!sNAME)}
           (If (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) NS) Then
               (ret true)
               Else
               (count <- Count
                      For
                      (UnConstrQuery_In r_n Fin.F1
                                        (fun tup => Where (RDataTypeToRRecordType tup!sRDATA = NS
                                                           /\ prefix (tup!sNAME) (rr!sNAME)
                                                           /\ tup!sNAME <> rr!sNAME)
                                                          Return () )%QueryImpl);
                  ret (beq_nat count 0))).
Proof.
  intros; rewrite refine_no_usurp_authority_check'.
  setoid_rewrite (@refine_Count_map DnsSchema Fin.F1 r_n).
  reflexivity.
  apply DecideableEnsemble_And.
  intros; eapply (DropQSConstraints_AbsR_SatisfiesTupleConstraints H Fin.F1); eauto.
Qed.

Lemma beq_RRecordType_trans
  : forall RType RType' RType'' ,
    beq_RRecordType RType RType' = true
    -> beq_RRecordType RType RType'' = beq_RRecordType RType'' RType'.
Proof.
  unfold beq_RRecordType; intros.
  rewrite fin_beq_dec in H; subst; apply beq_RRecordType_sym.
Qed.

Instance ADomainName_eq : Query_eq DomainName := Astring_eq.
Instance ARRecordType_eq : Query_eq RRecordType :=
  {| A_eq_dec := fin_eq_dec |}.

Lemma refine_MaxElements {A B}
      {eqB : Query_eq B }
  : forall (op : B -> B -> Prop)
           (op_refl : forall b, op b b)
           (op_trans : forall b b' b'', op b b' -> op b' b'' -> op b b'')
           (op_dec : forall b, DecideableEnsemble (fun b' => op b' b))
           (op_irrefl : forall b b', op b b' -> op b' b -> b = b')
           (bound : B)
           (As : @IndexedEnsemble A)
           (f : A -> B),
    refine (MaxElements (fun a a' => op (f a) (f a'))
                        (As' <- {As' : list A | UnIndexedEnsembleListEquivalence As As'};
                           FlattenCompList.flatten_CompList (map (fun a => Where (op (f a) bound)
                                                                                 Return a) As')))
           (As' <- (As' <- {As' : list A | UnIndexedEnsembleListEquivalence As As'};
                      FlattenCompList.flatten_CompList (map (fun a => Where ((f a) = bound)
                                                                            Return a) As'));
              If negb (is_empty As') Then ret As' Else
                 (MaxElements (fun a a' => op (f a) (f a'))
                              (As' <- {As' : list A | UnIndexedEnsembleListEquivalence As As'};
                                 FlattenCompList.flatten_CompList (map (fun a => Where (op (f a) bound /\ (f a) <> bound)
                                                                                       Return a) As')))).
Proof.
  unfold MaxElements; intros; simplify with monad laws.
  setoid_rewrite refineEquiv_bind_bind.
  unfold refine; intros.
  computes_to_inv.
  destruct (is_empty v1) eqn: v1_eq; simpl in *; computes_to_inv; subst.
  - computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    assert (forall a', List.In a' v3 -> f a' <> bound).
    { intros; eapply Permutation_in in H0;
        eauto using (Permutation_UnIndexedEnsembleListEquivalence' H'' H).
      clear H.
      generalize dependent v1; generalize dependent v0; clear;
        induction v0; simpl; intros; intuition;
          computes_to_inv; subst.
      + unfold Query_Where, Query_Return in H'; computes_to_inv; subst.
        intuition; computes_to_inv; subst.
        simpl in v1_eq; discriminate.
      + eapply H0; eauto.
        rewrite is_empty_app, andb_true_iff in v1_eq.
        intuition.
    }
    generalize v2 H'''0 H0; clear; induction v3; simpl; intros;
      computes_to_inv; subst; intuition eauto.
    computes_to_econstructor.
    eapply refine_Query_Where_Cond in H'''0; eauto.
    intuition eauto.
    computes_to_econstructor.
    eapply IHv3; eauto.
    eauto.
  - computes_to_econstructor; eauto.
    assert (exists v',
               computes_to
                 (FlattenCompList.flatten_CompList (map (fun a : A => Where (op (f a) bound)
                                                                            Return a ) v0)) v').
    {
      revert op_dec; clear; induction v0; simpl; intros; eauto.
      destruct IHv0; eauto.
      destruct (dec (DecideableEnsemble := op_dec bound) (f a)) eqn:?.
      rewrite dec_decides_P in Heqb.
      eexists; computes_to_econstructor.
      computes_to_econstructor; split; intros.
      computes_to_econstructor.
      intuition.
      computes_to_econstructor; eauto.
      eexists; computes_to_econstructor.
      computes_to_econstructor; split; intros.
      apply Decides_false in Heqb.
      intuition.
      reflexivity.
      computes_to_econstructor; eauto.
    }
    destruct_ex; computes_to_econstructor; eauto.
    eapply (@refine_FindUpperBound _ _ _ op_trans bound); eauto.
    intros.
    eapply flatten_CompList_Prop in H0; eauto.
    refine {| dec a := dec (f a) |}.
    intros; rewrite dec_decides_P; reflexivity.
    generalize dependent v; generalize dependent x; clear H.
    induction v0; simpl.
    + intros; computes_to_inv; subst; simpl in *; discriminate.
    + intros; computes_to_inv; subst; simpl; eauto.
      unfold Query_Where, Query_Return in H0, H'; computes_to_inv; subst.
      intuition; computes_to_inv; subst.
      destruct (A_eq_dec (f a) bound); subst.
      * specialize (H0 (eq_refl _)); computes_to_inv; subst.
        specialize (H (op_refl _)); computes_to_inv; subst.
        eexists; simpl; intuition eauto.
      * apply H2 in n; subst.
        simpl in v1_eq.
        destruct (IHv0 _ H0' _ H'' v1_eq); intuition.
        eexists; split; eauto.
        apply in_or_app; right; eauto.
    + generalize dependent v; generalize dependent x; clear H.
      induction v0; simpl.
      * intros; computes_to_inv; subst; simpl in *; discriminate.
      * intros; computes_to_inv; subst; simpl; eauto.
        unfold Query_Where, Query_Return in H0, H'; computes_to_inv; subst.
        intuition; computes_to_inv; subst.
        destruct (dec (DecideableEnsemble := op_dec bound) (f a)) eqn:?.
        rewrite dec_decides_P in Heqb; pose proof (H Heqb).
        computes_to_inv; subst; simpl.
        destruct (A_eq_dec (f a) bound); subst.
        pose proof (H0 (eq_refl _)); computes_to_inv; subst.
        destruct (is_empty v2) eqn: ?.
        apply (@BindComputes _ _ _ _ [ ]); eauto.
        { revert eqB op_dec op_irrefl Heqb0 H0' H''; clear; revert v4 v2; induction v0;
            simpl; intros; computes_to_inv; subst; simpl.
          computes_to_econstructor.
          unfold Query_Where, Query_Return in H0', H''; computes_to_inv; subst.
          intuition; computes_to_inv; subst.
          destruct (dec (DecideableEnsemble := op_dec (f a)) (f a0)) eqn: ?.
          - rewrite dec_decides_P in Heqb; pose proof (H Heqb).
            computes_to_inv; subst.
            simpl.
            destruct (A_eq_dec (f a0) (f a)).
            + apply H1 in e; computes_to_inv; subst.
              simpl in *; discriminate.
            + pose proof (H2 n); subst; simpl in *.
              computes_to_econstructor; eauto.
              apply (@BindComputes _ _ _ _ false); eauto.
              computes_to_econstructor; simpl.
              intuition.
          - apply Decides_false in Heqb.
            pose proof (H0 Heqb); subst; simpl.
            destruct (A_eq_dec (f a0) (f a)); subst.
            intuition; computes_to_inv; subst.
            simpl in Heqb0; discriminate.
            apply H2 in n; subst; eauto.
        }
        apply (@BindComputes _ _ _ _ true); eauto.
        destruct v2; simpl in *; try discriminate.
        computes_to_econstructor.
        computes_to_econstructor.
        eauto.
        apply (@BindComputes _ _ _ _ true); eauto.
        pose proof (H2 n); subst; simpl.
        simpl in v1_eq.
        computes_to_econstructor; eauto.
        apply (@BindComputes _ _ _ _ false); eauto.
        computes_to_econstructor; simpl.
        intro; eapply n; eauto.
        apply Decides_false in Heqb.
        pose proof (H1 Heqb); subst; simpl.
        destruct (A_eq_dec (f a) bound); subst.
        intuition.
        apply H2 in n; subst; eauto.
Qed.

Lemma Permutation_filtered_List {A}
  : forall l l' P,
    Permutation (A := A) l l' ->
    forall l'',
    computes_to (⟦x in l | P x ⟧) l'' ->
    exists l''',
      computes_to (⟦x in l' | P x ⟧) l'''
      /\ Permutation l'' l'''.
Proof.
  intros ? ? ? H; induction H; simpl; intros; computes_to_inv.
  - subst; eauto.
  - apply IHPermutation in H0; destruct_ex; intuition.
    eexists (if v0 then x :: x0 else x0); split.
    repeat computes_to_econstructor; eauto.
    destruct v0; computes_to_inv; subst; eauto.
    destruct v0; computes_to_inv; subst; eauto.
  - eexists (if v0 && v2 then _ :: _ :: _ else
               if v0 then _ :: _ else
                 if v2 then _ :: _ else _
            ); split.
    repeat setoid_rewrite refine_bind_bind.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    destruct v0; destruct v2; simpl;
      repeat computes_to_econstructor; simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    destruct v0; destruct v2; simpl in *;
      computes_to_inv; subst; eauto.
    constructor 3; subst.
    subst; eauto.
  - apply IHPermutation1 in H1; destruct_ex; intuition.
    apply IHPermutation2 in H2; destruct_ex; intuition.
    eexists; split; eauto.
    rewrite H3; assumption.
Qed.

Lemma UpperBound_Permutation {A}
  : forall op l l',
    Permutation l l'
    -> forall (a : A),
      UpperBound op l a
      -> UpperBound op l' a.
Proof.
  unfold UpperBound;
    intros ? ? ? H; induction H; simpl; intros; intuition.
Qed.

Lemma build_FilteredList_app {A}
  : forall l l' l'' P,
    (⟦element in l | P element ⟧) ↝ (l' ++ l'')
    -> exists k' k'' : list A ,
      l = k' ++ k'' /\
      (⟦element in k' | P element ⟧) ↝ l'
      /\ (⟦element in k'' | P element ⟧) ↝ l''.
Proof.
  induction l; simpl; intros; computes_to_inv; subst.
  - eexists nil, nil; simpl; intuition eauto.
    destruct l'; destruct l''; simpl in H; try discriminate; simpl; eauto.
    destruct l'; destruct l''; simpl in H; try discriminate; simpl; eauto.
  - destruct v0; simpl in *; computes_to_inv; subst.
    + destruct l'; simpl in *; subst.
      eexists nil, _; intuition eauto; simpl.
      computes_to_econstructor; eauto.
      computes_to_econstructor; eauto.
      refine pick val true; simpl; eauto.
      apply refine_bind_unit; eauto.
      injections.
      apply IHl in H; destruct_ex; subst; intuition;
        computes_to_inv; subst.
      eexists (a0 :: x), _; intuition eauto; simpl.
      computes_to_econstructor; eauto.
      refine pick val true; simpl; eauto.
      apply refine_bind_unit; eauto.
    + apply IHl in H; destruct_ex; subst; intuition;
        computes_to_inv; subst.
      eexists (a :: x), _; intuition eauto; simpl.
      computes_to_econstructor; eauto.
      refine pick val false; simpl; eauto.
      apply refine_bind_unit; eauto.
Qed.

Lemma app_build_FilteredList {A}
  : forall (l' l'' k' k'' : list A) P,
    (⟦element in l' | P element ⟧) ↝ k'
    -> (⟦element in l'' | P element ⟧) ↝ k''
    -> (⟦element in l' ++ l'' | P element ⟧) ↝ (k' ++ k'').
Proof.
  induction l'; simpl; intros; computes_to_inv; subst.
  - eauto.
  - computes_to_inv; subst;
        computes_to_econstructor; eauto.
    refine pick val v0; simpl; eauto.
    apply refine_bind_unit; eauto.
    destruct v0; simpl in *; computes_to_inv;
      subst; simpl; eauto.
Qed.

Lemma refine_MaxElements_For {A}
  : forall (op : A -> A -> Prop) ens,
    refine (MaxElements op For ens)
           (l <- MaxElements op ens; {l' | Permutation l l'}).
Proof.
  unfold MaxElements; intros.
  rewrite refine_For.
  autorewrite with monad laws.
  f_equiv; intro.
  etransitivity.
  apply refine_under_bind; intros.
  eapply refine_ListComprehension_Equiv.
  computes_to_inv; subst.
  split; intros.
  symmetry in H; eapply UpperBound_Permutation; eauto.
  simpl in H0; eapply UpperBound_Permutation; eauto.
  simpl.
  remember a.
  setoid_rewrite Heql at 1;
    rewrite Heql at 1; clear Heql.
  intros ? ?; computes_to_inv; subst.
  revert l v v0 H H'; induction a; simpl; intros;
    computes_to_inv; subst.
  - repeat computes_to_econstructor; eauto.
    apply Permutation_nil in H'; subst; simpl; eauto.
  - destruct v2; simpl in *; computes_to_inv; subst.
    + pose proof (PermutationFacts.PermutationConsSplit _ _ _ H'); destruct_ex; subst.
      eapply (IHa _ (x ++ x0)) in H.
      computes_to_inv.
      apply build_FilteredList_app in H'1; destruct_ex; intuition; subst.
      refine pick val (x1 ++ (a :: x2)).
      apply refine_bind_unit.
      apply app_build_FilteredList; eauto.
      simpl.
      computes_to_econstructor; eauto.
      refine pick val true.
      computes_to_econstructor; simpl; eauto.
      simpl; eauto.
      simpl; eauto.
      rewrite H, Permutation_middle; reflexivity.
      rewrite <- Permutation_middle in H'.
      eapply Permutation_cons_inv; eauto.
    + eapply IHa in H'; eauto.
      computes_to_inv.
      refine pick val (a :: v1); eauto.
      computes_to_econstructor.
      computes_to_econstructor.
      simpl; computes_to_econstructor; eauto.
      refine pick val false; simpl; eauto.
      repeat computes_to_econstructor.
Qed.

Lemma refine_MaxElements' A op
  : forall (ca ca' : Comp (list A)),
    refine ca ca'
    -> refine (MaxElements op ca) (MaxElements op ca').
Proof.
  simpl; intros.
  Local Transparent MaxElements.
  unfold MaxElements, refine; simpl in *; intros.
  rewrite H; assumption.
  Local Opaque MaxElements.
Qed.

Lemma prefix_refl
  : forall b : string, prefix b b.
Proof.
  induction b; simpl; eauto.
  rewrite Equality.ascii_dec_refl; eauto.
Qed.

Lemma prefix_trans
  : forall b b' b'' : string, prefix b b' -> prefix b' b'' -> prefix b b''.
Proof.
  induction b; simpl; auto.
  - destruct b''; simpl; eauto.
  - induction b'; simpl; intros; intuition eauto.
    unfold is_true in H; discriminate.
    find_if_inside; subst.
    destruct b''; simpl in *.
    + unfold is_true in *; discriminate.
    + find_if_inside; subst; eauto.
    + unfold is_true in *; discriminate.
Qed.

Lemma prefix_antisym
  : forall b b' : string, prefix b b' -> prefix b' b -> b = b'.
Proof.
  induction b; simpl; intros;
    destruct b'; try reflexivity;
      unfold is_true in *; try discriminate.
  find_if_inside; subst;
    unfold is_true in *; try discriminate.
  f_equal.
  simpl in H; rewrite Equality.ascii_dec_refl in H; eauto.
Qed.

Lemma MaxElementsUnConstrQuery_In {qs_schema}
  : forall idx f bound (r_o : UnConstrQueryStructure qs_schema),
    refine (MaxElements (fun r r' : RawTuple => prefix (f r) (f r'))
                        For (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (prefix (f r) bound)
                                                                                 Return r )))
           (results' <- For (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (f r = bound)
                                                                                 Return r ));
              If negb (is_empty results') Then ret results' Else
                 (MaxElements (fun r r' => prefix (f r) (f r'))
                              For (UnConstrQuery_In r_o idx (fun r : RawTuple => Where (prefix (f r) bound
                                                                                        /\ (f r) <> bound)
                                                                                       Return r )))
           ).
Proof.
  intros.
  pose proof (fun H H' H'' H''' =>
                @refine_MaxElements _ _ _ prefix H H' H'' H''' bound (GetUnConstrRelation r_o idx) f).
  Local Transparent MaxElements.
  Local Transparent Query_For.
  Local Transparent UnConstrQuery_In.
  Local Transparent QueryResultComp.
  rewrite refine_MaxElements_For.
  rewrite H.
  simplify with monad laws.
  unfold Query_For, UnConstrQuery_In, QueryResultComp.
  rewrite !refineEquiv_bind_bind.
  f_equiv; intro.
  f_equiv; intro.
  intros ? ?; computes_to_inv.
  destruct a0.
  - apply Permutation_nil in H0; subst; simpl in *.
    unfold MaxElements in *.
    computes_to_inv; subst.
    symmetry in H0''0.
    pose proof (Permutation_filtered_List _ H0''0 _  H0'');
      destruct_ex; intuition.
    repeat computes_to_econstructor.
    eassumption.
    eassumption.
    eapply refine_ListComprehension_Equiv; eauto.
    split; intros; eauto using UpperBound_Permutation.
    symmetry in H0''0; eauto using UpperBound_Permutation.
    rewrite H2; reflexivity.
  - destruct v0; simpl in *.
    + symmetry in H0; apply Permutation_nil in H0; discriminate.
    + computes_to_inv; subst; computes_to_econstructor; eauto.
  - apply prefix_refl .
  - apply prefix_trans.
  - intro; apply DecideableEnsemble_bool.
  - apply prefix_antisym.
Qed.

Lemma Permutation_flatten_CompList {A B}
  : forall (l l' : list A) (f : A -> Comp (list B)),
    Permutation l l'
    -> forall x,
      FlattenCompList.flatten_CompList (map f l) ↝ x
      -> exists x',
        FlattenCompList.flatten_CompList (map f l') ↝ x'
        /\ Permutation x x'.
Proof.
  intros ? ? ? H; induction H; simpl; intros; computes_to_inv; subst; eauto.
  - eapply IHPermutation in H0'; destruct_ex; intuition eauto.
    eexists; split.
    computes_to_econstructor; eauto.
    rewrite H3; reflexivity.
  - eexists; split.
    computes_to_econstructor; eauto.
    rewrite List.app_assoc.
    rewrite Permutation_app with (l := v ++ v1) (m := v2) (m' := v2).
    2: rewrite Permutation_app_comm; reflexivity.
    rewrite List.app_assoc; reflexivity.
    reflexivity.
  - apply IHPermutation1 in H1.
    destruct_ex; intuition eauto.
    apply IHPermutation2 in H2; eauto.
    destruct_ex; intuition eauto.
    eexists; split; eauto.
    rewrite H3; eauto.
Qed.

(*Lemma Permutation_flatten_CompList' {A B}
  : forall (f : A -> Comp (list B)) (l l' : list B),
    Permutation l l'
    -> forall x,
        FlattenCompList.flatten_CompList (map (Where  x) ↝ l
        -> exists x',
          Permutation x x'
          /\ FlattenCompList.flatten_CompList (map f x') ↝ l'.
Proof.

Lemma Permutation_flatten_CompList' {A B}
  : forall (f : A -> Comp (list B)) (l l' : list B),
    (forall a v, computes_to (f a) v -> exists b, v = [b] \/ v = [ ])
    -> Permutation l l'
    -> forall x,
        FlattenCompList.flatten_CompList (map f x) ↝ l
        -> exists x',
          Permutation x x'
          /\ FlattenCompList.flatten_CompList (map f x') ↝ l'.
Proof.
  intros ? ? ? ? H; induction H; simpl; intros.
  - destruct x; simpl in *; computes_to_inv.
    eexists; split; simpl; eauto.
    simpl; eauto.
    apply app_eq_nil in H''; intuition subst.
    exists (a :: x); simpl; intuition eauto.
  - destruct x0; simpl in *; computes_to_inv.
    + discriminate.
    + pose proof (H0 _ _ H1); destruct_ex; intuition; subst; simpl in *.
      injections.
      apply IHPermutation in H1';
        destruct_ex; intuition.
      eexists (a :: x1); rewrite H3; intuition eauto.
      simpl; computes_to_econstructor; eauto.
      subst.


    induction x; simpl; intros; computes_to_inv; subst.


Lemma Permutation_flatten_CompList' {A B}
  : forall x (f : A -> Comp (list B)) (l l' : list B),
    (forall a v, computes_to (f a) v -> exists b, v = [b] \/ v = [ ])
    -> Permutation l l'
      -> FlattenCompList.flatten_CompList (map f x) ↝ l
      -> exists x',
        Permutation x x'
        /\ FlattenCompList.flatten_CompList (map f x') ↝ l'.
Proof.


  induction x; simpl; intros; computes_to_inv; subst.
  - apply Permutation_nil in H0; subst;
      eexists nil; simpl; intuition eauto.
  - pose proof (H _ _ H1); destruct_ex; intuition; subst.
    Focus 2.
    simpl in *.
    eexists (a :: x); split; eauto.
    simpl; computes_to_econstructor; eauto.
    computes
    simpl; eauto.
    eapply IHx in H1'; eauto.
    destruct_ex; intuition eauto.
    pose proof (H _ _ H1); destruct_ex; intuition; subst.
    Focus 2.
    simpl in *.
    eexists (a :: x0); split; eauto.
    simpl; repeat computes_to_econstructor; eauto.
    simpl.
    + simpl in H0.
      pose proof (PermutationFacts.PermutationConsSplit _ _ _ H0);
        destruct_ex; intuition; subst; eauto.
      cut (Permutation v0 (x2 ++ x3)); clear H0.
      revert H H3 x1 H1 v0 x2 x3 H4; clear; intros ? ? ? ?; induction H3; intros;
        simpl in H4; computes_to_inv; subst.
      * eapply Permutation_nil in H0; subst.
        apply app_eq_nil in H0; intuition subst.
        eexists; split; cbv beta; simpl; eauto.
        simpl; eauto.
      * pose proof (H _ _ H4); destruct_ex; intuition; subst.
        simpl in H0.
        pose proof (PermutationFacts.PermutationConsSplit _ _ _ H0);
          destruct_ex; intuition; subst; eauto.
        rewrite H2 in H0.
        eapply (IHPermutation _ x4 x5) in H4'; destruct_ex; intuition.


        apply IHPermutation in H0; destruct_ex; intuition.


        apply
        exists
        rewrite perm_swap in H0.
        pose proof (PermutationFacts.PermutationConsSplit _ _ _ H0);
          destruct_ex; intuition; subst; eauto.


        eapply IHPermutation in H4'.


        induction H3 .
        assert (exists x' x'' v' v'',
                 x0 = x' ++ x''
                 /\ FlattenCompList.flatten_CompList (map f x') ↝ v'
                 /\ FlattenCompList.flatten_CompList (map f x'') ↝ v''
                 /\ v0 = v' ++ v'').
      { admit. }
      destruct_ex; intuition; subst.
      pose proof (PermutationFacts.PermutationConsSplit _ _ _ H0);
        destruct_ex; intuition; subst; eauto.
      exists (x2 ++ (a :: x3)); split.
      rewrite H3.
      apply Permutation_middle.
      rewrite map_app.
      apply FlattenCompList.flatten_CompList_app.

      exists (a :: x0).
      simpl; rewrite H3; intuition.
      repeat computes_to_econstructor; eauto.


Admitted. *)

Lemma refine_flatten_CompList_filter {A}
  : forall v l P Q
           (P_dec : DecideableEnsemble P)
           (Q_dec : DecideableEnsemble Q),
FlattenCompList.flatten_CompList (map (fun r : A => Where (Q r /\ P r)
                                                                 Return r ) v) ↝ l
-> exists l',
      FlattenCompList.flatten_CompList (map (fun r : A => Where (P r)
                                                                Return r ) v) ↝ l'
    /\ l = filter (dec (DecideableEnsemble := Q_dec)) l'.
Proof.
  induction v; simpl; intros; computes_to_inv; subst; eauto.
  unfold Query_Where, Query_Return in H; computes_to_inv; intuition eauto.
  unfold Query_Where at 1, Query_Return at 1.
  eapply IHv in H'; destruct_ex; intuition; subst.
  exists (if dec (DecideableEnsemble := P_dec) a then a :: x else x).
  split.
  - destruct (dec (DecideableEnsemble := P_dec) a) eqn: ?.
    + rewrite dec_decides_P in Heqb.
      repeat computes_to_econstructor; intuition eauto.
    + apply Decides_false in Heqb.
      repeat computes_to_econstructor; intuition eauto.
  - destruct (dec (DecideableEnsemble := P_dec) a) eqn: ?.
    + rewrite dec_decides_P in Heqb.
      simpl.
      destruct (dec (DecideableEnsemble := Q_dec) a) eqn: ?.
      * rewrite dec_decides_P in Heqb0.
        intuition eauto.
        computes_to_inv; subst; simpl; eauto.
      * apply Decides_false in Heqb0.
        intuition eauto.
        subst; simpl; eauto.
    + apply Decides_false in Heqb.
      destruct (dec (DecideableEnsemble := Q_dec) a) eqn: ?.
      * rewrite dec_decides_P in Heqb0.
        intuition eauto.
        computes_to_inv; subst; simpl; eauto.
      * apply Decides_false in Heqb0.
        intuition eauto.
        subst; simpl; eauto.
Qed.

Lemma flatten_Complist_app {A}
  : forall (l : list (Comp (list A))) l' l'',
    (forall a v, List.In a l -> computes_to a v -> (exists a', v = [a']) \/ v = nil)
    -> FlattenCompList.flatten_CompList l ↝ l' ++ l''
    -> exists l3 l4,
      FlattenCompList.flatten_CompList l3 ↝ l'
      /\ FlattenCompList.flatten_CompList l4 ↝ l''
      /\ l = l3 ++ l4.
Proof.
  induction l; simpl; intros; computes_to_inv; subst.
  - symmetry in H0; eapply app_eq_nil in H0; intuition; subst.
    eexists nil, nil; simpl; intuition eauto.
  - destruct (fun G => H _ _ G H0); destruct_ex; intuition; subst.
    + simpl in H0''; destruct l'; simpl in H0''; subst.
      eexists nil, (a :: l); simpl; intuition eauto.
      injections.
      apply IHl in H0'; destruct_ex; intuition eauto; subst.
      eexists (_ :: _), _; simpl; intuition eauto.
    + simpl in H0''; subst.
      apply IHl in H0'; destruct_ex; intuition eauto; subst.
      eexists (_ :: _), _; simpl; intuition eauto.
Qed.

Lemma refine_Split_Where {heading}
  : forall (R : Ensemble (@IndexedRawTuple heading)) P Q
           (P_dec : DecideableEnsemble P)
           (Q_dec : DecideableEnsemble Q),
    refine (QueryResultComp R (fun r : RawTuple => Where (P r) Return r ))
           (results <- QueryResultComp R (fun r : RawTuple => Where (Q r /\ P r) Return r );
              results' <- QueryResultComp R (fun r : RawTuple => Where (~Q r /\ P r) Return r );
              {results'' | Permutation (results ++ results') results''}).
Proof.
  unfold QueryResultComp; intros. autorewrite with monad laws.
  intros ? ?; computes_to_inv.
  eapply refine_flatten_CompList_filter in H'; eauto.
  eapply refine_flatten_CompList_filter in H'''; eauto.
  destruct_ex; intuition eauto; subst.
  apply Permutation_flatten_CompList with (l' := v2) in H2;
  destruct_ex; intuition.
  assert (exists v',
             Permutation v' v2
             /\ FlattenCompList.flatten_CompList (map (fun r : RawTuple => Where (P r)
                                                                                 Return r ) v') ↝ v).
  { generalize dependent x1.
    revert P_dec.
    generalize dependent x; clear.
    revert v x0.
    induction v2; simpl; intros; computes_to_inv; subst.
    - eexists nil; simpl.
      symmetry in H3; apply Permutation_nil in H3; subst; simpl in *.
      apply Permutation_nil in H''''; subst; split; eauto.
    - unfold Query_Where, Query_Return in H1, H2; computes_to_inv; intuition.
      destruct (dec (DecideableEnsemble := P_dec) a) eqn: ?.
      + rewrite dec_decides_P in Heqb.
        pose proof (H Heqb); pose proof (H1 Heqb); computes_to_inv; subst.
        symmetry in H3.
        pose proof (PermutationFacts.PermutationConsSplit _ _ _ H3);
          destruct_ex; intuition; subst; eauto.
        simpl in H''''.
        rewrite filter_app in H''''; simpl in H''''.
        destruct (dec (DecideableEnsemble := Q_dec) a) eqn: ?; simpl in H''''.
        * rewrite dec_decides_P in Heqb0; simpl in *.
          assert (exists v' v'', v = v' ++ a :: v'').
          { rewrite <- Permutation_middle in H''''.
            simpl in H''''.
            apply PermutationFacts.PermutationConsSplit in H''''.
            eauto.
          }
          destruct_ex; subst.
          eapply (IHv2 (x0 ++ x2)) in H2'.
          2: apply H1'.
          3: eassumption.
          destruct_ex; intuition eauto.
          eapply flatten_Complist_app in H6; destruct_ex.
          intuition.
          symmetry in H8; apply app_map_inv in H8; destruct_ex; intuition.
          subst.
          eexists (x6 ++ (a :: x7)); intuition.
          rewrite <- H2.
          rewrite <- Permutation_cons_app; reflexivity.
          rewrite map_app.
          eapply FlattenCompList.flatten_CompList_app; simpl; eauto.
          repeat computes_to_econstructor; eauto.
          revert P_dec; clear; induction x3; simpl; intros; intuition.
          unfold Query_Where, Query_Return in H1; subst; computes_to_inv;
            intuition.
          destruct (dec (DecideableEnsemble := P_dec) a) eqn: ?.
          rewrite dec_decides_P in Heqb; apply H1 in Heqb; computes_to_inv; subst; eauto.
          apply Decides_false in Heqb.
          pose proof (H2 Heqb); subst; eauto.
          eauto.
          apply Permutation_cons_inv with (a := a).
          rewrite Permutation_middle with (l1 := x0), <- H''''.
          rewrite <- Permutation_middle with (l1 := filter dec x); simpl.
          econstructor.
          rewrite <- filter_app.
          reflexivity.
          apply Permutation_cons_inv with (a := a); eauto.
          rewrite H3.
          apply Permutation_middle.
        * assert (exists v' v'', v = v' ++ a :: v'').
          { rewrite <- Permutation_middle in H''''.
            simpl in H''''.
            apply PermutationFacts.PermutationConsSplit in H''''.
            eauto.
          }
          destruct_ex; subst.
          eapply (IHv2 (x0 ++ x2)) in H2'.
          2: apply H1'.
          3: eassumption.
          destruct_ex; intuition eauto.
          eapply flatten_Complist_app in H6; destruct_ex.
          intuition.
          symmetry in H8; apply app_map_inv in H8; destruct_ex; intuition.
          subst.
          eexists (x6 ++ (a :: x7)); intuition.
          rewrite <- H2.
          rewrite <- Permutation_cons_app; reflexivity.
          rewrite map_app.
          eapply FlattenCompList.flatten_CompList_app; simpl; eauto.
          repeat computes_to_econstructor; eauto.
          revert P_dec; clear; induction x3; simpl; intros; intuition.
          unfold Query_Where, Query_Return in H1; subst; computes_to_inv;
            intuition.
          destruct (dec (DecideableEnsemble := P_dec) a) eqn: ?.
          rewrite dec_decides_P in Heqb; apply H1 in Heqb; computes_to_inv; eauto.
          apply Decides_false in Heqb; apply H2 in Heqb; eauto.
          eauto.
          apply Permutation_cons_inv with (a := a).
          rewrite Permutation_middle with (l1 := x0), <- H''''.
          rewrite <- Permutation_middle; simpl.
          econstructor.
          rewrite <- filter_app.
          reflexivity.
          apply Permutation_cons_inv with (a := a); eauto.
          rewrite H3.
          apply Permutation_middle.
      + apply Decides_false in Heqb.
        pose proof (H0 Heqb); pose proof (H4 Heqb); computes_to_inv; subst.
        simpl in *; eapply IHv2 in H2'.
        2: apply H1'.
        destruct_ex; intuition.
        exists (a :: x); split; eauto.
        simpl.
        repeat computes_to_econstructor; intuition.
        apply H6.
        simpl; computes_to_econstructor.
        eassumption.
        eassumption.
        eassumption.
  }
  destruct_ex; intuition.
  computes_to_econstructor; try eassumption.
  computes_to_econstructor.
  eapply Permutation_UnIndexedEnsembleListEquivalence; try symmetry; eauto.
  eapply Permutation_UnIndexedEnsembleListEquivalence'; eauto.
Qed.

Lemma refine_Process_Query
  : forall (r_o : QueryStructure DnsSchema)
           (r_n : UnConstrQueryStructure DnsSchema)
           bound,
    DropQSConstraints_AbsR r_o r_n
    -> refine (For (UnConstrQuery_In r_n Fin.F1
                                     (fun r : RawTuple => Where (GetAttributeRaw r Fin.F1 = bound)
                                                                Return r )))
              (results <- For (UnConstrQuery_In r_n Fin.F1
                                                (fun r : RawTuple => Where
                                                                       ((RDataTypeToRRecordType r!sRDATA) = CNAME
                                                                        /\ GetAttributeRaw r Fin.F1 = bound)
                                                                       Return r ));
                 (Ifopt (hd_error results) as record Then
                                                     (ret [record])
                                                     Else
                                                     For (UnConstrQuery_In r_n Fin.F1
                                                                           (fun r : RawTuple => Where
                                                                                                  ((RDataTypeToRRecordType r!sRDATA) <> CNAME
                                                                                                   /\ GetAttributeRaw r Fin.F1 = bound)
                                                                                                  Return r )))).
Proof.
  unfold refine; intros.
  computes_to_inv.
  destruct v0; simpl in *; eauto.
  - unfold Query_For in *.
    computes_to_inv.
    computes_to_econstructor.
    eapply refine_Split_Where with
    (R := (GetUnConstrRelation r_n Fin.F1))
      (P := fun r : resourceRecord => GetAttributeRaw r Fin.F1 = bound).
    auto with typeclass_instances.
    2: computes_to_econstructor; try apply H0.
    2: computes_to_econstructor; try apply H0'.
    auto with typeclass_instances.
    computes_to_econstructor; eauto.
    symmetry in H0'0; apply Permutation_nil in H0'0; subst.
    simpl; computes_to_econstructor; eauto.
  - computes_to_inv; subst.
    Local Transparent Query_For.
    Local Transparent QueryResultComp.
    unfold UnConstrQuery_In, Query_For, QueryResultComp in *; computes_to_inv.
    apply refineEquiv_bind_bind.
    pose proof (DropQSConstraints_AbsR_SatisfiesTupleConstraints H Fin.F1); eauto.
    (*pose (@SatisfiesTupleConstraints DnsSchema Fin.F1 ); simpl in P.
    computes_to_econstructor; eauto; clear H0.
    assert (v0 = nil) by admit; subst.
    apply PermutationFacts.permutation_singleton in H0'; subst.
    destruct (flatten_CompList_Prop _ _ _  H0'0 r); simpl; intuition.
    generalize r H0 H1; clear.
    induction v1; simpl in *; intros.
    + computes_to_inv; subst.
      apply Permutation_nil in H0'; subst.
      discriminate.
      (* apply app_eq_nil in H0'; intuition; subst.
      repeat computes_to_econstructor; eauto. *)
    + unfold Query_Where at 1, Query_Return at 1 in H0'0.
      computes_to_inv; subst.
      intuition.
      apply refineEquiv_bind_bind.
      match goal with
        |- context [GetAttributeRaw ?a ?idx] =>
        destruct (string_dec (GetAttributeRaw a idx) bound)
      end.
      * computes_to_econstructor.
        computes_to_econstructor.
        split; intros.
        computes_to_econstructor.
        congruence.
        unfold GetAttribute in *; simpl in *.
        destruct ((RDataTypeToRRecordType (GetAttributeRaw a (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) == CNAME).
        { apply H2 in e0; eauto.
          computes_to_inv; subst.
          apply refineEquiv_bind_bind.
          pose proof (PermutationFacts.PermutationConsSplit _ _ _ H0');
            destruct_ex; intuition; subst; eauto; subst.

          eapply (IHv1 x _ x0) in H0'0'; computes_to_inv.
          computes_to_econstructor.
          eassumption.
          apply refine_bind_unit.
          computes_to_econstructor.
          rewrite H0'0''.
          revert H0; clear.
          grever
          induction  *)
Admitted.
(*       rewrite refine_QueryResultComp_body_Where_False      . *)



(*       inversion H0'. *)
(*     computes_to_econstructor. *)
(*     computes_to_econstructor. *)
(*     computes_to_inv; subst; computes_to_econstructor; split; intros. *)
(*       discriminate. *)
(*       intuition. *)
(*     + match goal with *)
(*         H : context[fin_eq_dec ?X ?Y] |- _ => *)
(*         destruct (fin_eq_dec X Y); simpl in H *)
(*       end. *)
(*       * computes_to_inv; subst. *)
(*         destruct l; simpl in *. *)
(*         { computes_to_econstructor; split; intros. *)
(*           injections. *)
(*           split; eauto; left. *)
(*           destruct b as [? [? [? [? ?] ] ] ]; simpl in *. *)
(*           unfold Tuple_DecomposeRawQueryStructure_inj'; simpl. *)
(*           unfold icons2, ilist2_hd, ilist2_tl; simpl; repeat f_equal. *)
(*           unfold SumType.inj_SumType; simpl. *)
(*           unfold CNAME_Record2RRecord; simpl. *)
(*           unfold VariantResourceRecord2RRecord; simpl. *)
(*           unfold icons2; simpl. *)
(*           repeat f_equal. *)
(*           unfold Domain; simpl; reflexivity. *)
(*           unfold Domain; simpl; reflexivity. *)
(*           destruct prim_snd; destruct (@inil2 Type); reflexivity. *)
(*           f_equal. *)
(*           intuition. *)
(*           destruct b as [? [? [? [? ?] ] ] ]; simpl in *. *)
(*           unfold Tuple_DecomposeRawQueryStructure_inj' in *; simpl in *. *)
(*           unfold icons2, ilist2_hd, ilist2_tl in *; simpl in *; *)
(*             unfold SumType.inj_SumType in *; simpl in *. *)
(*           unfold CNAME_Record2RRecord in *; simpl in *. *)
(*           unfold VariantResourceRecord2RRecord in *; simpl in *. *)
(*           unfold icons2 in *; simpl in *. *)
(*           destruct v0 as [? [? [? [? ?] ] ] ]; simpl in *. *)
(*           injections; simpl. *)
(*           repeat f_equal. *)
(*           destruct prim_snd; destruct (@inil2 Type); reflexivity. *)
(*         } *)
(*         admit. *)
(*       * admit. *)
(* Admitted. *)

Lemma is_empty_app {A} : forall l1 l2 : list A,
    is_empty (l1 ++ l2) = is_empty l1 && is_empty l2.
Proof.
  induction l1; simpl; eauto.
Qed.

Lemma negb_is_empty_app {A} : forall l1 l2 : list A,
    negb (is_empty (l1 ++ l2)) = negb (is_empty l1) || negb (is_empty l2).
Proof.
  intros; rewrite is_empty_app.
  rewrite negb_andb; reflexivity.
Qed.

Lemma eq_If_orb {A}
  : forall i1 i2 (t e : A) ,
    If i1 || i2 Then t Else e =
    If i1 Then t Else
       (If i2 Then t Else e).
Proof.
  intros; destruct i1; simpl; eauto.
Qed.

Arguments SumType.inj_SumType : simpl never.

Lemma refine_Singleton_Set
  : forall (r_n : UnConstrQueryStructure DnsSchema) q bound a,
    For (UnConstrQuery_In r_n Fin.F1
                          (fun r : RawTuple =>
                             Where (RDataTypeToRRecordType r!sRDATA = CNAME /\ GetAttributeRaw r Fin.F1 = bound)
                                   Return r )) ↝ [a]
    -> refine
         (SingletonSet (fun b : CNAME_Record =>
                          List.In (A := resourceRecord) b [a]
                          /\ q <> QType_inj CNAME))
         (If q == (QType_inj CNAME) Then
                                    (ret None)
                                    Else
                                    (c_record <- {c_record : CNAME_Record | a =
                                                                            @Tuple_DecomposeRawQueryStructure_inj'
                                                                              _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) _
                                                                              (SumType.inj_SumType ResourceRecordTypeTypes)
                                                                              CNAME c_record  };
                                       ret (Some c_record))).
Proof.
  unfold refine; intros.
  destruct (q == CNAME); simpl in *; computes_to_inv; subst.
  - computes_to_econstructor; split; intros.
    discriminate.
    intuition.
  - unfold SingletonSet.
    computes_to_econstructor; split; intros.
    + pose proof (@For_UnConstrQuery_In_Where_Prop DnsSchema Fin.F1 r_n _ _ _ H);
        inversion H1; subst; eauto.
      injection H0; intro; subst.
      intuition.
      left.
      destruct b as [? [? [? [? ?] ] ] ]; simpl in *.
      unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
      unfold icons2, ilist2_hd, ilist2_tl; simpl; repeat f_equal.
      unfold SumType.inj_SumType; simpl.
      unfold CNAME_Record2RRecord; simpl.
      unfold VariantResourceRecord2RRecord; simpl.
      unfold icons2; simpl.
      destruct prim_snd; destruct (@inil2 Type); reflexivity.
    + f_equal.
      intuition.
      destruct b as [? [? [? [? ?] ] ] ]; simpl in *.
      unfold Tuple_DecomposeRawQueryStructure_inj' in *; simpl in *.
      unfold icons2, ilist2_hd, ilist2_tl in *; simpl in *;
        unfold SumType.inj_SumType in *; simpl in *.
      unfold CNAME_Record2RRecord in *; simpl in *.
      unfold VariantResourceRecord2RRecord in *; simpl in *.
      unfold icons2 in *; simpl in *.
      destruct v0 as [? [? [? [? ?] ] ] ]; simpl in *.
      injections; simpl.
      destruct prim_snd; destruct (@inil2 Type); reflexivity.
Qed.

Lemma refine_Singleton_Set''
  : forall (r_o : QueryStructure DnsSchema)
           (r_n : UnConstrQueryStructure DnsSchema) q bound l a,
    For (UnConstrQuery_In r_n Fin.F1
                          (fun r : RawTuple =>
                             Where (RDataTypeToRRecordType r!sRDATA = CNAME /\ GetAttributeRaw r Fin.F1 = bound)
                                   Return r )) ↝ l
    -> hd_error l = Some a
    -> refine
         (SingletonSet (fun b : CNAME_Record =>
                          List.In (A := resourceRecord) b [a]
                          /\ q <> QType_inj CNAME))
         (If q == (QType_inj CNAME) Then
                                    (ret None)
                                    Else
                                    (c_record <- {c_record : CNAME_Record | a =
                                                                            @Tuple_DecomposeRawQueryStructure_inj'
                                                                              _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) _
                                                                              (SumType.inj_SumType ResourceRecordTypeTypes)
                                                                              CNAME c_record  };
                                       ret (Some c_record))).
Proof.
  intros.
  destruct l as [ | ? [ | ?] ]; simpl in *; try discriminate.
  pose proof (@refine_Singleton_Set _ q _ _ H); eauto.
  - injection H0; intros; subst; simpl in H1; rewrite H1.
    reflexivity.
  - pose proof (@For_UnConstrQuery_In_Where_Prop DnsSchema Fin.F1 r_n _ _ _ H);
      inversion H1; subst; eauto.
Admitted.

Lemma refine_Singleton_Set'
  : forall (r_n : UnConstrQueryStructure DnsSchema) q bound l,
    For (UnConstrQuery_In r_n Fin.F1
                          (fun r : RawTuple =>
                             Where (RDataTypeToRRecordType r!sRDATA <> CNAME /\ GetAttributeRaw r Fin.F1 = bound)
                                   Return r )) ↝ l
    -> refine
         (SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                          List.In (A := resourceRecord) b l
                          /\ q <> QType_inj CNAME))
         (ret None).
Proof.
Admitted.
(*    MaxElements (fun r r' : resourceRecord => prefix (GetAttributeRaw r Fin.F1) (GetAttributeRaw r' Fin.F1))
                For (Query_In r_o Fin.F1 (fun r : RawTuple => Where (prefix (GetAttributeRaw r Fin.F1) bound)
                                                                    Return r )) ↝ l
    -> Forall (fun r : resourceRecord => r!sNAME = bound) l
    -> refine
         (SingletonSet (fun b : CNAME_Record =>      (* If the record is a CNAME, *)
                          List.In (A := resourceRecord) b l
                          /\ q <> QType_inj CNAME))
         (If q == (QType_inj CNAME) Then
                                    (ret None)
                                    Else
         (Ifopt (hd_error l ) as record Then
                                               (If (RDataTypeToRRecordType record!sRDATA) == CNAME Then
                                               c_record <- {c_record : CNAME_Record | record =
                                                                        @Tuple_DecomposeRawQueryStructure_inj'
                                                                          _ DnsSchema Fin.F1 (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) _
                                                                          (SumType.inj_SumType ResourceRecordTypeTypes)
                                                                          CNAME c_record  };
                   ret (Some c_record)
                       Else ret None)
                Else ret None)).
Proof.
  unfold refine, IfDec_Then_Else; intros.
  destruct (q == CNAME); simpl in *; computes_to_inv; subst.
  - computes_to_econstructor; split; intros.
    discriminate.
    intuition.
  - destruct l; simpl in *; unfold SingletonSet.
    + computes_to_inv; subst; computes_to_econstructor; split; intros.
      discriminate.
      intuition.
    + match goal with
        H : context[fin_eq_dec ?X ?Y] |- _ =>
        destruct (fin_eq_dec X Y); simpl in H
      end.
      * computes_to_inv; subst.
        destruct l; simpl in *.
        { computes_to_econstructor; split; intros.
          injections.
          split; eauto; left.
          destruct b as [? [? [? [? ?] ] ] ]; simpl in *.
          unfold Tuple_DecomposeRawQueryStructure_inj'; simpl.
          unfold icons2, ilist2_hd, ilist2_tl; simpl; repeat f_equal.
          unfold SumType.inj_SumType; simpl.
          unfold CNAME_Record2RRecord; simpl.
          unfold VariantResourceRecord2RRecord; simpl.
          unfold icons2; simpl.
          repeat f_equal.
          unfold Domain; simpl; reflexivity.
          unfold Domain; simpl; reflexivity.
          destruct prim_snd; destruct (@inil2 Type); reflexivity.
          f_equal.
          intuition.
          destruct b as [? [? [? [? ?] ] ] ]; simpl in *.
          unfold Tuple_DecomposeRawQueryStructure_inj' in *; simpl in *.
          unfold icons2, ilist2_hd, ilist2_tl in *; simpl in *;
            unfold SumType.inj_SumType in *; simpl in *.
          unfold CNAME_Record2RRecord in *; simpl in *.
          unfold VariantResourceRecord2RRecord in *; simpl in *.
          unfold icons2 in *; simpl in *.
          destruct v0 as [? [? [? [? ?] ] ] ]; simpl in *.
          injections; simpl.
          repeat f_equal.
          destruct prim_snd; destruct (@inil2 Type); reflexivity.
        }
        admit.
      * admit.
Admitted. *)

Lemma refine_If_Opt_Then_Else'
  : forall (A B : Type) (c : option A) (x y : A -> Comp B),
    (forall a, c = Some a -> refine (x a) (y a)) ->
    forall x0 y0 : Comp B,
      refine x0 y0 -> refine (Ifopt c as c' Then x c' Else x0) (Ifopt c as c' Then y c' Else y0).
Proof.
  intros; destruct c; simpl; eauto.
Qed.

Lemma refine_decides_QType_match
  : forall rType qType,
    ?[ QType_dec qType CNAME ] = true
    -> refine {b : bool | decides b (QType_match rType qType)}
              (ret (if (QType_dec rType CNAME) then true else false)).
Proof.
  intros ? ?; find_if_inside; intros; try discriminate.
  subst.
  refine pick val _; try reflexivity.
  find_if_inside; subst; simpl.
  econstructor 2; eauto.
  intro; inversion H0; subst.
  compute in H1; discriminate.
  congruence.
Qed.

Lemma refine_If_Then_Bind {A B}
  : forall b a (k : A -> Comp B) e,
    refine (If b Then a' <- a; k a' Else e)
           (a' <- a; If b Then k a' Else e).
Proof.
  destruct b; simpl; intros; try reflexivity.
  intros ? ?.
  computes_to_inv; eauto.
Qed.

Lemma refine_If_opt_hd_error_map {A B C}
  : forall (f : A -> B) l t t' (e e' : Comp C),
    (forall a , hd_error l = Some a -> refine (t (f a)) (t' a))
    -> refine e e'
    -> refine (Ifopt hd_error (map f l) as b' Then t b' Else e)
              (Ifopt hd_error l as b' Then t' b' Else e').
Proof.
  destruct l; simpl; intros; subst; simpl; eauto.
Qed.

Lemma MaxElements_UnConstrQuery_In_Where_Prop {qs_schema}
  : forall (idx : Fin.t (numRawQSschemaSchemas qs_schema))
           (r_o0 : UnConstrQueryStructure qs_schema) (P : Ensemble RawTuple)
           (l : list RawTuple) op,
    DecideableEnsemble P ->
    MaxElements op
                (For (UnConstrQuery_In r_o0 idx (fun r0 : RawTuple => Where (P r0)
                                                                            Return r0 ))) ↝ l -> Forall P l.
Proof.
Admitted.

Definition QType_proj : QType -> option RRecordType. Admitted.

Lemma refine_Process_Query_Exact_Match
  : forall (r_o : UnConstrQueryStructure DnsSchema)
           r_n e a1 qType a0 s,
    DecomposeRawQueryStructureSchema_AbsR (qs_schema := DnsSchema) Fin.F1
                                          (Fin.FS (Fin.FS (Fin.FS Fin.F1))) ResourceRecordTypeTypes
                                          (SumType.SumType_index ResourceRecordTypeTypes)
                                          (SumType.SumType_proj ResourceRecordTypeTypes)
                                          (SumType.inj_SumType ResourceRecordTypeTypes) r_o r_n
    -> refine
         (a3 <- For (UnConstrQuery_In r_o Fin.F1
                                      (fun r : RawTuple =>
                                         Where (RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) <> CNAME
                                                /\ GetAttributeRaw r Fin.F1 = a1)
                                               Return r ));
            a' <- ⟦element in a3
                  | QType_match (RDataTypeToRRecordType (GetAttributeRaw element (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
                                qType ⟧;
            If negb (is_empty a3) Then ret (add_answers a' (buildempty true s a0))
               Else e)
         (If (QType_dec qType (EnumType.BoundedIndex_inj_EnumType ``("STAR"))) Then
             (a3 <- For (UnConstrQuery_In r_o Fin.F1
                                          (fun r : RawTuple =>
                                             Where (RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) <> CNAME
                                                    /\ GetAttributeRaw r Fin.F1 = a1)
                                                   Return r ));
                If negb (is_empty a3) Then ret (add_answers a3 (buildempty true s a0))
                   Else e)
             Else
             (Ifopt QType_proj qType as rType Then
                                              (a3 <- For (UnConstrQuery_In r_o Fin.F1
                                                                           (fun r : RawTuple =>
                                                                              Where (RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) = rType /\ RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) <> CNAME /\
                                                                                     GetAttributeRaw r Fin.F1 = a1)
                                                                                    Return r ));
                                                 count <- Count (UnConstrQuery_In r_o Fin.F1
                                                                                  (fun r : RawTuple =>
                                                                                     Where (RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) <> rType
                                                                                            /\ RDataTypeToRRecordType (GetAttributeRaw r (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) <> CNAME
                                                                                            /\ GetAttributeRaw r Fin.F1 = a1)
                                                                                           Return () ));
                                                 If negb (is_empty a3) || (le_lt_dec count 0) Then ret (add_answers a3 (buildempty true s a0))
                                                    Else e)
                                              Else e)).
Admitted.

Lemma refine_If_Else_Bind {A B}
  : forall b a (k : A -> Comp B) t,
    refine (If b Then t Else (a' <- a; k a'))
           (a' <- a; If b Then t Else k a').
Proof.
  destruct b; simpl; intros; try reflexivity.
  intros ? ?.
  computes_to_inv; eauto.
Qed.

Arguments Iterate_Equiv_QueryResultComp_body : simpl never.

Lemma refine_For_Bind {A B} :
  forall (c : Comp (list A)) (f : A -> B),
    refine (For (l <- c; ret (map f l)))
           (l <- For c; ret (map f l)).
Proof.
  intros.
  Local Transparent Query_For.
  unfold Query_For; repeat rewrite refineEquiv_bind_bind.
  simplify with monad laws.
  f_equiv; intro.
  intros ? ?; computes_to_inv; subst; computes_to_econstructor.
  rewrite H; reflexivity.
  Local Opaque Query_For.
Qed.

Lemma refine_MaxElements_map {A B}
  : forall (f : A -> B) (c : Comp (list A)) (op : B -> B -> Prop),
    refine (MaxElements op (l <- c; ret (map f l)))
           (l <- MaxElements (fun a a' => op (f a) (f a')) c; ret (map f l)).
Proof.
  Local Transparent MaxElements.
  intros; unfold MaxElements; simplify with monad laws.
  rewrite refineEquiv_bind_bind; f_equiv; intro.
  cut (forall a'',
          refine {b : bool | decides b (UpperBound op (map f a) (f a''))}
                 {b : bool | decides b (UpperBound (fun a0 a' : A => op (f a0) (f a')) a a'')}).
  - generalize (UpperBound op (map f a)).
    generalize (UpperBound (fun a0 a' : A => op (f a0) (f a')) a); intros.
    induction a; simpl.
    + rewrite refineEquiv_bind_unit; reflexivity.
    + repeat setoid_rewrite refineEquiv_bind_bind.
      rewrite IHa; simplify with monad laws.
      f_equiv; intro.
      setoid_rewrite H.
      f_equiv; intro.
      find_if_inside; rewrite refineEquiv_bind_unit; reflexivity.
  - intros.
    apply refineEquiv_pick_pick; intros.
    apply decide_eq_iff_iff_morphism; eauto.
    unfold UpperBound; split; intros;
      induction a; simpl in *; intuition; subst; eauto.
    Local Opaque MaxElements.
Qed.

Lemma refine_filter_Tuple_Decompose_inj' :
  forall ns_results' : list NS_Record,
    refine {ns_results : list NS_Record |
            forall x : NS_Record,
              List.In x ns_results <->
              List.In x (A := resourceRecord)
                      (map
                         (Tuple_DecomposeRawQueryStructure_inj' (qs_schema := DnsSchema) Fin.F1
                                                                (Fin.FS (Fin.FS (Fin.FS Fin.F1))) ResourceRecordTypeTypes
                                                                (SumType.inj_SumType ResourceRecordTypeTypes) NS) ns_results')}
           (ret ns_results').
Proof.
  intros; refine pick val _; eauto.
  reflexivity.
  induction ns_results'; simpl; split; intros; intuition eauto.
  subst.
  - left; destruct x as [? [? [? [? [ ] ] ] ] ]; reflexivity.
  - right; apply IHns_results'; intuition eauto.
  - left.
    unfold NS_Record2RRecord, VariantResourceRecord2RRecord, Tuple_DecomposeRawQueryStructure_inj' in H0.
    destruct x as [? [? [? [? [ ] ] ] ] ];
      destruct a as [? [? [? [? [ ] ] ] ] ]; simpl in *.
    unfold GetAttribute, GetAttributeRaw in *; simpl in *.
    unfold icons2, ilist2_tl, ilist2_hd in H0; simpl in *.
    injection H0; intros; subst.
    reflexivity.
  - right; apply IHns_results'; intuition eauto.
Qed.

Opaque Query_For.
Opaque QueryResultComp.

Lemma refine_If_Then_Else_true {C}
  : forall i (t e : Comp C),
    i = true
    -> refine (If i Then t Else e) t.
Proof.
  intros; subst; simpl; reflexivity.
Qed.

Lemma refine_If_Then_Else_false {C}
  : forall i (t e : Comp C),
    i = false
    -> refine (If i Then t Else e) e.
Proof.
  intros; subst; simpl; reflexivity.
Qed.

Lemma refine_Process_Query_Imprecise_Match
  : forall (r_o : QueryStructure DnsSchema)
           (r_n : UnConstrQueryStructure DnsSchema)
           bound p BStringId2 BStringId7,
    DropQSConstraints_AbsR r_o r_n
    -> refine
         (a4 <- MaxElements (fun r r' : resourceRecord => prefix (GetAttributeRaw r Fin.F1) (GetAttributeRaw r' Fin.F1))
             For (UnConstrQuery_In r_n Fin.F1
                                   (fun r : RawTuple =>
                                      Where (prefix (GetAttributeRaw r Fin.F1) bound /\ GetAttributeRaw r Fin.F1 <> bound)
                                            Return r ));
            a' <- {ns_results : list NS_Record | forall x : NS_Record, List.In x ns_results <-> List.In (A := resourceRecord) x a4};
            If is_empty a4 Then ret (buildempty true BStringId2 p)
               Else (a5 <- foldComp
                        (fun (a6 : list RawTuple) (a7 : NS_Record) =>
                           a5 <- For
                              (UnConstrQuery_In r_n Fin.F1
                                                (fun rRec : RawTuple =>
                                                   Where
                                                     (GetAttributeRaw rRec Fin.F1 = GetAttributeRaw a7 (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
                                                     Return rRec ));
                             ret (a5 ++ a6))
                        nil a';
                       ret
                         (add_additionals a5
                                          (add_nses (map VariantResourceRecord2RRecord a') (buildempty true BStringId7 p)))))
         (a4 <- MaxElements (fun r r' : resourceRecord => prefix (GetAttributeRaw r Fin.F1) (GetAttributeRaw r' Fin.F1))
             For (UnConstrQuery_In r_n Fin.F1
                                   (fun r : RawTuple =>
                                      Where (RDataTypeToRRecordType r!sRDATA = NS /\ prefix (GetAttributeRaw r Fin.F1) bound)
                                            Return r ));
            a' <- {ns_results : list NS_Record | forall x : NS_Record, List.In x ns_results <-> List.In x (A := resourceRecord) a4};
            If is_empty a' Then ret (buildempty true BStringId2 p)
               Else (a5 <- foldComp
                    (fun (a6 : list RawTuple) (a7 : NS_Record) =>
                    a5 <- For
                    (UnConstrQuery_In r_n Fin.F1
                    (fun rRec : RawTuple =>
                    Where
                    (GetAttributeRaw rRec Fin.F1 = GetAttributeRaw a7 (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
                    Return rRec ));
                    ret (a5 ++ a6))
                    nil a';
                       ret
                         (add_additionals a5
                                          (add_nses (map VariantResourceRecord2RRecord a') (buildempty true BStringId7 p))))).
Admitted.

Lemma refine_decides_forall_and {A}
  : forall (P Q : A -> Prop)
           (P' Q' : @IndexedElement A -> Prop)
           (R : @IndexedEnsemble A),
    (forall a, P (indexedElement a) <-> P' a)
    -> (forall a, Q (indexedElement a) <-> Q' a)
    -> refine {b |
               decides b
                       (forall tup' : @IndexedElement A,
                           R tup'
                           -> Q' tup'
                              /\ P' tup')}
              (b' <- {b |
                      decides b
                              (forall tup' : @IndexedElement A,
                                  R tup'
                                  -> Q' tup')};
                 If b' Then
                    {b |
                     decides b
                             (forall tup' : @IndexedElement A,
                                 R tup'
                                 -> P' tup')}
                    Else (ret false)).
Proof.
  unfold refine; intros; computes_to_inv; subst.
  computes_to_econstructor.
  find_if_inside; simpl in *; computes_to_inv; subst; simpl.
  - destruct v; simpl in *; intros.
    + intuition eauto.
    + intro; eapply H1'; intros; eapply H2; eauto.
  - intro; apply H1; intros; eapply H2; eauto.
Qed.

Lemma RDataTypeToRRecordType_inj :
  forall tag attr,
    RDataTypeToRRecordType
      (SumType.inj_SumType ResourceRecordTypeTypes tag attr) = tag.
Proof.
  intros; apply SumType.index_SumType_inj_inverse.
Qed.

Lemma resourceRecord_DecomposeRawQueryStructure_inj_inverse :
  forall (tup : resourceRecord),
    Tuple_DecomposeRawQueryStructure_inj'
      (qs_schema := DnsSchema)
      Fin.F1
      (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
      ResourceRecordTypeTypes
      (SumType.inj_SumType ResourceRecordTypeTypes)
      (SumType.SumType_index ResourceRecordTypeTypes (GetAttributeRaw tup (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
      (Tuple_DecomposeRawQueryStructure_proj'
         (qs_schema := DnsSchema)
         Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
         ResourceRecordTypeTypes
         (SumType.SumType_index ResourceRecordTypeTypes)
         (SumType.SumType_proj ResourceRecordTypeTypes)
         tup) = tup.
Proof.
  destruct tup as [? [? [? [? [ ] ] ] ] ]; simpl.
  unfold Tuple_DecomposeRawQueryStructure_proj',
  Tuple_DecomposeRawQueryStructure_inj'; simpl.
  unfold GetAttributeRaw; simpl.
  unfold ilist2_hd, ilist2_tl; simpl.
  destruct prim_fst2 as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?] ] ] ] ] ] ] ] ]; simpl;
    try reflexivity.
Qed.

Ltac simplify_Query_Where :=
  match goal with
    |- context [UnConstrQuery_In ?r_n ?Ridx (fun tup =>  Query_Where (@?P tup) _)] =>
    rewrite (fun ResultT =>
               @refine_UnConstrQuery_In_Query_Where_Cond _ r_n Ridx ResultT P);
    [ | intros; match goal with
                  |- context [RDataTypeToRRecordType (SumType.inj_SumType ?y ?z ?x) <> ?q] =>
                  case_eq (fin_eq_dec z q); simpl; intros ? ?; try discriminate;
                  first [let H' := fresh in
                         assert (RDataTypeToRRecordType (SumType.inj_SumType y z x) <> q <-> True) as H' by
                               (rewrite RDataTypeToRRecordType_inj; intuition eauto);
                         set_evars; rewrite ?H', ?and_True_l, ?and_True_r, ?and_False_r, ?and_False_l
                        | let H' := fresh in
                          assert (RDataTypeToRRecordType (SumType.inj_SumType y z x) <> q <-> False) as H' by
                                (rewrite RDataTypeToRRecordType_inj; eauto; intuition eauto);
                          set_evars; rewrite ?H', ?and_True_l, ?and_True_r, ?and_False_r, ?and_False_l];
                  finish honing
                end]
  end.
