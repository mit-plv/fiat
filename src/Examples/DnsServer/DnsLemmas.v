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
                      Return tup )%QueryImpl;
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

(* uses refine_forall_to_exists; refines x2 in AddData
very similar to refine_count_constraint_broken; comments below are relative to refine_count_constraint_broken *)

(* implement the DNS record constraint check as code that counts the number of occurrences of
the constraint being broken (refines the boolean x1 in AddData) *)
(* TODO [autorewrite with monad laws] breaks in this file *)

(*
Lemma refine_count_constraint_broken :
  forall (n : resourceRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sRRecords),
                       (r!sRRecords)%QueryImpl tup' ->
                       n!sNAME = (indexedElement tup')!sNAME -> RDataTypeToRRecordType (n!sRDATA) <> CNAME)}
           (If (beq_RRecordType RDataTypeToRRecordType (n!sRDATA) CNAME)
               Then count <- Count
               For (UnConstrQuery_In r ``(sRRecords)
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
  remember RDataTypeToRRecordType (n!sRDATA); refine pick val (beq_RRecordType d CNAME); subst;
  [ | case_eq (beq_RRecordType RDataTypeToRRecordType (n!sRDATA) CNAME); intros;
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
                             [ simpl (* Discharge DecideableEnsemble w/ intances. *)
                             | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  apply @DecideableEnsemble_And.  apply DecideableEnsemble_EqDec.
  auto with typeclass_instances.
  apply DecideableEnsemble_EqDec. apply Query_eq_RRecordType.
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

(* Main lemma -- TODO generalize *)

(* should be generalized *)
Lemma tuples_in_relation_satisfy_constraint_specific :
  forall (a : list RawTuple)
         (n : packet)
         (r_n : QueryStructure DnsSchema),
    (* TODO *)
    For (r in r_n!sRRecords)
        (Where (prefix r!sNAME ((n!"question"!"qname" ))) (* Where Predicate ... *)
               Return r ) ↝ a ->
    forall (t t' : resourceRecord) (n0 n' : nat),
      n0 <> n' ->
      nth_error a n0 = Some t -> (* this isn't right? *)
      nth_error a n' = Some t' ->
      get_name t = get_name t' ->
      RDataTypeToRRecordType t!sRDATA <> CNAME.
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
     forall x2 (new) : indexedelement, it's in sRRecords if and only if it's in x1, the list of indexed elements  *)

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

        eapply in_flatten; eauto using string_dec.
        intros; setoid_rewrite prefix_correct;
          setoid_rewrite <- string_dec_bool_true_iff;
          find_if_inside; eauto.

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

  (* prove that everything in a is in sRRecords *)
  assert (forall l,
             In (list RawTuple)
                (let qs_schema := DnsSchema in
                 let r' := r_n in
                 Query_In r' bCOLLECTIONS (fun r : RawTuple => Return r)) l ->
             incl a l).
  {
    (* x \subset sRRecords, and Permutation a x *)
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
  simpl in H5.
  eapply refine_Intersection_Where in H5.
  unfold QueryResultComp in H5; computes_to_inv.
  destruct H5 as [x' [Equiv [Equiv' Equiv''] ] ].
  rewrite <- Equiv in *.
  eapply flatmap_permutation in H5'; rewrite H5' in H7.
  destruct (unindexed_OK_exists_index' _ H0 H1 H2 H7) as [m [m' [idx [idx' ?] ] ] ];
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
  apply DecideableEnsemble_bool.
Qed.

Lemma refine_beq_RRecordType_dec :
  forall rr : resourceRecord,
    refine {b | decides b (RDataTypeToRRecordType rr!sRDATA = CNAME)}
           (ret (beq_RRecordType (RDataTypeToRRecordType rr!sRDATA) CNAME)).
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
                                                  Return tup )%QueryImpl);
                  ret (beq_nat count 0) Else ret true).
Proof.
  intros; eapply refine_noDup_CNAME_check.
  intros; eapply (DropQSConstraints_AbsR_SatisfiesTupleConstraints H Fin.F1); eauto.
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

Lemma refine_under_bind_both_ambivalent {A B}
  : forall (c c' : Comp A)
           (x y : A -> Comp B),
    (forall (a' : A),
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

Local Transparent Query_For.

Lemma refine_MaxElements_For {A}
  : forall (op : A -> A -> Prop) ens,
    refine (MaxElements op For ens)
        (MaxElements op ens).
Proof.
  unfold MaxElements; intros.
  rewrite refine_For.
  simplify with monad laws.
  f_equiv; intro.
  refine pick val a; eauto.
  simplify with monad laws; reflexivity.
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
(* simplify with monad laws.
  Local Transparent Query_For.
  Local Transparent Query_In.
  Local Transparent QueryResultComp.
  unfold Query_For, Query_In, QueryResultComp.
  rewrite !refineEquiv_bind_bind.
  intros ? ?.
  computes_to_inv.
  computes_to_econstructor; eauto.
  computes_to_econstructor; eauto.
  assert (is_empty v0 = is_empty a0).
  { revert H; clear; generalize a0; induction v0; simpl; intros.
    symmetry in H; rewrite (Permutation_nil H); reflexivity.
    destruct a1; simpl; try reflexivity.
    pose proof (Permutation_nil H); discriminate.
  }
  rewrite <- H0.
  destruct (is_empty v0) eqn: ?; simpl in *.
  unfold MaxElements in *; computes_to_inv.
  apply refineEquiv_bind_bind.
  computes_to_econstructor; eauto.
  computes_to_econstructor; eauto.
  Focus 2.




  rewrite H.
  unfold MaxElements in *.
  unfold Query_For.
  simplify with monad laws.

  f_equiv; intro.
  setoid_rewrite H.

  Local Opaque QueryResultComp. *)
Admitted.

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
