 Require Import AutoDB.

(* Our bookstore has two relations (tables):
   - The [Books] relation contains the books in the
     inventory, represented as a tuple with
     [Author], [Title], and [ISBN] attributes.
     The [ISBN] attribute is a key for the relation,
     specified by the [where attributes .. depend on ..]
     constraint.
   - The [Orders] relation contains the orders that
     have been placed, represented as a tuple with the
     [ISBN] and [Date] attributes.

   The schema for the entire query structure specifies that
   the [ISBN] attribute of [Orders] is a foreign key into
   [Books], specified by the [attribute .. of .. references ..]
   constraint.
 *)

(* Let's define some synonyms for strings we'll need,
 * to save on type-checking time. *)
Definition sBOOKS := "Books".
Definition sAUTHOR := "Authors".
Definition sTITLE := "Title".
Definition sISBN := "ISBN".
Definition sORDERS := "Orders".
Definition sDATE := "Date".

(* Now here's the actual schema, in the usual sense. *)
Definition BookStoreSchema :=
  Query Structure Schema
    [ relation sBOOKS has
              schema <sAUTHOR :: string,
                      sTITLE :: string,
                      sISBN :: nat>
              where attributes [sTITLE; sAUTHOR] depend on [sISBN];
      relation sORDERS has
              schema <sISBN :: nat,
                      sDATE :: nat> ]
    enforcing [attribute sISBN for sORDERS references sBOOKS].

(* Aliases for the tuples contained in Books and Orders, respectively. *)
Definition Book := TupleDef BookStoreSchema sBOOKS.
Definition Order := TupleDef BookStoreSchema sORDERS.

(* Our bookstore has two mutators:
   - [PlaceOrder] : Place an order into the 'Orders' table
   - [AddBook] : Add a book to the inventory

   Our bookstore has two observers:
   - [GetTitles] : The titles of books written by a given author
   - [NumOrders] : The number of orders for a given author
 *)

(* So, first let's give the type signatures of the methods. *)
Definition BookStoreSig : ADTSig :=
  ADTsignature {
      "Init" : unit → rep,
      "PlaceOrder" : rep × Order → rep × bool,
      "DeleteOrder" : rep × nat → rep × list Order,
      "AddBook" : rep × Book → rep × bool,
      "GetTitles" : rep × string → rep × list string,
      "NumOrders" : rep × string → rep × nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    const "Init" (_ : unit) : rep := empty,

    update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS,

    update "DeleteOrder" ( oid : nat ) : list Order :=
        Delete o from sORDERS where o!sISBN = oid ,

    update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS ,

    query "GetTitles" ( author : string ) : list string :=
      For (b in sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE),

     query "NumOrders" ( author : string ) : nat :=
        Count (For (o in sORDERS) (b in sBOOKS)
               Where (author = b!sAUTHOR)
               Where (b!sISBN = o!sISBN)
               Return ())
}.

(* Aliases for internal names of the two tables *)
Definition Books := GetRelationKey BookStoreSchema sBOOKS.
Definition Orders := GetRelationKey BookStoreSchema sORDERS.

(* Aliases for internal notions of schemas for the two tables *)
Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

(* Now we define an index structure for each table. *)

Definition BookStorage : BagPlusProof (@Tuple BookSchema).
  mkIndex BookSchema [ BookSchema/sAUTHOR; BookSchema/sISBN ].
Defined.
(* In other words, index first on the author field, then the ISBN field.
 * Works especially efficiently for accesses keyed on author. *)

Definition OrderStorage : BagPlusProof (@Tuple OrderSchema).
  mkIndex OrderSchema [ OrderSchema/sISBN ].
Defined.

(* For convenience, we define aliases for the types of the
   index structures contained in our storage types. *)
Definition TBookStorage := BagTypePlus BookStorage.
Definition TOrderStorage := BagTypePlus OrderStorage.

(* This abstraction relation connects:
 * 1. Abstract database from reference implementation, using sets
 * 2. Our fancy realization, using search trees (from Bags library) *)

Definition BookStore_AbsR
           (or : UnConstrQueryStructure BookStoreSchema)
           (nr : TBookStorage * TOrderStorage) : Prop :=
  or!sBOOKS ≃ fst nr /\ or!sORDERS ≃ snd nr.

Opaque QSDelete.

Definition BookStoreManual :
  Sharpened BookStoreSpec.
Proof.
  unfold BookStoreSpec.

  (* First, we unfold various definitions and drop constraints *)
  start honing QueryStructure.

  (* Then we introduce the BookStore_AbsR abstraction relation *)
  hone representation using BookStore_AbsR.

  (* We start the actual refinement with the constructor, in a fully
  automated way *)
  hone constructor "Init". {
    initializer.
  }

  (* We then move on to the "GetTitles" method, which we decide to
     implement semi-manually *)

  hone method "GetTitles". {
    (* STEP 1: unfold the definition of the abstraction relation. *)
    startMethod BookStore_AbsR.

    (* STEP 2: use rewrites to phrase the query in terms of some
     * concrete list computation. *)
    (* First, instead of looping over the mathematical relation,
     * let's loop over an enumeration of the elements in the
     * concrete data structure. *)

    rewrite refine_List_Query_In by EquivalentBagIsEquivalentIndexedList.

    (* Next, we can implement the [Where] test as a list [filter]. *)
    rewrite refine_List_Query_In_Where; instantiate (1 := _).

    (* Now the expression is close enough to a list computation, so
     * we can replace the whole [for] with selection of some list that
     * is a permutation of the one we're building. *)
    rewrite refine_List_For_Query_In_Return_Permutation.

    (* A tactic from our library will do this sort of rewriting for us. *)
    Undo 3.
    concretize.

    (* STEP 3: more rewrites to find opportunities to use the index
     * structures efficiently *)
    (* We are filtering the results of enumerating all entries in a data structure.
     * There's a method available that combines the two operations. *)

    rewrite filter over BookStorage
            using search term (Some n, (@None nat, @nil (TSearchTermMatcher BookSchema))).

    (* Again, a generic tactic can handle this phase. *)
    Undo 1.
    asPerm BookStorage.

    (* STEP 4: Now we have settled on the final list expression.
     * Let's commit to using it instead of one of its other permutations. *)
    setoid_rewrite refine_Permutation_Reflexivity.
    simplify with monad laws.

    (* As usual, we have automation for this phase. *)
    Undo 2.
    commit.

    (* STEP 5: Pick the current database as the new one. *)
    rewrite refine_pick_val by eauto.
    simplify with monad laws.

    (* Automated version: *)
    Undo 2.
    choose_db BookStore_AbsR.

    (* And we're done! *)
    finish honing.
  }

  (* We then move on to implementing one of the mutators.
     Again, we adopt a slightly more manual style to demonstrate the
     main steps of the implementation. *)
  hone method "PlaceOrder". {
    (* First, we unfold the definition of our abstraction relation *)
    startMethod BookStore_AbsR.

    (* Then, we remove trivial or redundant checks *)
    pruneDuplicates.

    (* Since the specification represents datasets as mathematical
       sets, every inserted item is paired with a unique ID, which we
       need to pick. Further refinements will drop this index, which
       thus doesn't have any computational cost. *)

    pickIndex.

    (* To ease its implementation, we convert this foregin key check
       into a query *)
    foreignToQuery.

    (* This query, operating on sets, is then transformed into a
       filter on lists, making use of the equivalence relations
       specified by Bookstore_AbsR *)
    concretize.

    (* At this point, we need to pick a list of results whose elements
       are a permutation of the one derived from the query. Using
       permutation-preserving transformations, we substitute slow
       operations for more efficient ones *)
    asPerm (BookStorage, OrderStorage).

    (* This representation is reasonably satisfactory; we pick the
       resulting list, and proceed to a few extra optimizations *)
    commit.

    (* Now that we have a decision procedure for the constraint checks,
       all that remains is to proceed to the actual insertions. We
       distinguish the case where checks succeeded, and the case where
       checks failed. *)
    Split Constraint Checks.

    (* First, the case where checks succeed: the insertion is valid: *)
    checksSucceeded.

    (* Second, the case where checks failed: in that case, the DB
       remains untouched: *)
    checksFailed.
  }

  (* The remaining methods are similar, so we'll just throw the
   * automation at them. *)

  hone method "AddBook". {

    startMethod BookStore_AbsR.

    (* The, we remove trivial or redundant checks *)
    pruneDuplicates.

    (* Since the specification represents datasets as mathematical
       sets, every inserted item is paired with a unique ID, which we
       need to pick. Further refinements will drop this index, which
       thus doesn't have any computational cost. *)
    pickIndex.

    (* To ease its implementation, we convert this functional dependency
       check into a query *)
    fundepToQuery.

    (* This query, operating on sets, is then transformed into a
       filter on lists, making use of the equivalence relations
       specified by Bookstore_AbsR *)
    concretize.

    (* At this point, we need to pick a list of results whose elements
       are a permutation of the one derived from the query. Using
       permutation-preserving transformations, we substitute slow
       operations for more efficient ones *)
    asPerm (BookStorage, OrderStorage).

    (* This representation is reasonnably satisfactory; we pick the
       resulting list, and proceed to a few extra optimizations *)
    commit.

    (* Now that we have a decision procedure for the constraint checks,
       all that remains is to proceed to the actual insertions. We
       distinguish the case where checks succeeded, and the case where
       checks failed. *)
    Split Constraint Checks.

    (* First, the case where checks succeed: the insertion is valid: *)
    checksSucceeded.

    (* Second, the case where checks failed: in that case, the DB
       remains untouched: *)
    checksFailed.
  }

  hone method "NumOrders". {
    observer.
  }

  hone method "DeleteOrder". {
    startMethod BookStore_AbsR.

    Lemma EnsembleComplementIntersection {A}
    : forall (E P : Ensemble A),
        DecideableEnsemble P
        -> forall (a : A),
             (In _ (Intersection _ E
                                (Complement _ (EnsembleDelete E P))) a
             <-> In _ (Intersection _ E P) a).
    Proof.
      unfold EnsembleDelete, Complement, In in *; intuition;
      destruct H; constructor; eauto; unfold In in *.
      - case_eq (GeneralQueryRefinements.dec x); intros.
        + eapply dec_decides_P; eauto.
        + exfalso; apply H0; constructor; unfold In; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
      - intros H'; destruct H'; unfold In in *; eauto.
    Qed.

    Global Instance IndexedDecideableEnsemble
           {heading}
           {P : Ensemble (@Tuple heading)}
           {P_dec : DecideableEnsemble P}
    : DecideableEnsemble (fun x : IndexedTuple => P x) :=
      {| dec := @GeneralQueryRefinements.dec _ _ P_dec |}.
    Proof.
      intuition; eapply dec_decides_P; simpl in *; eauto.
    Defined.

    Lemma DeletedTuplesIntersection {qsSchema}
    : forall (qs : UnConstrQueryStructure qsSchema)
             (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
             (P : Ensemble Tuple),
        DecideableEnsemble P
        -> refine {x | QSDeletedTuples qs Ridx P x}
                  {x | UnIndexedEnsembleListEquivalence
                         (Intersection _ (GetUnConstrRelation qs Ridx) P) x}.
    Proof.
      intros qs Ridx P P_dec v Comp_v; inversion_by computes_to_inv.
      constructor.
      unfold QSDeletedTuples, UnIndexedEnsembleListEquivalence in *; destruct_ex;
        intuition; subst.
        eexists; intuition.
        unfold EnsembleListEquivalence in *; intuition; eauto with typeclass_instances.
        + eapply H0; eapply EnsembleComplementIntersection; eauto with typeclass_instances.
        + eapply EnsembleComplementIntersection; eauto with typeclass_instances.
          eapply H0; eauto.
    Qed.

    Lemma NoDupFilter {A}
    : forall (f : A -> bool) (l : list A),
        NoDup l -> NoDup (filter f l).
    Proof.
      induction l; simpl; intros; eauto.
      inversion H; subst; find_if_inside; try constructor; eauto.
      unfold not; intros H'; apply H2; revert H'; clear; induction l;
      simpl; eauto; find_if_inside; simpl; intuition.
    Qed.

    Local Transparent Query_For.

    Require Import AdditionalPermutationLemmas.

    Lemma DeletedTuplesFor {qsSchema}
    : forall (qs : UnConstrQueryStructure qsSchema)
             (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
             (P : Ensemble Tuple),
        DecideableEnsemble P
        -> refine {x | QSDeletedTuples qs Ridx P x}
                  (For (UnConstrQuery_In qs Ridx
                                        (fun tup => Where (P tup) Return tup))).
    Proof.
      intros qs Ridx P P_dec v Comp_v; rewrite DeletedTuplesIntersection by auto.
      constructor.
      unfold UnIndexedEnsembleListEquivalence.
      unfold Query_For in *; apply computes_to_inv in Comp_v; simpl in *;
      destruct Comp_v as [l [Comp_v Perm_l_v]].
      unfold UnConstrQuery_In, QueryResultComp in *; inversion_by computes_to_inv.
      remember (GetUnConstrRelation qs Ridx); clear Hequ.
      revert P_dec u v l Perm_l_v H1 H0; clear; induction x; simpl; intros.
      - inversion_by computes_to_inv; subst.
        exists (@nil (@IndexedTuple
                        (schemaHeading
                           (relSchema
                              (@nth_Bounded NamedSchema string relName
                                            (qschemaSchemas qsSchema) Ridx)))));
          simpl; split; eauto.
        rewrite Permutation_nil by eauto; reflexivity.
        + unfold EnsembleListEquivalence in *; intuition.
          destruct H0; eapply H1; eauto.
      - inversion_by computes_to_inv; subst.
        unfold UnConstrRelation in u.
        case_eq (@GeneralQueryRefinements.dec _ P P_dec a); intros.
        + apply computes_to_inv in H1; simpl in *; intuition.
          apply dec_decides_P in H; apply H3 in H.
          apply computes_to_inv in H; simpl in *; subst; simpl in *.
          pose proof (PermutationConsSplit _ _ _ Perm_l_v); destruct_ex; subst.
          destruct (H1 (fun x => u x /\ x <> a) (app x0 x2) x1); intuition eauto.
          * eapply Permutation_cons_inv; rewrite Permutation_middle; eassumption.
          * unfold EnsembleListEquivalence in *; intuition.
            inversion H; subst; eauto.
            unfold In in *; intuition.
            apply H5 in H6; destruct H6; subst; eauto; congruence.
            unfold In; intuition.
            apply H5; simpl; intuition.
            inversion H; subst; eauto.
          * symmetry in H5; pose proof (app_map_inv _ _ _ _ H5); destruct_ex;
            intuition; subst.
            exists (app x4 (a :: x5)); simpl; rewrite map_app; intuition.
            { unfold EnsembleListEquivalence in *; intuition.
              - apply NoDup_app_swap; simpl; constructor; eauto.
                inversion H; subst; unfold not; intros; apply H10.
                assert (List.In a (x4 ++ x5)) as In_a by
                    (apply in_or_app; apply in_app_or in H6; intuition).
                apply H8 in In_a; destruct In_a; unfold In in *; intuition.
                apply H7 in H13; simpl in H13; intuition.
                + apply NoDup_app_swap; eauto.
              - destruct H6; unfold In in *; apply H7 in H6; simpl in *; intuition.
                apply in_or_app; simpl; intuition.
                assert (u x0) as u_x0 by (apply H7; eauto).
                assert (List.In x0 (x4 ++ x5)) as In_x0
                by (apply H8; constructor; unfold In; intuition; subst;
                    inversion H; subst; eauto).
                apply in_or_app; simpl; apply in_app_or in In_x0; intuition.
              - unfold In.
                assert (List.In x0 (x4 ++ x5) \/ x0 = a)
                  as In_x0
                    by (apply in_app_or in H6; simpl in H6; intuition).
                intuition.
                apply H8 in H9; destruct H9; unfold In in *; intuition.
                constructor; eauto.
                subst; constructor; eauto.
                apply H7; simpl; eauto.
                case_eq (@GeneralQueryRefinements.dec _ P P_dec a); intros.
                apply dec_decides_P; eauto.
                assert (~ P a) as H''
                                  by (unfold not; intros H'; apply dec_decides_P in H'; congruence);
                    apply H4 in H''; discriminate.
            }
        + apply computes_to_inv in H1; simpl in *; intuition.
          assert (~ P a) as H''
                           by (unfold not; intros H'; apply dec_decides_P in H'; congruence);
            apply H4 in H''; subst.
          destruct (H1 (fun x => u x /\ x <> a) v x1); intuition eauto.
          * unfold EnsembleListEquivalence in *; intuition.
            inversion H5; subst; eauto.
            destruct H0; apply H6 in H0; simpl in H0; intuition.
            simpl in H6; constructor.
            apply H6; eauto.
            inversion H5; intros; subst; eauto.
          * eexists; split; eauto.
            unfold EnsembleListEquivalence in *; intuition.
            destruct H7; intuition.
            eapply H9; constructor; unfold In in *; subst; intuition.
            subst; apply_in_hyp dec_decides_P; congruence.
            constructor;
              apply H9 in H7; destruct H7; unfold In in *; intuition.
    Qed.

    Opaque Query_For.

    unfold QSDeletedTuples.
    pose proof (@DeletedTuplesFor _ or ``(sORDERS) (fun o : Tuple => o!sISBN = n)) as H';
    rewrite H' by eauto with typeclass_instances.
    concretize.
    asPerm (BookStorage, OrderStorage).
    commit.
    setoid_rewrite refineEquiv_pick_pair; simplify with monad laws.
    rewrite refine_pick_val by
        refine_bag_update_other_table.
    simplify with monad laws.

    Lemma bdelete_correct_DB
          db_schema qs index
          (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
    :  forall (store: BagTypePlus bag_plus),
         GetUnConstrRelation qs index ≃ store
         -> forall (DeletedTuples : Ensemble (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
                   (DT_Dec : DecideableEnsemble DeletedTuples),
              EnsembleIndexedListEquivalence
                (GetUnConstrRelation
                   (@UpdateUnConstrRelation db_schema qs index
                                            (EnsembleDelete (GetUnConstrRelation qs index)
                                                            DeletedTuples)) index)
                (snd (List.partition (@GeneralQueryRefinements.dec _ _ DT_Dec)
                                     (benumerate store))).
    Proof.
      simpl; unfold EnsembleDelete, EnsembleBagEquivalence, In, Complement; simpl;
      unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence,
      EnsembleListEquivalence; intros; intuition; destruct_ex; intuition; subst.
      repeat setoid_rewrite get_update_unconstr_eq; simpl; intros.
      exists x0.
      unfold UnConstrFreshIdx in *; intros; apply H; destruct H3; eauto.
      exists (snd (partition (@GeneralQueryRefinements.dec IndexedTuple (fun t => DeletedTuples t) _ ) x)); intuition.
      - unfold BagPlusProofAsBag; rewrite <- H2.
        repeat rewrite partition_filter_neq.
        clear; induction x; simpl; eauto.
        find_if_inside; simpl; eauto; rewrite <- IHx; reflexivity.
      - revert H0; clear; induction x; simpl; eauto.
        intros; inversion H0; subst.
        case_eq (partition (fun x0 => @GeneralQueryRefinements.dec IndexedTuple (fun t => DeletedTuples t) _ x0) x); intros; simpl in *; rewrite H.
        rewrite H in IHx; apply IHx in H3;
        case_eq (@GeneralQueryRefinements.dec IndexedTuple (fun t => DeletedTuples t) _ a);
        intros; simpl in *; rewrite H1; simpl; eauto.
        constructor; eauto.
        unfold not; intros; apply H2; eapply In_partition with
        (f := fun x0 : IndexedTuple => @GeneralQueryRefinements.dec IndexedTuple (fun t => DeletedTuples t) _ x0).
        simpl in *; rewrite H; eauto.
      - rewrite get_update_unconstr_eq in H3.
        destruct H3; unfold In in *.
        apply H4 in H3; eapply In_partition in H3; intuition; try apply H6.
        apply In_partition_matched in H6; apply dec_decides_P in H6; exfalso; eauto.
      - rewrite get_update_unconstr_eq; constructor.
        eapply H4; eapply In_partition; eauto.
        unfold In; intros.
        apply In_partition_unmatched in H3.
        simpl in *; apply dec_decides_P in H5.
        unfold QSGetNRelSchemaHeading, GetNRelSchemaHeading, GetNRelSchema in *;
          rewrite H3 in H5; congruence.
    Qed.

    Lemma bdeletePlus_correct_DB
          db_schema qs index
          bag_plus
    :  forall (store: BagTypePlus bag_plus),
         EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs index) store
         -> forall (DeletedTuples : Ensemble (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
                   (DT_Dec : DecideableEnsemble DeletedTuples)
                   search_term,
              ExtensionalEq (@GeneralQueryRefinements.dec _ _ DT_Dec)
                            (bfind_matcher (Bag := BagPlus bag_plus) search_term)     
              -> EnsembleBagEquivalence
                bag_plus
                (GetUnConstrRelation
                   (@UpdateUnConstrRelation db_schema qs index
                                            (EnsembleDelete (GetUnConstrRelation qs index)
                                                            DeletedTuples)) index)
                (snd (bdelete store search_term)).
    Proof.
      intros; unfold ExtensionalEq, EnsembleBagEquivalence in *.
      unfold EnsembleBagEquivalence.
      repeat rewrite get_update_unconstr_eq; simpl; intros.
      split;
        [
        | eapply bdelete_RepInv; intuition ].
      simpl in *;
        unfold EnsembleListEquivalence, EnsembleIndexedListEquivalence,
        UnConstrFreshIdx, EnsembleDelete, Complement in *; intuition; destruct_ex; intuition; intros.
      exists x; intros; eapply H; destruct H1; unfold In in *; eauto.
      unfold UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.
      generalize (bdelete_correct store search_term H2); destruct_ex; intuition.
      rewrite partition_filter_neq in H1.
      unfold BagPlusProofAsBag in *; simpl in *; rewrite <- H4 in H1.
      clear H6 H H2 H4.
      remember (filter (fun a : Tuple => negb (bfind_matcher search_term a))
            (map indexedTuple x0)).
      revert H1 H0 x0 Heql H3 H7; clear; intro;
      induction (benumerate (snd (bdelete store search_term))); intros.
      - rewrite Permutation_nil in Heql; subst; eauto.
    Admitted.
(*      - destruct x0; simpl in *; try discriminate.
        eexists; intuition eauto.
        simpl; auto.
        destruct H; eapply H7; eauto.
        destruct H.
        find_if_inside; try discriminate.
      destruct_ex *)
    simpl.
    rewrite refine_pick_val.
    Focus 2.
    simpl.
    eapply (@bdeletePlus_correct_DB _ _ _ _ _ H2 (fun x => (x!sISBN)%Tuple = n) _ (Some n, [])).
    unfold ExtensionalEq; simpl.
    intros; rewrite andb_true_r.
    reflexivity.
    simplify with monad laws.

    (* Almost done!*)

    unfold cast, eq_rect, eq_rect_r, eq_rect, eq_sym.
    unfold NatTreeBag.KeyFilter, NatTreeBag.MoreFacts.BasicProperties.F.eq_dec.

    simpl.
    intros; destruct (eq_nat_dec (a!sISBN) n).
    simpl.

    simplify with monad laws.
        (eapply bdeletePlus_correct_DB).
    rewrite pick_val.



      split.
      Print TSearchTermMatcher.

snd (List.partition (@GeneralQueryRefinements.dec _ _ DT_Dec)
                                     (benumerate store))).
    Proof.
      simpl; intros; constructor.
      - eapply bdelete_correct_DB; eauto.
      - eapply binsert_RepInv; apply H.
    Qed.

    idtac.

        simpl in *.
pose proof (In_partition_unmatched _ _ H3); constructor.
        elimtype False; apply H5.
        t
        right



        find_if_inside;
        case_eq (partition (@GeneralQueryRefinements.dec IndexedTuple _ _) x). partition_filter_neq
        split.

      simpl.
      exists (snd
      destruct_ex.
      idtac.
      simpl in H0.
      setoid_rewrite NoDup_modulo_permutation.
      split; intros.

      rewrite

    Permutation (benumerate (snd (bdelete container search_term)))
                (snd (List.partition (bfind_matcher search_term)
                                     (benumerate container)))


    Lemma

      {b : TOrderStorage |
       EnsembleBagEquivalence OrderStorage
                              ((UpdateUnConstrRelation or ``(sORDERS)
                                                       (EnsembleDelete or!sORDERS
                     (fun x : IndexedTuple => (x!sISBN)%Tuple = n)))!sORDERS)%QueryImpl
              b}

    setoid_rewrite refineEquiv_pick_pair.


    setoid_rewrite refine_pick_val by
                     (refine_bag_insert_in_other_table).
                    || binsert_correct_DB);


    Lemma EnsembleIntersectionFor {A}
    : forall (E P : Ensemble A),
        DecideableEnsemble P
        -> forall (a : A),
             (In _ (Intersection _ E
                                (Complement _ (EnsembleDelete E P))) a
             <-> In _ (Intersection _ E P) a).
    Proof.
      unfold EnsembleDelete, Complement, In in *; intuition;
      destruct H; constructor; eauto; unfold In in *.
      - case_eq (GeneralQueryRefinements.dec x); intros.
        + eapply dec_decides_P; eauto.
        + exfalso; apply H0; constructor; unfold In; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
      - intros H'; destruct H'; unfold In in *; eauto.
    Qed.



    Show.

    rewrite DeletedTuplesIntersection; eauto with typeclass_instances.


Lemma binsert_correct_DB
      db_schema qs index
      (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
:  forall (store: BagTypePlus bag_plus),
     GetUnConstrRelation qs index ≃ store
     -> forall DeletedTuples,
      UnIndexedEnsembleListEquivalence
        (GetUnConstrRelation
           (@UpdateUnConstrRelation db_schema qs index
                                   (EnsembleDelete index DeletedTuples)) index)
        (benumerate (bdelete (Bag := BagPlus bag_plus) store tuple)).
Proof.
  intros * store_eqv; destruct store_eqv as (store_eqv, store_WF).
  unfold EnsembleIndexedTreeEquivalence_AbsR,
  EnsembleBagEquivalence, UnIndexedEnsembleListEquivalence,
  UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.

  setoid_rewrite get_update_unconstr_eq.
  setoid_rewrite in_ensemble_insert_iff.
  setoid_rewrite NoDup_modulo_permutation.
  split; intros.

  erewrite binsert_enumerate_length by eauto with typeclass_instances.
    intuition; subst;
    [ | apply lt_S];
    intuition.

  destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto.

  destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto.

  destruct (permutation_map_cons indexedTuple (binsert_enumerate tuple store store_WF)
                                 {| tupleIndex := Datatypes.length (benumerate store);
                                    indexedTuple := tuple |} l' eq_refl map)
    as [ l'0 (map' & perm) ].

  exists l'0.
  split; [ assumption | split ].

  eexists; split; try apply perm.

  constructor;
    [ rewrite <- equiv; intro abs;
      apply indices in abs; simpl in abs;
      eapply lt_refl_False; eauto | assumption ].

  setoid_rewrite perm.
  setoid_rewrite equiv.
  setoid_rewrite eq_sym_iff at 1.
  reflexivity.
Qed.



  }



  unfold cast, eq_rect_r, eq_rect, eq_sym; simpl.

  (* At this point our implementation is fully computational: we're done! *)
  finish sharpening.
Defined.
