Section BookStoreExamples.
  Require Import QueryStructureNotations.
  Require Import ListImplementation.
  Require Import ConstraintChecksRefinements.
  Require Import AdditionalLemmas AdditionalMorphisms.

  Unset Implicit Arguments.

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

  Definition sBOOKS := "Books".
  Definition sAUTHOR := "Authors".
  Definition sTITLE := "Title".
  Definition sISBN := "ISBN".
  Definition sORDERS := "Orders".
  Definition sDATE := "Date".

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
      enforcing [attribute sISBN of sORDERS references sBOOKS].

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

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "InitBookstore" : unit → rep,
        "PlaceOrder" : rep × Order → rep × unit,
        "AddBook" : rep × Book → rep × unit,
        "GetTitles" : rep × string → rep × list string,
        "NumOrders" : rep × string → rep × nat
      }.

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreSchema {
      const "InitBookstore" (_ : unit) : rep := empty,

      update "PlaceOrder" ( o : Order ) : unit :=
          Insert o into sORDERS,

      update "AddBook" ( b : Book ) : unit :=
          Insert b into sBOOKS ,

      query "GetTitles" ( author : string ) : list string :=
        For (b in sBOOKS)
        Where (author = b!sAUTHOR)
        Return (b!sTITLE),

       query "NumOrders" ( author : string ) : nat :=
          Count (For (o in sORDERS) (b in sBOOKS)
                 Where (author = b!sAUTHOR)
                 Where (b!sISBN = o!sISBN)
                 Return o!sISBN)
  }.

  Require Import BagsOfTuples Bool.

  (* (* TODO *)
  Eval compute in 
      (
        let relation_key := 
            (fun (x : BoundedIndex (map relName (qschemaSchemas BookStoreSchema))) => x)
              {| bindex := sBOOKS; indexb := _ |} in
        let attribute_key := 
            (fun (x :  Attributes (GetNRelSchemaHeading (qschemaSchemas BookStoreSchema) relation_key)) => x)
              {| bindex := sISBN; indexb := _ |} in
        attribute_key
      ).
   *)
  
  Notation "qs_schema / rel_index" := (GetRelationKey qs_schema rel_index) (at level 40, left associativity).
  Notation "rel_key // attr_index" := (GetAttributeKey rel_key attr_index) (at level 50).

  Definition Books := BookStoreSchema/sBOOKS. 
  Definition Orders := BookStoreSchema/sORDERS.
  Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
  Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

  Definition BookStorage : @BagPlusBagProof Book.
    mkIndex BookSchema [ Books//sAUTHOR; Books//sISBN ].
  Defined.

  Definition OrderStorage : @BagPlusBagProof Order.
    mkIndex OrderSchema [ Orders//sISBN ].
  Defined.

  Definition TBookStorage := BagType BookStorage.
  Definition TOrderStorage := BagType OrderStorage.

  Definition BookStoreListImpl_AbsR
             (or : UnConstrQueryStructure BookStoreSchema)
             (nr : TBookStorage * TOrderStorage) : Prop :=
    or ! sBOOKS ≃ benumerate (fst nr) /\ or ! sORDERS ≃ benumerate (snd nr).

  Opaque Query_For.
  Opaque benumerate bfind_matcher bfind benumerate. (* TODO *)

  (* TODO: How to do the instantiations automatically? *)

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    (* Step 1: Drop the constraints on the tables. From the perspective
      of a client of a sharpened ADT the invariants will still hold,
      since ADT refinement preserves the simulation relation. *)

    match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
        hone representation using (@DropQSConstraints_AbsR Rep)
    end.
    
    drop constraints from insert "PlaceOrder".
    drop constraints from insert "AddBook".
    drop constraints from query "GetTitles".
    drop constraints from query "NumOrders".

    (*TODO: start honing QueryStructure.*)

    hone representation using BookStoreListImpl_AbsR.

    hone constructor "InitBookstore". {
       unfold BookStoreListImpl_AbsR.

      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      repeat setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws.

      rewrite (refine_pick_val' (bempty, bempty)) by (intuition; apply bempty_correct_DB).
      subst_body; higher_order_1_reflexivity. 
    }

    Notation "?[ A ]" := (if A then true else false) (at level 50).

    hone method "NumOrders". {
      unfold BookStoreListImpl_AbsR in H0; split_and.
      simplify with monad laws.

      (* Step 1: Move to a concrete representation *)
      rewrite refine_List_Query_In by eassumption.
      rewrite refine_Join_List_Query_In by eassumption.
      rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.
      simpl.

      (* Step 2: Make it more efficient *)
      rewrite (filter_join_snd (fun (a: Book) => ?[string_dec n (a!sAUTHOR)])).
      
      rewrite filter over BookStorage using search term
                (Some n, (@None nat, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite swap_joins; trickle_swap; simpl.

      setoid_rewrite filter_join_lists; simpl.

      rewrite dependent filter 
                (fun (x: Book) (y : Order) => ?[eq_nat_dec x!sISBN y!sISBN]) 
              over OrderStorage using dependent search term 
                (fun (x: Book) => (Some x!sISBN, @nil (TSearchTermMatcher OrderSchema))).

      setoid_rewrite (bfind_correct _).

      setoid_rewrite map_flat_map.      
      setoid_rewrite map_map; simpl.
      
      setoid_rewrite refine_Permutation_Reflexivity.
      setoid_rewrite refine_Count.
      simplify with monad laws.

      (* Step 3: Pass the database, unmodified *)
      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.

      (* Step 4: A few final tweaks *)
      setoid_rewrite length_flat_map.
      setoid_rewrite map_length.

      (* Step 5: All done *)
      finish honing.
    }

    hone method "GetTitles". {
      unfold BookStoreListImpl_AbsR in H0; split_and.
      simplify with monad laws.

      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over BookStorage using search term
              (Some n, (@None nat, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite (bfind_correct _).

      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.
      simpl.

      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto. 
      simplify with monad laws.
      finish honing.
    }

    hone method "PlaceOrder". {
      Notation " A ! B " := (A ``(B)) (at level 2).
      setoid_rewrite refine_trivial_if_then_else.

      unfold BookStoreListImpl_AbsR in H0; split_and.
      simplify with monad laws.

      rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index.
      simplify with monad laws.

      Check refine_List_Query_In.
      
      Lemma in_indexed_in_list :
        forall {heading} table seq P,
          (@EnsembleIndexedListEquivalence heading table seq) ->
          ((exists itup, table itup /\ P (indexedTuple itup)) <-> 
           (exists tup,  List.In tup seq /\ P tup)).
      Proof.
        intros * ( indices & [ seq' ( map_correct & nodup & equiv ) ] ).
        split; subst; setoid_rewrite in_map_iff; intros [ tup' (_in & _P) ].

        - eexists; split; 
          [ eexists; split; [ reflexivity | apply equiv ] | ]; 
          eassumption. 
        - destruct _in as [ tup'' ( proj_eq & _in ) ];
          eexists; subst; split; [ apply equiv |  ];
          eassumption.
      Qed.        

      Show.
      Add Parametric Morphism :
        (decides)
          with signature (eq ==> iff ==> iff) 
            as decides_eq_iff_eq_morphism.
      Proof.
        intros b **; unfold decides; destruct b; intuition.
      Qed.

      Require Import List.

      
      Transparent Query_For Count.

      Print boxed_option.
      Require Import AdditionalPermutationLemmas.

      SearchAbout DecideableEnsemble.
      Opaque Query_For .
      Opaque Count.

      setoid_rewrite (refine_foreign_key_constraint_via_select (fun (b: Book) => n!sISBN = b!sISBN)); eauto.

      simplify with monad laws; simpl.
      
      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over BookStorage using search term
              (@None string, (Some n!sISBN, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Count.
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      setoid_rewrite map_length.
      unfold BookStoreListImpl_AbsR.
      
      Split Constraint Checks.

      Definition ID {A}  := fun (x: A) => x.

      Lemma ens_red :
        forall {heading TContainer TSearchTerm} x y (y_is_bag: Bag TContainer _ TSearchTerm),
          @EnsembleIndexedListEquivalence heading x (benumerate (Bag := y_is_bag) y) =
          (ID (fun y => EnsembleIndexedListEquivalence x (benumerate y))) y.
      Proof.
        intros; reflexivity.
      Qed.

      
      setoid_rewrite ens_red.
      setoid_rewrite refineEquiv_pick_pair.
      unfold ID; simpl.
      simplify with monad laws.

      rewrite (refine_pick_val' (fst r_n)) by ((*apply (fun id => @refine_list_insert_in_other_table _ c id _ (benumerate (Bag := BagProof BookStorage) (fst r_n)) H1);*) 
                                               intuition discriminate).
      simplify with monad laws.

      rewrite refine_pick_val by (apply (binsert_correct_DB (store_is_bag := BagProof OrderStorage) _ _ _ _ H2); eauto).
      simplify with monad laws.
      reflexivity.

      rewrite refine_pick_val by eauto.
      reflexivity.


      constructor.
      
      Lemma gtb_true_iff :
        forall x y, gtb x y = true <-> x > y.
      Proof.
        unfold gtb; intros;
        rewrite andb_true_iff, negb_true_iff, beq_nat_false_iff, leb_iff;
        intuition omega.
      Qed.          

      Lemma gtb_false_iff :
        forall x y, gtb x y = false <-> x <= y.
      Proof.
        unfold gtb; intros;
        rewrite andb_false_iff, negb_false_iff, beq_nat_true_iff, leb_iff_conv;
        intuition omega.
      Qed.

      destruct (gtb _ _) eqn:eq_gtb; [ rewrite gtb_true_iff in eq_gtb | rewrite gtb_false_iff in eq_gtb ].
      induction x2; simpl in *; intros;
      inversion_by computes_to_inv.

      Lemma EnsembleListEquivalence_nil_In_False :
        forall {heading} (ens: @IndexedTuple heading -> Prop),
          EnsembleListEquivalence ens (@nil (@IndexedTuple heading)) ->
          (forall x, ens x <-> False).
      Proof.
        intros * equiv ** .
        destruct equiv as ( ? & equiv ).
        rewrite equiv. 
        intuition.
      Qed.

      Lemma EnsembleIndexedListEquivalence_nil_In_False :
        forall {heading} ens,
          EnsembleIndexedListEquivalence ens (@nil (@Tuple heading)) ->
          (forall x, ens x <-> False).
      Proof.
        intros * equiv ** .
        destruct equiv as ( _ & [ ? ( map_nil & ? & equiv ) ] ).
        rewrite equiv. 
        apply map_eq_nil_inv in map_nil; subst.
        intuition.
      Qed.

      rewrite <- H3, <- H4 in eq_gtb;
      simpl in eq_gtb; exfalso; omega.

      Lemma count_query :
        forall {A sch} qs tbl F (P: Tuple -> A),
        forall n,
          computes_to
            (Count (For (UnConstrQuery_In (qsSchema := sch)  qs tbl (fun x => Where (F x) Return (P x) )))) n /\ n > 0 <->
          exists x, F x.
      Proof.
        intros.
        unfold Count, Query_For, UnConstrQuery_In, Query_Where, Query_Return, QueryResultComp, flatten_CompList.
        split; intros; inversion_by computes_to_inv.
        Print computes_to.

        rewrite <- H3 in H2.
        rewrite <- H2 in H1.
        subst. clear H3 x.
        


    (* TODO: Look into Typeclasses Opaque (BoundedString Attribute). *)
  Defined.
End BookStoreExamples.
