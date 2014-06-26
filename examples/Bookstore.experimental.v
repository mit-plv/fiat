Section BookStoreExamples.
  Require Import QueryStructureNotations.
  Require Import ListImplementation.
  Require Import ConstraintChecksRefinements.
  Require Import Bags AdditionalLemmas AdditionalRefinementLemmas AdditionalMorphisms Bool tupleAgree.

  Unset Implicit Arguments.

  Opaque binsert benumerate bfind bcount.

  Ltac prove_decidability_for_functional_dependencies :=
    simpl; econstructor; intros;
    try setoid_rewrite <- eq_nat_dec_bool_true_iff;
    try setoid_rewrite <- string_dec_bool_true_iff;
    setoid_rewrite and_True;
    repeat progress (
             try setoid_rewrite <- andb_true_iff;
             try setoid_rewrite not_true_iff_false;
             try setoid_rewrite <- negb_true_iff);
    rewrite bool_equiv_true;
    reflexivity.

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
        "PlaceOrder" : rep × Order → rep × bool,
        "AddBook" : rep × Book → rep × bool,
        "GetTitles" : rep × string → rep × list string,
        "NumOrders" : rep × string → rep × nat
      }.

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreSchema {
      const "InitBookstore" (_ : unit) : rep := empty,

      update "PlaceOrder" ( o : Order ) : bool :=
          Insert o into sORDERS,

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

  (* TODO: *)
  Notation "?[ A ]" := (if A then true else false) (at level 50).
 
 (* TODO: Find a way to do the instantiations automatically *)

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    (* Step 1: Drop the constraints on the tables. From the perspective
      of a client of a sharpened ADT the invariants will still hold,
      since ADT refinement preserves the simulation relation. *)

    start honing QueryStructure.

    hone representation using BookStoreListImpl_AbsR.
    
    hone constructor "InitBookstore". {
       unfold BookStoreListImpl_AbsR.
      simplify with monad laws.

      rewrite (refine_pick_val' (bempty, bempty)) by (intuition; apply bempty_correct_DB).
      subst_body; higher_order_1_reflexivity. 
    }

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
      unfold BookStoreListImpl_AbsR in H0; split_and.
      simplify with monad laws.

      rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index.
      simplify with monad laws.

      rewrite (refine_foreign_key_check_into_query (fun (b: Book) => n!sISBN = b!sISBN)) 
        by eauto with typeclass_instances.
      simplify with monad laws; cbv beta; 
      simpl.

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
      setoid_rewrite refine_trivial_if_then_else.
      simplify with monad laws.

      unfold BookStoreListImpl_AbsR.
      Split Constraint Checks.
 
      refineEquiv_pick_pair_benumerate.
      simplify with monad laws.

      rewrite (refine_pick_val' (fst r_n)) by refine_list_insert_in_other_table.
      simplify with monad laws.

      rewrite refine_pick_val by binsert_correct_DB.
      simplify with monad laws.
      reflexivity.

      rewrite refine_pick_val by eauto.
      simplify with monad laws.
      reflexivity.
    }

    Lemma blah1 : (* TODO: Get rid of this *)
      forall (n: @Tuple BookSchema), 
        DecideableEnsemble
          (fun x : Tuple =>
             tupleAgree_computational n x [sISBN]%SchemaConstraints /\
             ~ tupleAgree_computational n x [sTITLE; sAUTHOR]%SchemaConstraints).
    Proof.
      prove_decidability_for_functional_dependencies.
    Defined.

    hone method "AddBook". {
      unfold BookStoreListImpl_AbsR in H0; split_and.
      simplify with monad laws.

      rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index.
      simplify with monad laws.
 
      rewrite refine_tupleAgree_refl_True.
      simplify with monad laws.

      rewrite (refine_functional_dependency_check_into_query n); 
        [ | prove_decidability_for_functional_dependencies | ].

      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In_Where; instantiate (1 := @blah1 n). (* TODO: get rid of blah1 *)
      rewrite refine_List_For_Query_In_Return_Permutation.
      simplify with monad laws.

      rewrite filter over BookStorage
              using search term (@None string, (Some n!sISBN, [ 
                                  (fun (x: Book) => (negb (?[string_dec x!sTITLE n!sTITLE]))
                                                 || (negb (?[string_dec x!sAUTHOR n!sAUTHOR])))
                                ])).
      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Count.
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.
      
      rewrite (refine_pick_val' true) by (clear; admit). (* Redundant check *)
      simplify with monad laws.

      setoid_rewrite map_length.
      
      unfold BookStoreListImpl_AbsR; simpl.
      Split Constraint Checks.

      refineEquiv_pick_pair_benumerate;
      simplify with monad laws.

      rewrite refine_pick_val by binsert_correct_DB. 
      simplify with monad laws. 

      rewrite refine_pick_val by refine_list_insert_in_other_table.
      simplify with monad laws.
      reflexivity.

      setoid_rewrite refine_pick_val; eauto.
      simplify with monad laws; reflexivity.

      admit. (* Classical logic thing; should go away when the specs are changed *)
    }
    

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

      Definition gtb x y :=
        andb (leb y x) (negb (beq_nat x y)). 

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

    (* TODO: Look into Typeclasses Opaque (BoundedString Attribute). *)
  Defined.
End BookStoreExamples.
