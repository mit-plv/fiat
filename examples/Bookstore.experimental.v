Section BookStoreExamples.
  Require Import QueryStructureNotations.
  Require Import ListImplementation.
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
      unfold BookStoreListImpl_AbsR in H; split_and.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

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
      unfold BookStoreListImpl_AbsR in H; split_and.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.
 
      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over BookStorage using search term
              (Some n, (@None nat, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite (bfind_correct _).

      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto. 
      simplify with monad laws.
      finish honing.
    }

    

    (* TODO: Look into Typeclasses Opaque (BoundedString Attribute). *)
  Defined.
End BookStoreExamples.
