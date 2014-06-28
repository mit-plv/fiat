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
 * to save on type-checking time.
 * (Thanks for being weird, Coq!) *)
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

(* Aliases for internal names of the two tables *)
Definition Books := BookStoreSchema/sBOOKS. 
Definition Orders := BookStoreSchema/sORDERS.

(* Aliases for internal notions of schemas for the two tables *)
Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

(* Now we define an index structure for each table. *)

Definition BookStorage : @BagPlusBagProof Book.
  mkIndex BookSchema [ Books//sAUTHOR; Books//sISBN ].
Defined.
(* In other words, index first on the author field, then the ISBN field.
 * Works especially efficiently for accesses keyed on author. *)

Definition OrderStorage : @BagPlusBagProof Order.
  mkIndex OrderSchema [ Orders//sISBN ].
Defined.

(* Each index has an associate datatype.  Let's name each one. *)
Definition TBookStorage := BagType BookStorage.
Definition TOrderStorage := BagType OrderStorage.

(* This abstraction relation connects:
 * 1. Abstract database from reference implementation, using sets
 * 2. Our fancy realization, using search trees (from Bags library) *)
Definition BookStoreListImpl_AbsR
           (or : UnConstrQueryStructure BookStoreSchema)
           (nr : TBookStorage * TOrderStorage) : Prop :=
  or!sBOOKS ≃ benumerate (fst nr) /\ or!sORDERS ≃ benumerate (snd nr).

Definition BookStore :
  Sharpened BookStoreSpec.
Proof.
  unfold BookStoreSpec.

  (* Step 1: Drop the constraints on the tables. From the perspective
    of a client of a sharpened ADT the invariants will still hold,
    since ADT refinement preserves the simulation relation. *)

  start honing QueryStructure.

  hone representation using BookStoreListImpl_AbsR.

  hone constructor "Init". {
    startMethod BookStoreListImpl_AbsR.
    finishMethod.
  }

  hone method "NumOrders"; [ observer | ].

  hone method "GetTitles"; [ observer | ].

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

  finish sharpening.
Defined.
