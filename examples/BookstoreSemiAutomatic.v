Require Import ADTSynthesis.QueryStructure.Refinements.AutoDB.

Locate EnsembleListEquivalence.

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
      Constructor "Init" : unit -> rep,
      Method "PlaceOrder" : rep x Order -> rep x bool,
      Method "DeleteOrder" : rep x nat -> rep x list Order,
      Method "AddBook" : rep x Book -> rep x bool,
      Method "DeleteBook" : rep x nat -> rep x list Book,
      Method "GetTitles" : rep x string -> rep x list string,
      Method "NumOrders" : rep x string -> rep x nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS,

    update "DeleteOrder" ( oid : nat ) : list Order :=
        Delete o from sORDERS where o!sISBN = oid ,

    update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS ,

    update "DeleteBook" ( id : nat ) : list Book :=
        Delete book from sBOOKS where book!sISBN = id ,

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

Theorem BookStoreManual :
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

    deleteChecksSucceeded.

    finish honing.
  }

  hone method "DeleteBook". {
    startMethod BookStore_AbsR.

    setoid_rewrite refine_if_bool_eta.
    simplify with monad laws.

    delete_preserves_primary_keys.

    delete_foreign_key_check_to_Query (sAUTHOR, sISBN).

    Split Constraint Checks;
      [ deleteChecksSucceeded; reflexivity
      | deleteChecksFailed].
  }

  unfold cast, eq_rect_r, eq_rect, eq_sym; simpl.

  (* At this point our implementation is fully computational: we're done! *)

  Show.

Ltac ilist_of_evar1 C B As k :=
  match As with
    | nil => k (fun c : C => inil B)
    | cons ?a ?As' =>
      makeEvar (forall c : C, B a)
               ltac:(fun b =>
                       ilist_of_evar1
                         C B As'
                         ltac:(fun Bs' => k (fun c : C => icons a (b c) (Bs' c))))
  end.

Ltac FullySharpenEachMethod1 delegateSigs delegateSpecs :=
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_evar1
        (ilist ComputationalADT.cADT delegateSigs)
        (fun Sig => ComputationalADT.cMethodType Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths => ilist_of_evar1
                              (ilist ComputationalADT.cADT delegateSigs)
                              (fun Sig => ComputationalADT.cConstructorType Rep (consDom Sig))
                              consSigs
                              ltac:(fun cCons =>
                                      eapply Notation_Friendly_SharpenFully
                                      with
                                      (rep := fun _ => Rep)
                                      (cAbsR :=
                                         fun (DelegateImpl : ilist
                                                          (fun Sig : ADTSig =>
                                                             ComputationalADT.cADT Sig)
                                                          delegateSigs)
                                             (ref : forall n : nat,
                                                      Dep_Option_elim_T2
                                                        (fun (Sig : ADTSig) (adt : ADT Sig)
                                                             (adt' : ComputationalADT.cADT Sig) =>
                                                           refineADT adt (ComputationalADT.LiftcADT adt'))
                                                        (ith_error (inil ADT) n) (ith_error DelegateImpl n)) => @eq _)
                                    (DelegateSpecs := delegateSpecs)
                                             (cConstructors := cCons)
                                             (cMethods := cMeths)));
        unfold Dep_Type_BoundedIndex_app_comm_cons; simpl;
        intuition; intros; subst
  end.

  Ltac make_computational_constructor :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(b) end in
    let x' := (eval pattern a, b in x) in
    let f' := match x' with ?f' _ _ => constr:(f') end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

Ltac make_computational_method :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b) end in
    let b' := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b') end in
    let c := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(c) end in
    let x' := (eval pattern a, b, b', c in x) in
    let f' := match x' with ?f' _ _ _ _ => constr:(fun i a => f' i (fst a) (snd a)) end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

Lemma refineIfret {A} :
  forall (cond : bool) (a a' : A),
    refine (if cond then ret a else ret a')
           (ret (if cond then a else a')).
Proof.
  destruct cond; reflexivity.
Qed.



  FullySharpenEachMethod1 (@nil ADTSig) (inil ADT); cbv beta; simpl;
  intros; subst; setoid_rewrite refineEquiv_pick_eq';
  simplify with monad laws.

  make_computational_constructor.

  setoid_rewrite refineIfret; simplify with monad laws; injection H; intros; subst;
  make_computational_method.
  injection H; intros; subst; simpl; make_computational_method.
  setoid_rewrite refineIfret; simplify with monad laws;
  injection H; intros; subst; simpl; make_computational_method.
  setoid_rewrite refineIfret; simplify with monad laws;
  injection H; intros; subst; simpl; make_computational_method.
  injection H; intros; subst; simpl; make_computational_method.
  injection H; intros; subst; simpl; make_computational_method.

Defined.

Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl.
