Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.
Definition boolToWord (b : bool) : W :=
  if b then Word.natToWord _ 1 else Word.natToWord _ 0.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.
Opaque Word.natToWord.
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
              schema <sAUTHOR :: W,
                      sTITLE :: W,
                      sISBN :: W>
                      where UniqueAttribute ``sISBN;
      relation sORDERS has
              schema <sISBN :: W,
                      sDATE :: W> ]
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

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure BookStoreSchema,

    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "PlaceOrder" ( r : rep) (o : Order) : rep * bool :=
        Insert o into r!sORDERS,

    Def Method1 "AddBook" (r : rep) (b : Book) : rep * bool :=
        Insert b into r!sBOOKS ,

    Def Method1 "GetTitles" (r : rep) (author : W) : rep * list W :=
        titles <- For (b in r ! sBOOKS)
               Where (author = b!sAUTHOR)
               Return (b!sTITLE);
    ret (r, titles),

    Def Method1 "NumOrders" (r : rep) (author : W ) : rep * W :=
      count <- Count (For (o in r!sORDERS) (b in r!sBOOKS)
                              Where (author = b!sAUTHOR)
                              Where (o!sISBN = b!sISBN)
                              Return ());
      ret (r, Word.natToWord 32 count)
}%methDefParsing.

Theorem SharpenedBookStore :
  MostlySharpened BookStoreSpec.
Proof.

  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  hone method "AddBook".
  { setoid_rewrite UniqueAttribute_symmetry.
    setoid_rewrite (@refine_uniqueness_check_into_query' BookStoreSchema Fin.F1 _ _ _ _).
    setoid_rewrite refine_For_rev.
    setoid_rewrite refine_Count.
    simplify with monad laws; simpl in *; subst.
    setoid_rewrite refine_pick_eq'.
    setoid_rewrite refine_bind_unit.
    setoid_rewrite refine_If_Then_Else_Duplicate.
    finish honing. }
  GenerateIndexesForAll EqExpressionAttributeCounter
  ltac:(fun attrlist =>
          let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in
              make_simple_indexes attrlist'
                                  ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                         ltac:(LastCombineCase5 BuildLastEqualityIndex)).
  + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + hone method "PlaceOrder".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      setoid_rewrite app_nil_r;
        setoid_rewrite map_map; simpl.
      unfold ilist2_hd at 1; simpl.
      setoid_rewrite rev_length.
      setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1.
      eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "AddBook".
    { simpl in *; subst; simplify with monad laws.
      setoid_rewrite app_nil_r;
        setoid_rewrite map_map; simpl.
      unfold ilist2_hd at 1; simpl.
      repeat setoid_rewrite rev_length.
      setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "GetTitles".
    { simpl in *; subst; simplify with monad laws.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite app_nil_r, map_map; unfold ilist2_hd; simpl.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "NumOrders".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      setoid_rewrite app_nil_r.
      rewrite (CallBagEnumerate_fst H0); simpl.
      etransitivity.
      eapply refine_under_bind_both.
      refine (@Join_Comp_Lists_eq BookStoreSchema Index Fin.F1 _ _ _ _ _).
      intros; finish honing.
      simplify with monad laws.
      unfold H2; apply refine_under_bind.
      intros.
      apply Join_Comp_Lists_eq' in H3; rewrite H3.
      finish honing.
    }
    simpl; eapply reflexivityT.
  + unfold CallBagFind, CallBagInsert.
    pose_headings_all.
    match goal with
    | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
      FullySharpenQueryStructure Schema Indexes
    end.

    Time Defined.

Time Definition BookstoreImpl :=
  Eval simpl in (fst (projT1 SharpenedBookStore)).

Print BookstoreImpl.
