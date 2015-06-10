Require Import Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.AutoDB.

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
  Eval simpl in
    QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "PlaceOrder" ( r : rep , o : Order ) : bool :=
        Insert o into r!sORDERS,

    update "DeleteOrder" (r : rep, oid : nat ) : list Order :=
       Delete o from r!sORDERS where True,

    update "AddBook" (r : rep, b : Book ) : bool :=
        Insert b into r!sBOOKS ,

     update "DeleteBook" ( r : rep, id : nat ) : list Book :=
        Delete book from r!sBOOKS where book!sISBN = id,

    query "GetTitles" (r : rep, author : string ) : list string :=
      For (b in r ! sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE),

    query "NumOrders" (r : rep, author : string ) : nat :=
      Count (For (o in r!sORDERS) (b in r!sBOOKS)
                 Where (author = b!sAUTHOR)
                 Where (o!sISBN = b!sISBN)
                 Return ())
}.

Arguments ilist2 : simpl never.
Arguments ilist2_tl : simpl never.
Arguments ilist2_hd : simpl never.

Theorem SharpenedBookStore :
  MostlySharpened BookStoreSpec.
Proof.

  Time start_honing_QueryStructure.

  let attrlist := constr:(icons2 (a := Vector.hd (qschemaSchemas BookStoreSchema)) [("EqualityIndex", @Fin.F1 2); ("EqualityIndex", Fin.FS (Fin.FS (@Fin.F1 0)))] (icons2 [("EqualityIndex", @Fin.F1 1 )] inil2) : ilist2 (B := fun sch => list (prod string (Attributes (rawSchemaHeading sch)))) (qschemaSchemas BookStoreSchema) ) in
  make simple indexes using attrlist.

  initializer.
  Implement_Insert_Checks.
  etransitivity.


  Ltac implement_Query' k k_dep:=
  Focused_refine_Query;
  [ (* Step 1: Implement [In / Where Combinations] by enumerating and joining. *)
    implement_In_opt;
    (* Step 2: Move filters to the outermost [Join_Comp_Lists] to which *)
    (* they can be applied. *)
    distribute_filters_to_joins (*;
    (* Step 3: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep *)
  |
  ]; pose_string_hyps; pose_heading_hyps.

Ltac implement_Query CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  implement_Query'
    ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex)
           ltac:(find_simple_search_term_dep makeClause_dep EarlyIndex_dep LastIndex_dep).

  match goal with
  | |- context[Query_For _] =>
    setoid_rewrite refineEquiv_swap_bind at 1;
      implement_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                      EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep end.

  match goal with
      |- refine (l <- Join_Filtered_Comp_Lists ?l1 ?l2 ?f; _) _
      =>  let T := type of f in
          makeEvar T
                   ltac:(fun g =>
                           let eqv := fresh in
                           assert (ExtensionalEq f g) as eqv;
                         [ try apply ExtensionalEq_andb_true
                         | rewrite (@Join_Filtered_Comp_Lists_ExtensionalEq_filters _ _ _ _ _ l1 l2 f g eqv); clear eqv ])
  end.

Ltac get_ithDefault f n k :=
  match type of f with
    | ilist2 (B := @RawTuple) ?A -> ?C =>
      let G := fresh "G" in
      let p := fresh "p" in
      let H := fresh "H" in
      let proj := fresh "proj" in
      let proj := eval simpl in
      (fun b : ilist2 (B := @RawTuple) A => ith2 b n) in
          evar (G : @RawTuple (Vector.nth A n) -> C);
        assert (H : forall p, f p = G (proj p)) by
          (subst G; intro p;
           let p' := eval simpl in (proj p) in
               pattern p';
           match goal with
             | [ |- (fun t => @?f t = @?g t) _ ] => equate g f; reflexivity
           end); clear H;
        let G' := eval unfold G in G in clear G; k G'
  end.

Unset Ltac Debug.
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- ExtensionalEq ?f _ ] =>
      let n := match type of f with (ilist2 (n := S ?n) _ -> _) => n end in
      get_ithDefault f (@Fin.F1 n)
                     ltac:(fun filter_dec =>
                             let heading := match type of filter_dec with
                                            | @RawTuple ?heading -> bool => constr:(heading)
                                            end in
                             let schemas := eval simpl in (qschemaSchemas qs_schema) in
                                 find_equivalent_tuple schemas heading
                                                       ltac:(fun id => let idx' := constr:({| bindex := id |} : BoundedIndex (map relName (qschemaSchemas qs_schema)))
                                                                       in let idx := eval simpl in idx' in
                                                                              let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
                                                                                  let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                                      let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                                          let search_term_type := eval unfold search_term_type' in search_term_type' in
                                                                                          makeEvar (search_term_type)
                                                                                                   ltac: (fun search_term =>
                                                                                                            let eqv := fresh in
                                                                                                            assert (forall a, filter_dec a
                                                                                                                              = search_term_matcher search_term a) as eqv;
                                                                                                          [ build_search_term qs_schema idx
                                                                                                                              filter_dec search_term
                                                                                                          | match goal with
                                                                                                                |- ExtensionalEq ?f ?search_term' =>
                                                                                                                match type of f with
                                                                                                                  | ?A -> _ =>
                                                                                                                    unify search_term' (fun a : A => search_term_matcher search_term (ith2 unit_Tuple a 0))
                                                                                                                end
                                                                                                            end;
                                                                                                            unfold ExtensionalEq in *; intros;
                                                                                                            simpl in *; rewrite <- eqv; simpl; reflexivity
                                                                                                          ]))) end.


convert_filter_to_search_term.

Ltac implement_filters_with_find k k_dep:=
  repeat (try (convert_filter_to_search_term; (* This will fail if there's no filter on the join. *)
               [first [find_equivalent_search_term k
                      | find_equivalent_search_term_pair k_dep]
               | cbv beta; simpl; convert_filter_search_term_to_find]);
          pose_string_hyps; pose_heading_hyps;
          apply refine_under_bind; intros);
  apply List_Query_In_Return.


Ltac implement_In_opt' :=
  match goal with
    (* Implement a List_Query_In of a list [l] applied to a UnConstrQuery_In [idx]
        by enumerating [idx] with a method call and joining the result with [l] *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (List_Query_In ?l (fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b) )) _ ] =>
      etransitivity;
        [ let H' := eval simpl in (refine_Filtered_Join_Query_In_Enumerate' H (idx := idx) f (l := l)) in
              apply H'
        |  apply refine_under_bind; intros; implement_In_opt' ]

    (* Implement a 'naked' UnConstrQuery_In as a call to enumerate *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
      etransitivity;
        [ let H' := eval simpl in (refine_Filtered_Query_In_Enumerate H (idx := idx) f) in
              apply H'
        | apply refine_under_bind; intros; implement_In_opt' ]

    (* Convert all Where clauses to filters.*)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (List_Query_In ?b (fun b : ?QueryT => Where (@?P b) (@?resultComp b))) _ ] =>
       etransitivity;
         [ let H' := eval simpl in (@refine_List_Query_In_Where QueryT _ b P resultComp _) in
               apply H'
         | implement_In_opt'; implement_In_opt' ]

    (* Finish if no progress can be made. This may miss some
       filters if In and Where Clauses are mixed. *)
    | _ =>
      repeat rewrite <- filter_and;
        repeat setoid_rewrite andb_true_r;
        higher_order_reflexivity

  end.
Ltac implement_In_opt :=
  etransitivity;
  [ implement_In_opt' | ].

Unset Ltac Debug.

implement_In_opt.

Ltac find_equiv_tl a As f g :=
  (* Find an equivalent function on just the tail of an ilist*)
  let a := fresh in
  let H := fresh in
  assert (forall a : ilist (Vector.cons a _ As), f a = g (ilist2_tl a)) as H;
    [let a := fresh in
     intro a;
       match goal with
           |- ?f = ?g (ilist2_tl a)=>
           let f' :=  match eval pattern (ilist2_tl a) in f
                      with ?f' (ilist2_tl a) => eval simpl in f' end in
                   unify f' g
               end; reflexivity
             | clear H].

Unset Ltac Debug.

Unset Ltac Debug.
simpl.
Set Ltac Debug.

distribute_filters_to_joins.


  match goal with
  | |- context[Query_For _] =>
    setoid_rewrite refineEquiv_swap_bind at 1;
      implement_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                      EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep end.


        CreateTerm EarlyIndex LastIndex
                      makeClause_dep EarlyIndex_dep LastIndex_dep;
      eapply refine_under_bind; intros
  end


  insertion .

  Set Printing Implicit.
  Set Printing Coercions.
  simpl.


  Check UnConstrQueryStructure.
  Check BookStoreSchema.
  (* 552 MB vs 624MB. *)
  partial_master_plan EqIndexTactics.

  FullySharpenQueryStructure BookStoreSchema Index.
  Time Defined.
(* <130 seconds for master_plan.
   <141 seconds for Defined. *)

Time Definition BookstoreImpl' : SharpenedUnderDelegates BookStoreSig :=
  Eval simpl in projT1 SharpenedBookStore.

Print BookstoreImpl'.
