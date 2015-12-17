Require Import Fiat.QueryStructure.Automation.MasterPlan.

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
      Constructor "Init" : rep,
      Method "PlaceOrder" : rep * Order -> rep * bool,
      Method "DeleteOrder" : rep * nat -> rep * (list Order),
      Method "AddBook" : rep * Book -> rep * bool,
      Method "DeleteBook" : rep * nat -> rep * (list Book),
      Method "GetTitles" : rep * string -> rep * (list string),
      Method "NumOrders" : rep * string -> rep * nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  Eval simpl in
    QueryADTRep BookStoreSchema {
    Def Constructor0 "Init" : rep := empty,

    Def Method1 "PlaceOrder" ( r : rep) (o : Order ) : rep * bool :=
        Insert o into r!sORDERS,

    Def Method1 "DeleteOrder" (r : rep) (oid : nat) : rep * list Order :=
       Delete o from r!sORDERS where o!sISBN = oid,

    Def Method1 "AddBook" (r : rep) (b : Book ) : rep * bool :=
        Insert b into r!sBOOKS ,

    Def Method1 "DeleteBook" ( r : rep) (id : nat ) : rep * list Book :=
        Delete book from r!sBOOKS where book!sISBN = id,

    Def Method1 "GetTitles" (r : rep) (author : string) : rep * list string :=
        titles <- For (b in r ! sBOOKS)
               Where (author = b!sAUTHOR)
               Return (b!sTITLE);
    ret (r, titles),

    Def Method1 "NumOrders" (r : rep) (author : string ) : rep * nat :=
      count <- Count (For (o in r!sORDERS) (b in r!sBOOKS)
                              Where (author = b!sAUTHOR)
                              Where (o!sISBN = b!sISBN)
                              Return ());
      ret (r, count)
}%methDefParsing.

Lemma GetRel_FiniteTableAbsR:
  forall (qsSchema : QueryStructureSchema) (qs qs' : UnConstrQueryStructure qsSchema)
         (Ridx : Fin.t (numRawQSschemaSchemas qsSchema)),
    FiniteTables_AbsR qs qs'
    -> GetUnConstrRelation qs Ridx = GetUnConstrRelation qs' Ridx.
Proof.
  unfold FiniteTables_AbsR; intros; intuition; subst; eauto.
Qed.

Lemma FiniteTable_FiniteTableAbsR
      {qsSchema}
  : forall (qs qs' : UnConstrQueryStructure qsSchema)
           (idx : Fin.t (numRawQSschemaSchemas qsSchema)),
    FiniteTables_AbsR qs qs'
    -> FiniteEnsemble (GetUnConstrRelation qs idx).
Proof.
  unfold FiniteTables_AbsR; intros; intuition; subst; eauto.
Qed.

Lemma FiniteTable_FiniteTableAbsR'
      {qsSchema}
  : forall (qs qs' : UnConstrQueryStructure qsSchema)
           (idx : Fin.t (numRawQSschemaSchemas qsSchema)),
    FiniteTables_AbsR qs qs'
    -> FiniteEnsemble (GetUnConstrRelation qs' idx).
Proof.
  unfold FiniteTables_AbsR; intros; intuition; subst; eauto.
Qed.

Ltac subst_FiniteTables_AbsR :=
  match goal with
  | [ H : FiniteTables_AbsR ?r_o ?r_n
      |- context [?r_o] ]=> rewrite (proj1 H)
  | [ H : FiniteTables_AbsR ?r_o ?r_n
    |- context [GetUnConstrRelation ?r_o ?Ridx] ]=>
  rewrite (@GetRel_FiniteTableAbsR _ r_o r_n Ridx H)
end.

Ltac Finite_FiniteTables_AbsR :=
match goal with
| [ H : FiniteTables_AbsR ?r_o ?r_n
    |- context [FiniteEnsemble (GetUnConstrRelation ?r_o ?Ridx)] ]=>
  eapply (@FiniteTable_FiniteTableAbsR _ r_o r_n Ridx H)
| [ H : FiniteTables_AbsR ?r_o ?r_n
    |- context [FiniteEnsemble (GetUnConstrRelation ?r_n ?Ridx)] ]=>
  eapply (@FiniteTable_FiniteTableAbsR' _ r_o r_n Ridx H)
end.

Ltac doAny' srewrite_fn drills_fn finish_fn :=
  let repeat_srewrite_fn := repeat srewrite_fn in
  try repeat_srewrite_fn;
    try apply_under_subgoal drills_fn ltac:(repeat_srewrite_fn);
    finish_fn.

Ltac simplify_queries :=
  first [
           simplify with monad laws
         | progress unfold UnConstrQuery_In
         | rewrite (@refine_Where_Intersection _ _ _ _ _ _)
         | Finite_FiniteTables_AbsR
         | subst_FiniteTables_AbsR
         ].

Theorem SharpenedBookStore :
  FullySharpened BookStoreSpec.
Proof.

  start sharpening ADT.
  pose_string_hyps.
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl | ]
                          ])]
    end | ].
  - doAny' drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone representation using (@FiniteTables_AbsR BookStoreSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill.
      repeat simplify_queries.
      (rewrite_drill || finish honing).
      repeat simplify_queries.
      (rewrite_drill || finish honing).
      repeat simplify_queries.
      (rewrite_drill || finish honing).
      repeat simplify_queries.
      (rewrite_drill || finish honing).

    simplify_queries; set_refine_evar.
    repeat simplify_queries.
    Focus 2.
    repeat simplify_queries.
    (rewrite_drill || finish honing).

    doAny' simplify_queries rewrite_drill ltac:(try finish honing).

    rewrite_drill.
    { subst_FiniteTables_AbsR.
      finish honing. }

    finish honing.
    repeat first [
             simplify with monad laws
           | rewrite (@refine_Where_Intersection _ _ _ _ _ _)
           | Finite_FiniteTables_AbsR
           | subst_FiniteTables_AbsR
           ].
    rewrite_drill.
    repeat first [
             simplify with monad laws
           | rewrite (@refine_Where_Intersection _ _ _ _ _ _)
           | Finite_FiniteTables_AbsR
           | subst_FiniteTables_AbsR
           ].
    finish honing.

    simplify with monad laws.

    rewrite_drill.

    eauto using FiniteTable_FiniteTableAbsR',
      FiniteTable_FiniteTableAbsR.
    Focus 2.
    eapply FiniteTable_FiniteTableAbsR.
    unfold QueryResultComp; setoid_rewrite flatten_CompList_Return.
    finish honing.
    eapply ((proj2 H0) Fin.F1).
    simplify with monad laws.

    Ltac implement_stuff  :=
      repeat (cbv beta; simpl;
              first
                [simplify with monad laws; simpl
                | setoid_rewrite refine_If_Then_Else_Bind
                | rewrite (@FiniteTables_AbsR_Insert BookStoreSchema);
                  try simplify with monad laws; eauto
                | rewrite (@FiniteTables_AbsR_Delete BookStoreSchema);
                  eauto with typeclass_instances
                | try (refine pick val _; [ | eassumption ])
             ]).
    etransitivity.

Ltac stuff :=
  doAny ltac:(implement_stuff) rewrite_drill ltac:(finish honing).
stuff.
simpl.
destruct H0; subst.
finish honing.
  - etransitivity. stuff.
    destruct H0; subst; finish honing.
  - simplify with monad laws.
    unfold UnConstrQuery_In.
    Focused_refine_Query.
    rewrite (@refine_Where_Intersection _ _ _ _ _ _); eauto.
    unfold QueryResultComp; setoid_rewrite flatten_CompList_Return.
    finish honing.
    eapply ((proj2 H0) Fin.F1).
    simplify with monad laws.
    etransitivity.
    stuff.
    destruct H0; subst.
    finish honing.
  - simplify with monad laws.
    unfold UnConstrQuery_In.
    Focused_refine_Query.
    unfold QueryResultComp.
    setoid_rewrite (@refine_Where_Intersection _ _ _ _ _ _); eauto.
    unfold QueryResultComp; setoid_rewrite flatten_CompList_Return.
    finish honing.
    eapply ((proj2 H0) Fin.F1).
    simplify with monad laws.
    etransitivity.
    stuff.
    destruct H0; subst.
    finish honing.

    rewrite_drill.
Focus 2.
rewrite_drill.
Focus 2.
rewrite_drill.
rewrite (@FiniteTables_AbsR_Insert BookStoreSchema);
  try simplify with monad laws; eauto.

simpl.
    unfold QueryResultComp. set_evars. unfold FlattenCompList.flatten_CompList.
    finish honing.
    Show Existentials.
    unfold Query_For.
    unfold QueryResultComp; simpl.


  }

  master_plan EqIndexTactics.
      (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan EqIndexTactics. *)

Time Defined.

Time Definition BookstoreImpl : ComputationalADT.cADT BookStoreSig :=
  Eval simpl in projT1 SharpenedBookStore.

Print BookstoreImpl.
