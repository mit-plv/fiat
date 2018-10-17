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
    Def ADT {
    rep := QueryStructure BookStoreSchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "PlaceOrder" (r : rep) (o : Order) : rep * bool :=
        Insert o into r!sORDERS,

    Def Method1 "DeleteOrder" (r : rep) (oid : nat) : rep * list Order :=
        Delete o from r!sORDERS where o!sISBN = oid,

    Def Method1 "AddBook" (r : rep) (b : Book) : rep * bool :=
        Insert b into r!sBOOKS,

    Def Method1 "DeleteBook" (r : rep) (id : nat) : rep * list Book :=
        Delete book from r!sBOOKS where book!sISBN = id,

    Def Method1 "GetTitles" (r : rep) (author : string) : rep * list string :=
        titles <- For (b in r!sBOOKS)
                  Where (author = b!sAUTHOR)
                  Return (b!sTITLE);
        ret (r, titles),

    Def Method1 "NumOrders" (r : rep) (author : string) : rep * nat :=
        count <- Count (For (o in r!sORDERS) (b in r!sBOOKS)
                        Where (author = b!sAUTHOR)
                        Where (o!sISBN = b!sISBN)
                        Return ());
        ret (r, count)
  }%methDefParsing.

Record DelegationADT (Sig : ADTSig)
  : Type
  := Build_SharpenedUnderDelegates
       { DelegateeIDs : nat;
         DelegateeSigs : Fin.t DelegateeIDs -> ADTSig;
         DelegatedImplementation :
           forall (DelegateImpls : forall idx,
                      ADT (DelegateeSigs idx)),
             ADT Sig;
         DelegateeSpecs : forall idx, ADT (DelegateeSigs idx) }.

Theorem SharpenedBookStore :
  FullySharpened BookStoreSpec.
Proof.
  start sharpening ADT.

  eapply SharpenStep.

  match goal with
    |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
    eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep); idtac
  end.

  exfalso; admit.

  eapply refine_Methods_cons.

  exfalso; admit.

  eapply refine_Methods_cons.
  exfalso; admit.

  eapply refine_Methods_cons.

  simpl; intros.
  match goal with
  | |- refine _ (?E _ _) => let H := fresh in set (H := E)
  end.

  cbv delta [GetAttribute] beta; simpl.

  remove trivial insertion checks.

  (* The trivial insertion checks involve the fresh id,
       so we need to drill under the binder before
       attempting to remove them. *)
  rewrite refine_bind; set_refine_evar.
  3: unfold pointwise_relation; intros.
  3: drop_symmetric_functional_dependencies.

  (* (* 3: fundepToQuery. *) *)

  3: match goal with
  | |- context [ {b : _ | decides b (forall tup' : IndexedRawTuple, GetUnConstrRelation ?or ?Ridx _ -> @FunctionalDependency_P ?hhint ?attrlist1 ?attrlist2 ?n _)} ]
    =>
        let H' := fresh in
        let H'' := fresh in
        let refine_fundep := fresh in
        assert
         (H' :
          (forall tup' : IndexedRawTuple, GetUnConstrRelation or Ridx tup' -> @FunctionalDependency_P hhint attrlist1 attrlist2 n (indexedElement tup')) <->
          (forall tup' : IndexedRawTuple,
           ~ (GetUnConstrRelation or Ridx tup' /\ tupleAgree n (indexedElement tup') attrlist2 /\ ~ tupleAgree n (indexedElement tup') attrlist1))) by
         (unfold FunctionalDependency_P; dec_tauto);
         assert (H'' : DecideableEnsemble (fun x : RawTuple => tupleAgree_computational n x attrlist2 /\ ~ tupleAgree_computational n x attrlist1)) by
          (subst_all; FunctionalDependencyAutomation.prove_decidability_for_functional_dependencies);
         (let refine_fundep := eval simpl in (refine_functional_dependency_check_into_query n attrlist2 attrlist1 or H'' H') in
          setoid_rewrite refine_fundep; clear H'' H')
     end.
  3: simplify with monad laws.
  3: pose_string_hyps.

  Require Import
        Coq.Strings.String
        Fiat.Common
        Fiat.Common.StringBound
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.Tactics.HintDbExtra
        Fiat.Common.Tactics.TransparentAbstract
        Fiat.Computation.Refinements.General
        Fiat.Computation.SetoidMorphisms
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

  (* (* pose_heading_hyps. *) *)
  3: (* Commenting this line out makes the proof go through *)
  repeat foreach [ headingCache ] run (fun id => progress fold id).

  Unshelve.
  all: exfalso; admit.
Qed.


let FindAttributeUses := EqExpressionAttributeCounter in
let BuildEarlyIndex := ltac:(LastCombineCase6 BuildEarlyEqualityIndex) in
let BuildLastIndex := ltac:(LastCombineCase5 BuildLastEqualityIndex) in
let IndexUse := EqIndexUse in
let createEarlyTerm := createEarlyEqualityTerm in
let createLastTerm := createLastEqualityTerm in
let IndexUse_dep := EqIndexUse_dep in
let createEarlyTerm_dep := createEarlyEqualityTerm_dep in
let createLastTerm_dep := createLastEqualityTerm_dep in
let BuildEarlyBag := BuildEarlyEqualityBag in
let BuildLastBag := BuildLastEqualityBag in
let PickIndex := ltac:(fun makeIndex =>
                           GenerateIndexesForAll FindAttributeUses ltac:(fun attrlist =>
                                                         let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in makeIndex attrlist')) in
    PickIndex ltac:(fun attrlist =>
                      make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex).

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ => False) : t).
admit.

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ _ _ => False) : t).
admit.

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ _ _ => False) : t).
admit.

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ _ _ => False) : t).
admit.

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ _ _ => False) : t).
admit.

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ _ _ => False) : t).
admit.

compute in (type of H).
let H := (eval unfold H in H) in
let t := type of H in
unify H ((fun _ _ _ => False) : t).
admit.

exfalso.
admit.

Unshelve.
admit.

Defined.

let FindAttributeUses := EqExpressionAttributeCounter in
let BuildEarlyIndex := ltac:(LastCombineCase6 BuildEarlyEqualityIndex) in
let BuildLastIndex := ltac:(LastCombineCase5 BuildLastEqualityIndex) in
let IndexUse := EqIndexUse in
let createEarlyTerm := createEarlyEqualityTerm in
let createLastTerm := createLastEqualityTerm in
let IndexUse_dep := EqIndexUse_dep in
let createEarlyTerm_dep := createEarlyEqualityTerm_dep in
let createLastTerm_dep := createLastEqualityTerm_dep in
let BuildEarlyBag := BuildEarlyEqualityBag in
let BuildLastBag := BuildLastEqualityBag in
           Implement_Bags BuildEarlyBag BuildLastBag.

Time Defined.

Time Definition BookstoreImpl : ComputationalADT.cADT BookStoreSig :=
  Eval simpl in projT1 SharpenedBookStore.

Print BookstoreImpl.
