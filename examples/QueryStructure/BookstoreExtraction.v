Require Import Computation.Core ADT ADTRefinement ADTNotation BuildADTRefinements.
Require Import Bool String String_as_OT OrderedTypeEx.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlString.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.QSImplementation
        BookstorewDelegation.

Definition BookStoreDelegateReps
: ilist (fun ns => Type) (qschemaSchemas BookStoreSchema).
  simpl.
  BuildQSDelegateReps BookStoreImpl.
Defined.

Definition BookStoreDelegateSearchUpdateTerms
: ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
        (qschemaSchemas BookStoreSchema).
  simpl; BuildQSDelegateSigs BookStoreImpl.
Defined.

Definition BookStoreDelegateImpls
: i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
               (Rep : Type) =>
             ComputationalADT.pcADT
               (BagSig (@Tuple (schemaHeading (relSchema ns)))
                       (BagSearchTermType SearchTerm)
                       (BagUpdateTermType SearchTerm))
               Rep)
          BookStoreDelegateSearchUpdateTerms
          BookStoreDelegateReps.

  unfold BookStoreDelegateReps,
  BookStoreDelegateSearchUpdateTerms; simpl.
  BuildQSDelegateImpls BookStoreImpl.
Defined.

Definition ExtractWorthyBookStoreImpl : ComputationalADT.cADT BookStoreSig.
  let s := eval unfold BookStoreImpl in BookStoreImpl in
      let Impl := eval simpl in
      (Sharpened_Implementation s
                                (LookupQSDelegateReps BookStoreDelegateReps)
                                (LookupQSDelegateImpls BookStoreDelegateImpls)) in
          exact Impl.
Defined.

(* And we get a result worthy of extraction! *)
Print ExtractWorthyBookStoreImpl.




(*
Open Scope string.

Definition bookstore :=
  match BookStore with
    | existT bookstore _ => bookstore
  end.

Definition eval {A} (comp: Comp A) : option A :=
  match comp with
    | Return _ x => Some x
    | _          => None
  end.

Require Import QueryStructureNotations.

Definition init_bookstore (_: unit) :=
  eval (callCons bookstore "Init" ()).

Definition add_book (author title: string) (isbn: nat) (rep: Rep bookstore) : option (_ * bool) :=
  eval (Methods bookstore ``("AddBook") rep <sAUTHOR :: author, sTITLE :: title, sISBN :: isbn>).

Definition place_order (isbn date: nat) (rep: Rep bookstore) : option (_ * bool) :=
  eval (Methods bookstore ``("PlaceOrder") rep <sISBN :: isbn, sDATE :: date>).

Definition get_titles (author: string) (rep: Rep bookstore) : option (_ * list string) :=
  eval (Methods bookstore ``("GetTitles") rep (author)).

Definition num_orders (author: string) (rep: Rep bookstore) : option (_ * nat) :=
  eval (Methods bookstore ``("NumOrders") rep (author)).

Extraction "examples/bookstore.ml" init_bookstore add_book place_order get_titles num_orders.
 *)
