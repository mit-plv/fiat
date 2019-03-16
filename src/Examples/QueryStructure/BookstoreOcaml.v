Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bookstore.

Time Definition BookstoreImpl : ComputationalADT.cADT BookStoreSig :=
  Eval simpl in projT1 SharpenedBookStore.

Require Import Fiat.Computation.Core Fiat.ADT Fiat.ADTRefinement Fiat.ADTNotation Fiat.ADTRefinement.BuildADTRefinements.
Require Import Fiat.Common.String_as_OT Coq.Structures.OrderedTypeEx.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlNatInt Coq.extraction.ExtrOcamlZInt Coq.extraction.ExtrOcamlString.

Extract Inlined Constant fst => fst.
Extract Inlined Constant snd => snd.
Extract Inlined Constant negb => not.
Extract Inlined Constant List.length => "List.length".
Extract Inlined Constant app => "( @ )".
Extract Constant String_as_OT.eq_dec  => "(=)".
Extract Constant Nat_as_OT.eq_dec     => "(=)".

Extract Constant String_as_OT.compare => "fun a b -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant Nat_as_OT.compare    => "fun (a: int) (b: int) -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant String_as_OT.string_compare => "fun a b -> let comp = compare a b in
                                                 if comp = 0 then Eq else if comp < 0 then Lt else Gt".

Extract Inductive reflect => bool [ true false ].
Extract Inlined Constant iff_reflect => "".

Open Scope string.

Definition bookstore :=
  match BookstoreImpl with
    | existT bookstore _ => bookstore
  end.

Require Import QueryStructureNotations.

Definition init_bookstore : ComputationalADT.cRep BookstoreImpl :=
  Eval simpl in (CallConstructor BookstoreImpl "Init").

Definition add_book (author title: string) (isbn: nat) (rep: ComputationalADT.cRep BookstoreImpl) : (_ * bool) :=
  Eval simpl in CallMethod BookstoreImpl "AddBook" rep <sAUTHOR :: author, sTITLE :: title, sISBN :: isbn>.

Definition place_order (isbn date: nat) (rep: ComputationalADT.cRep BookstoreImpl) : (_ * bool) :=
  Eval simpl in CallMethod BookstoreImpl "PlaceOrder" rep <sISBN :: isbn, sDATE :: date>.

Definition get_titles (author: string) (rep: ComputationalADT.cRep BookstoreImpl) : (_ * list string) :=
  Eval simpl in CallMethod BookstoreImpl "GetTitles" rep (author).

Definition num_orders (author: string) (rep: ComputationalADT.cRep BookstoreImpl) : (_ * nat) :=
  Eval simpl in CallMethod BookstoreImpl "NumOrders" rep (author).

Extraction "bookstore.ml" init_bookstore add_book place_order get_titles num_orders.
