Require Import Computation.Core ADT ADTRefinement ADTNotation BuildADTRefinements.
Require Import String BagsExtraction Bookstore.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlString.

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
