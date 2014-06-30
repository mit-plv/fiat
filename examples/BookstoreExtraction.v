Require Import Computation.Core ADT ADTRefinement ADTNotation BuildADTRefinements.
Require Import Bool String String_as_OT OrderedTypeEx Bookstore.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlString.

Extract Inlined Constant fst => fst.
Extract Inlined Constant snd => snd.
Extract Inlined Constant negb => not.
Extract Inlined Constant List.length => "List.length".
Extract Inlined Constant app => "( @ )".
Extract Constant String_as_OT.eq_dec  => "(=)".
Extract Constant Nat_as_OT.eq_dec     => "(=)".

Extract Constant String_as_OT.compare => "fun a b -> let comp = compare a b in 
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant Nat_as_OT.compare    => "fun a b -> let comp = compare a b in 
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant String_as_OT.string_compare => "fun a b -> let comp = compare a b in 
                                                 if comp = 0 then Eq else if comp < 0 then Lt else Gt".

Extract Inductive reflect            => bool [ true false ].
Extract Inlined Constant iff_reflect => "".

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
