Set Implicit Arguments.

(* a typeclass to share notation {a ; b ; ...} *)
Class Listy e t :=
  {
    Nil : t;
    Cons : e -> t -> t
  }.

Module Notations.
  Notation " { } " := Nil (only parsing) : listy_scope.
  Notation " { x ; .. ; y } " := (Cons x .. (Cons y Nil) ..) (only parsing) : listy_scope.
  Module BeginEndNotation.
    Notation " 'begin' 'end' " := Nil (only parsing) : listy_scope.
    Notation " 'begin' x ; .. ; y 'end' " := (Cons x .. (Cons y Nil) ..) (only parsing) : listy_scope.
  End BeginEndNotation.
  Delimit Scope listy_scope with listy.

  (* make sure we didn't mess up with record syntax *)
  Record test_record := { AAA : nat; BBB : nat ; CCC : nat}.

End Notations.

Module Instances.

  Require Import Coq.Lists.List.

  Instance list_Listy e : Listy e (list e) :=
    {
      Nil := nil;
      Cons := @cons _
    }.

End Instances.
