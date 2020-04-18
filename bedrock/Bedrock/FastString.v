(* FastString -- speedy versions of string functions from String

This library defines tail-recursive, unverified versions of some of the
functions in String.  It's intended to be used in unverified applications
(e.g., the Bedrock assembly generator) where speed is important. *)

Require Import Coq.Strings.Ascii Coq.Lists.List.
Require Export Coq.Strings.String.

Module Import ForReverse.

  Fixpoint foldString {A} (f : A -> ascii -> A) (str : string) (zero : A) : A :=
    match str with
      | EmptyString => zero
      | String character str' => foldString f str' (f zero character)
    end.

  Definition prependReversed : string -> string -> string :=
    foldString (fun char str => String str char).

End ForReverse.

Definition reverse str := prependReversed str "".

Definition concat (strs : list string) : string :=
  reverse (fold_left (fun x y => prependReversed y x) strs ""%string).

Definition append x y := concat (x :: y :: nil).
Infix "++" := append : string_scope.


(* Intercalate.  This implementation is direct from the Haskell base
package. *)

Module Import ForIntercalate.
  Fixpoint prependToAll (sep : string) (xs : list string) :=
        match xs with
          | nil => nil
          | x :: xs => sep :: x :: prependToAll sep xs
        end.
End ForIntercalate.

Definition intersperse (sep : string) (xs : list string) : list string :=
  match xs with
    | nil => nil
    | x :: xs => x :: prependToAll sep xs
  end.

Definition intercalate (sep : string) (xs : list string) : string :=
  concat (intersperse sep xs).
