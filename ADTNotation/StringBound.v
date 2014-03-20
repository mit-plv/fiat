Require Import List String.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section StringBound.

  Class StringBound (s : string) (Bound : list string) :=
    { sbound : In s Bound }.

  Global Instance StringBound_head (s : string) (Bound : list string)
  : StringBound s (s :: Bound).
  Proof.
    econstructor; simpl; eauto.
  Qed.

  Global Instance StringBound_tail
           (s s' : string) (Bound : list string)
           {sB' : StringBound s Bound}
  : StringBound s (s' :: Bound).
  Proof.
    econstructor; simpl; right; apply sbound.
  Qed.

  Record BoundedString (Bound : list string) :=
    { bstring :> string;
      stringb :> StringBound bstring Bound }.

End StringBound.
