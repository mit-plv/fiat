(* Finite maps for labels *)

Require Import Bedrock.LabelMap.

Require Import Coq.Strings.Ascii Coq.NArith.NArith Coq.Strings.String Coq.Structures.OrderedType Coq.FSets.FSetAVL.

Module StringKey.
  Definition t := string.

  Definition eq := @eq t.
  Definition lt (s1 s2 : t) := string_lt s1 s2 = true.

  Theorem eq_refl : forall x : t, eq x x.
    congruence.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
    congruence.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    congruence.
  Qed.

  Section hide_hints.
    Hint Resolve string_lt_trans.
    Hint Rewrite string_lt_irrel : LabelMap.
    Hint Immediate string_tail_neq.
    Hint Resolve string_lt_sym.
    Hint Rewrite string_lt_irrel : LabelMap.

    Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      unfold lt; intuition (congruence || eauto).
    Qed.

    Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      unfold lt, eq; intuition; subst; autorewrite with LabelMap in *; discriminate.
    Qed.

    Definition compare' (x y : t) : comparison :=
      if string_lt x y
        then Datatypes.Lt
        else if string_dec x y
          then Datatypes.Eq
          else Gt.

    Definition compare (x y : t) : Structures.OrderedType.Compare lt eq x y.
      refine (match compare' x y as c return c = compare' x y -> Structures.OrderedType.Compare lt eq x y with
                | Datatypes.Lt => fun _ => Structures.OrderedType.LT _
                | Datatypes.Eq => fun _ => Structures.OrderedType.EQ _
                | Gt => fun _ => Structures.OrderedType.GT _
              end (refl_equal _)); abstract (unfold compare', eq, lt in *;
                repeat match goal with
                         | [ H : context[if ?E then _ else _] |- _ ] => let Heq := fresh "Heq" in case_eq E; (intros ? Heq || intro Heq);
                           rewrite Heq in H; try discriminate
                       end; intuition).
    Defined.

    Definition eq_dec x y : { eq x y } + { ~ eq x y }.
      refine (if string_dec x y then left _ _ else right _ _);
        abstract (unfold eq in *; destruct x; destruct y; simpl in *; congruence).
    Defined.
  End hide_hints.
End StringKey.


Module StringSet := FSetAVL.Make(StringKey).

Remove Hints StringSet.MSet.Raw.L.eq_cons StringSet.E.lt_trans
  StringSet.E.lt_not_eq StringSet.E.eq_trans StringSet.X'.eq_trans.

Require Coq.FSets.FSetFacts.
Module StringFacts := FSetFacts.WFacts_fun(StringKey)(StringSet).
