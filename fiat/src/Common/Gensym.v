(** * Generate a symbol distinct from every element of a list of symbols *)
(** Assumes a way to generate a new symbol from a pair of symbols "greater" than either one. *)
Require Import Coq.Classes.RelationClasses Coq.Lists.List Coq.omega.Omega.
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Common.StringFacts.

Set Implicit Arguments.

Class PreGensym A :=
  { s_gt : A -> A -> Prop;
    sym_init : A;
    combine_symbols : A -> A -> A;
    s_gt_Asymmetric :> Asymmetric s_gt;
    s_gt_Transitive :> Transitive s_gt;
    combine_respectful_l : forall x y, s_gt (combine_symbols x y) x;
    combine_respectful_r : forall x y, s_gt (combine_symbols x y) y }.

Delimit Scope gensym_scope with gensym.
Infix ">" := s_gt : gensym_scope.

Fixpoint gensym {A} {H : PreGensym A} (used : list A) : A
  := match used with
       | nil => sym_init
       | cons x xs => combine_symbols x (gensym xs)
     end.

Lemma gensym_gt {A} {H : PreGensym A} (ls : list A)
: forall x, List.In x ls -> (gensym ls > x)%gensym.
Proof.
  intro x.
  induction ls as [|l ls IHls]; simpl.
  { intros []. }
  { intros [H'|H']; subst.
    { apply combine_respectful_l. }
    { etransitivity; [ apply combine_respectful_r | ].
      apply IHls, H'. } }
Qed.

Lemma gensym_fresh {A} {H : PreGensym A} (ls : list A)
: ~List.In (gensym ls) ls.
Proof.
  intro H'.
  apply gensym_gt in H'.
  apply asymmetry in H'; assumption.
Qed.

Global Instance gensym_nat : PreGensym nat
  := { s_gt := gt;
       sym_init := 0;
       combine_symbols x y := S (x + y) }.
Proof.
  repeat intro; abstract omega.
  repeat intro; abstract omega.
  repeat intro; abstract omega.
  repeat intro; abstract omega.
Defined.

Global Instance gensym_string : PreGensym string
  := { s_gt x y := gt (length x) (length y);
       sym_init := ""%string;
       combine_symbols x y := String.String "a"%char (x ++ y)%string }.
Proof.
  repeat intro; abstract omega.
  repeat intro; abstract omega.
  simpl; repeat intro; abstract (rewrite concat_length; omega).
  simpl; repeat intro; abstract (rewrite concat_length; omega).
Defined.
