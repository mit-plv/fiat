(** * Definitions of some specific string-like types *)
Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.

Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (Nat.neq_succ_0 _ H) end.

Global Instance string_stringlike : StringLike string
  := { Char := Ascii.ascii;
       is_char str ch := string_dec str (String.String ch ""%string);
       length := String.length;
       take n s := substring 0 n s;
       drop n s := substring n (String.length s) s;
       bool_eq := string_dec }.

Local Arguments string_dec : simpl never.

Global Instance string_stringlike_properties : StringLikeProperties string.
Proof.
  split;
  repeat match goal with
           | _ => intro
           | [ |- _ = _ ] => reflexivity
           | [ |- is_true true ] => reflexivity
           | [ |- is_true false ] => exfalso
           | _ => progress simpl in *
           | _ => progress subst
           | [ H : context[string_dec ?x ?y] |- _ ] => destruct (string_dec x y)
           | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
           | [ H : is_true false |- _ ] => exfalso; clear -H; hnf in H; discriminate
           | _ => progress unfold beq in *
           | _ => rewrite string_dec_refl
           | [ |- Equivalence _ ] => split
           | [ H : String.length ?s = 0 |- _ ] => atomic s; destruct s
           | _ => exfalso; congruence
           | _ => rewrite substring_length
           | _ => rewrite <- plus_n_O
           | _ => rewrite <- Minus.minus_n_O
           | _ => rewrite Min.min_l by omega
           | _ => rewrite Min.min_r by omega
           | _ => rewrite substring_correct3 by assumption
           | _ => rewrite substring_substring
           | _ => rewrite substring_correct3'
           | _ => rewrite Nat.sub_min_distr_l
           | _ => rewrite Nat.add_sub
           | _ => rewrite Min.min_0_r
           | _ => rewrite Min.min_0_l
           | _ => rewrite <- Min.min_assoc
           | [ |- context[min ?m (?m - ?n)] ]
             => replace (min m (m - n)) with (m - max 0 n)
               by (rewrite <- Nat.sub_min_distr_l; apply f_equal2; omega)
           | [ |- context[min (?m + ?n) ?m] ]
             => replace (min (m + n) m) with (m + min n 0)
               by (rewrite <- Min.plus_min_distr_l; apply f_equal2; omega)
           | _ => rewrite Min.min_comm; reflexivity
           | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
           | [ H : _ <> _ |- False ] => apply H; clear H
           | _ => apply Max.max_case_strong; intro; apply substring_correct4; omega
         end.
Qed.
