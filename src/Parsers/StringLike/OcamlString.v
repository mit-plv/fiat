Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.StringOperations.
Require Import Fiat.Common.StringFacts.
Require Import Fiat.Common.
Require Import Fiat.Parsers.ExtrOcamlPrimitives.
Require Import Fiat.Parsers.StringLike.Core.

Import Fiat.Parsers.ExtrOcamlPrimitives.Ocaml.

Local Ltac t' :=
  idtac;
  match goal with
    | _ => intro
    | _ => congruence
    | [ |- _ = _ ] => reflexivity
    | [ |- is_true true ] => reflexivity
    | [ |- is_true false ] => exfalso
    | _ => progress autorewrite with ocaml in *
    | [ s : Ocaml.string |- _ ] => generalize dependent (Ocaml.explode s); clear s
    | [ |- Coq.Strings.String.get _ (string_of_list _) = List.nth_error _ _ ]
      => apply get_string_of_list
    | _ => progress simpl in *
    | _ => progress subst
    | [ H : context[string_eq_dec ?x ?y] |- _ ] => destruct (string_eq_dec x y)
    | [ H : context[ascii_eq_dec ?x ?y] |- _ ] => destruct (ascii_eq_dec x y)
    | [ H : Coq.Strings.String.String _ _ = Coq.Strings.String.String _ _ |- _ ] => inversion H; clear H
    | [ H : is_true false |- _ ] => exfalso; clear -H; hnf in H; discriminate
    | _ => progress unfold beq in *
    | _ => rewrite string_dec_refl
    | [ |- RelationClasses.Equivalence _ ] => split
    | [ H : Coq.Strings.String.length ?s = 0 |- _ ] => atomic s; destruct s
    | _ => exfalso; congruence
    | _ => rewrite substring_length
    | _ => rewrite <- plus_n_O
    | _ => rewrite <- Minus.minus_n_O
    | _ => rewrite Min.min_l by omega
    | _ => rewrite Min.min_r by omega
    | _ => rewrite substring_correct3 by assumption
    | _ => rewrite substring_substring
    | _ => rewrite substring_correct3'
    | _ => rewrite substring_correct0
    | _ => rewrite Nat.sub_min_distr_l
    | _ => rewrite Nat.add_sub
    | _ => rewrite Min.min_0_r
    | _ => rewrite Min.min_0_l
    | _ => rewrite Nat.add_1_r
    | _ => rewrite <- Min.min_assoc
    | [ |- String.get _ _ = _ ] => apply StringProperties.get_correct
    | _ => progress rewrite ?string_beq_correct, ?ascii_beq_correct, ?string_copy_length
    | [ H : _ |- _ ] => progress rewrite ?string_beq_correct, ?ascii_beq_correct in H
    | [ |- context[min ?m (?m - ?n)] ]
      => replace (min m (m - n)) with (m - max 0 n)
        by (rewrite <- Nat.sub_min_distr_l; apply f_equal2; omega)
    | [ |- context[min (?m + ?n) ?m] ]
      => replace (min (m + n) m) with (m + min n 0)
        by (rewrite <- Min.plus_min_distr_l; apply f_equal2; omega)
    | _ => rewrite Min.min_comm; reflexivity
    | [ |- context[string_eq_dec ?x ?y] ] => destruct (string_eq_dec x y)
    | [ H : _ <> _ |- False ] => apply H; clear H
    | _ => apply Max.max_case_strong; intro; apply substring_correct4; omega
    | [ H : Coq.Strings.String.length ?s = 1 |- _ ] => is_var s; destruct s
    | [ H : S (Coq.Strings.String.length ?s) = 1 |- _ ] => is_var s; destruct s
    | _ => eexists; rewrite (ascii_lb eq_refl); reflexivity
    | [ |- _ <-> _ ] => split
    | [ H : Coq.Strings.String.get 0 ?s = _ |- _ ] => is_var s; destruct s
    | [ |- Coq.Strings.String.get 0 ?s = _ ] => is_var s; destruct s
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ |- context[Coq.Strings.String.get ?p (Coq.Strings.String.substring _ ?m _)] ]
      => destruct (Compare_dec.lt_dec p m);
        [ rewrite substring_correct1 by omega
        | rewrite substring_correct2 by omega ]
    | _ => rewrite <- substring_correct3'; apply substring_correct2; omega
    | [ H : forall n, Coq.Strings.String.get n _ = Coq.Strings.String.get n _ |- _ ] => apply get_correct in H
    | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
    | [ H : EqNat.beq_nat _ _ = false |- _ ] => apply EqNat.beq_nat_false in H
    | [ H : context[EqNat.beq_nat ?x ?y] |- _ ] => destruct (EqNat.beq_nat x y) eqn:?
    | [ H : context[option_beq ascii_beq _ _] |- _ ] => rewrite (option_beq_correct (@ascii_bl) (@ascii_lb)) in H
    | [ H : context[option_eq_dec ?beq ?bl ?lb ?x ?y] |- _ ] => destruct (option_eq_dec beq bl lb x y)
    | _ => progress change (andb true) with (fun x : bool => x) in *
    | _ => progress cbv beta in *
    | _ => progress simpl in *
    | [ H : ?x = 1 |- context[?x] ] => rewrite H
    | _ => progress unfold beq in *
    | [ |- context[option_beq ?beq ?x (Some _)] ] => destruct x eqn:?
    | _ => progress unfold is_true in *
    | [ |- context[ascii_eq_dec ?x ?y] ] => destruct (ascii_eq_dec x y)
    | [ |- Zbool.Zeq_bool _ _ = _ ] => apply Zbool.Zeq_is_eq_bool
    | [ H : Zbool.Zeq_bool _ _ = _ |- _ ] => apply Zbool.Zeq_is_eq_bool in H
    | [ |- ?x = ?y :> Ocaml.string ]
      => cut (Ocaml.implode (Ocaml.explode x) = Ocaml.implode (Ocaml.explode y));
        [ autorewrite with ocaml; exact (fun z => z)
        | apply f_equal ]
    | [ H : context[String.get ?s ?n], H' : Strings.String.get ?n (Ocaml.explode ?s) = Some _ |- _ ]
      => rewrite (proj2 (@StringProperties.get_correct s n _) H') in H
    | [ H' : Strings.String.get ?n (Ocaml.explode ?s) = Some _ |- context[String.get ?s ?n] ]
      => rewrite (proj2 (@StringProperties.get_correct s n _) H')
    | [ H : forall n, String.safe_get ?str n = String.safe_get ?str' n |- _ ]
      => assert (forall n, Coq.Strings.String.get n (Ocaml.explode str) = Coq.Strings.String.get n (Ocaml.explode str'))
        by (intro n; specialize (H n); autorewrite with ocaml in H; exact H);
        clear H
    | [ |- String.substring ?n ?m ?s = String.substring ?n ?m' ?s ]
      => not constr_eq m m'; replace m with m' by omega
    | [ |- String.substring ?n ?m ?s = String.substring ?n ?m' ?s ]
      => not constr_eq m m'; replace m with m' by (repeat apply Min.min_case_strong; intros; omega)
  end.

Local Ltac t := repeat t'.

Module Export Ocaml.
  Global Instance string_stringlikemin : StringLikeMin Ascii.ascii
    := { String := Ocaml.string;
         length := String.length;
         unsafe_get n s := String.get s n;
         char_at_matches n str P := P (String.get str n) }.

  Global Instance string_stringlike : StringLike Ascii.ascii
    := { get n s := String.safe_get s n;
         take n s := String.sub s 0 n;
         drop n s := String.sub s n (String.length s - n);
         is_char s ch := ((EqNat.beq_nat (String.length s) 1)
                            && (option_beq ascii_beq (String.safe_get s 0) (Some ch)))%bool;
         bool_eq s1 s2 := Zbool.Zeq_bool (z_of_int (Ocaml.String.compare s1 s2)) 0%Z }.

  Global Instance string_stringiso : StringIso Ascii.ascii
    := { of_string s := Ocaml.implode (string_of_list s) }.

  Global Instance string_stringlike_properties : StringLikeProperties Ascii.ascii.
  Proof.
    refine {| strings_nontrivial n := ex_intro (fun str : String => length str = n) (Ocaml.implode (string_copy n "."%char)) _ |};
      t.
  Qed.

  Global Instance string_stringiso_properties : StringIsoProperties Ascii.ascii.
  Proof.
    split; simpl; t.
  Qed.

  Global Instance string_stringeq_properties : StringEqProperties Ascii.ascii.
  Proof.
    split; simpl; t.
  Qed.
End Ocaml.
