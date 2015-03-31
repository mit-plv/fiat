(** * Definitions of some specific string-like types *)
Require Import Coq.Strings.String Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Equality.

Set Implicit Arguments.

Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (Nat.neq_succ_0 _ H) end.

Section indexed.
  Variable base : string.

  Definition index_to_string (s : nat * nat) : string
    := substring (fst s) (snd s) base.

  Definition indexed_string_stringlike : StringLike Ascii.ascii
    := {| String := nat * nat;
          is_char s ch := ((Nat.eq_dec (min (String.length base - fst s) (snd s)) 1) && (option_dec Ascii.ascii_dec (String.get (fst s) base) (Some ch)))%bool;
          length s := min (String.length base - fst s) (snd s);
          take n s := (fst s, min (snd s) n);
          drop n s := (fst s + n, snd s - n);
          bool_eq s1 s2 := string_dec (index_to_string s1) (index_to_string s2) |}.

  Local Existing Instance indexed_string_stringlike.

  Local Arguments string_dec : simpl never.
  Local Arguments option_dec : simpl never.

  Global Instance indexed_string_stringlike_properties : StringLikeProperties Ascii.ascii.
  Proof.
    Start Profiling.
    Timeout 10 split;
    repeat match goal with
             | _ => intro
             | [ |- _ = _ ] => reflexivity
             | [ |- is_true true ] => reflexivity
             | [ |- is_true false ] => exfalso
             | [ |- true = false ] => exfalso
             | [ |- false = true ] => exfalso
             | [ H : is_true (_ && _) |- _ ] => apply Bool.andb_true_iff in H
             | [ H : and _ _ |- _ ] => destruct H
             | [ H : prod _ _ |- _ ] => destruct H
             | _ => progress simpl in *
             | _ => progress subst
             | _ => progress unfold index_to_string in *
             | [ H : context[string_dec ?x ?y] |- _ ] => destruct (string_dec x y)
             | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
             | [ H : is_true false |- _ ] => exfalso; clear -H; hnf in H; discriminate
             | _ => progress unfold beq, option_rect in *
             | _ => rewrite string_dec_refl
             | [ |- Equivalence _ ] => split
             | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : String.length ?s = 0 |- _ ] => atomic s; destruct s
             | [ H : context[Nat.eq_dec ?x ?y] |- _ ] => destruct (Nat.eq_dec x y)
             | [ H : context[option_dec ?H ?x ?y] |- _ ] => destruct (option_dec H x y)
             | [ |- context[Nat.eq_dec ?x ?y] ] => destruct (Nat.eq_dec x y)
             | [ |- context[option_dec ?H ?x ?y] ] => destruct (option_dec H x y)
             | [ H : ?x = ?x |- _ ] => clear H
             | _ => exfalso; congruence
             | _ => rewrite substring_length
             | _ => rewrite <- plus_n_O
             | _ => rewrite <- Minus.minus_n_O
             | _ => rewrite Min.min_l by omega
             | _ => rewrite Min.min_r by omega
             | _ => rewrite substring_correct3 by assumption
             | _ => rewrite substring_substring
             | _ => rewrite substring_correct3'
             | _ => rewrite substring1_get
             | [ H : _ |- _ ] => rewrite substring1_get in H
             | [ H : _ |- _ ] => rewrite substring_correct0 in H
             | _ => apply substring_min; assumption
             | _ => rewrite Nat.sub_min_distr_l
             | _ => rewrite Nat.add_sub
             | _ => rewrite Min.min_0_r
             | _ => rewrite Min.min_0_l
             | _ => rewrite <- Min.min_assoc
             | [ H : appcontext[match ?e with None => _ | _ => _ end] |- _ ]
               => revert H; case_eq e
             | [ |- 0 = S _ ] => exfalso
             | [ |- S _ = 0 ] => exfalso
             | [ |- S _ = S _ ] => apply f_equal
             | [ |- ?n = 0 ] => is_var n; destruct n
             | [ |- ?n = 1 ] => is_var n; destruct n
             | [ |- min _ ?x = 1 ] => is_var x; destruct x
             | [ |- min _ (S ?x) = 1 ] => is_var x; destruct x
             | [ H : min _ 0 = 1 |- _ ] => exfalso; clear -H; rewrite min_r in H by omega
             | [ H : min _ ?x = 1 |- _ ] => is_var x; destruct x
             | [ H : min _ (S ?x) = 1 |- _ ] => is_var x; destruct x
             | [ H : min ?x (S (S ?y)) = 1 |- _ ]
               => revert H; apply (Min.min_case x (S (S y)))
             | [ H : String.length ?str - ?x = ?y' |- context[substring ?x ?y ?str] ]
               => rewrite (@substring_correct4 str x y y') by omega
             | [ H : String.length ?str - ?x = ?y', H' : context[substring ?x ?y ?str] |- _ ]
               => rewrite (@substring_correct4 str x y y') in H' by omega
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
             | _ => congruence
           end.
Focus 10.
match goal with
  | |- context[
pose (@substring_substring base y (n0 - y) n n0).
.
Show Profile.
Focus 10.


    match goal with
    end.
    2:omega.
    2:omega.
    match goal with

end.
    SearchAbout min.

    do 4 match goal with
             | _ => congruence
end.

Focus 2.

repeat match goal with
    end.
    Focus 2.
    simpl in *.
    rewrite substring1_get in e.
    SearchAbout option.




    Focus 6.

    SearchAbout substring_length.

    Focus 2.


    SearchAbout get substring.
    congruence.
    SearchAbout (_ && _)%bool true.
  Qed.
