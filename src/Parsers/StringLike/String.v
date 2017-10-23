(** * Definitions of some specific string-like types *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Common Fiat.Common.Equality.
Require Import Fiat.Common.StringOperations Fiat.Common.StringFacts.
Require Import Fiat.Parsers.StringLike.Core.

Set Implicit Arguments.

Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (Nat.neq_succ_0 _ H) end.

Definition dummy_ch : Ascii.ascii.
Proof.
  repeat constructor.
Qed.

Global Instance string_stringlikemin : StringLikeMin Ascii.ascii
  := { String := string;
       char_at_matches n str P := match String.get n str with
                                    | Some ch => P ch
                                    | None => true
                                  end;
       unsafe_get n s := match String.get n s with
                           | Some ch => ch
                           | None => dummy_ch
                         end;
       length := String.length }.

Global Instance string_stringlike : StringLike Ascii.ascii
  := { is_char str ch := string_beq str (String.String ch ""%string);
       take n s := String.substring 0 n s;
       drop n s := String.substring n (String.length s) s;
       get := String.get;
       bool_eq := string_beq }.

Global Instance string_stringiso : StringIso Ascii.ascii
  := { of_string := string_of_list }.

Local Ltac t :=
  repeat match goal with
           | _ => intro
           | [ |- _ = _ ] => reflexivity
           | _ => assumption
           | [ |- is_true true ] => reflexivity
           | [ |- is_true false ] => exfalso
           | [ |- String.get _ (string_of_list _) = List.nth_error _ _ ]
             => apply get_string_of_list
           | _ => progress simpl in *
           | _ => progress subst
           | [ H : context[string_eq_dec ?x ?y] |- _ ] => destruct (string_eq_dec x y)
           | [ H : context[ascii_eq_dec ?x ?y] |- _ ] => destruct (ascii_eq_dec x y)
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
           | _ => rewrite substring_correct0
           | _ => rewrite Nat.sub_min_distr_l
           | _ => rewrite Nat.add_sub
           | _ => rewrite Min.min_0_r
           | _ => rewrite Min.min_0_l
           | _ => rewrite Nat.add_1_r
           | _ => rewrite <- Min.min_assoc
           | [ H : ?x = Some _ |- context[match ?x with _ => _ end] ] => rewrite H
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
           | [ H : String.length ?s = 1 |- _ ] => is_var s; destruct s
           | [ H : S (String.length ?s) = 1 |- _ ] => is_var s; destruct s
           | _ => eexists; rewrite (ascii_lb eq_refl); reflexivity
           | [ |- _ <-> _ ] => split
           | [ H : String.get 0 ?s = _ |- _ ] => is_var s; destruct s
           | [ |- String.get 0 ?s = _ ] => is_var s; destruct s
           | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
           | [ |- context[String.get ?p (String.substring _ ?m _)] ]
             => destruct (Compare_dec.lt_dec p m);
               [ rewrite substring_correct1 by omega
               | rewrite substring_correct2 by omega ]
           | _ => rewrite <- substring_correct3'; apply substring_correct2; omega
           | [ H : forall n, String.get n _ = String.get n _ |- _ ] => apply get_correct in H
           | [ H : context[match ?e with _ => _ end], H' : ?e = Some _ |- _ ]
             => rewrite H' in H
           | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
           | [ H : forall x, Some x = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
           | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
         end.

Global Instance string_stringlike_properties : StringLikeProperties Ascii.ascii.
Proof.
  refine {| strings_nontrivial n := ex_intro (fun str : String => length str = n) (string_copy n "."%char) _ |};
    t.
Qed.

Global Instance string_stringiso_properties : StringIsoProperties Ascii.ascii.
Proof. split; t. Qed.

Global Instance string_stringeq_properties : StringEqProperties Ascii.ascii.
Proof. split; t. Qed.

Lemma substring_take_drop (str : String) n m
: String.substring n m str = take m (drop n str).
Proof.
  simpl.
  rewrite substring_substring; simpl.
  apply Min.min_case_strong; simpl; trivial; [].
  intro H.
  apply substring_correct4; omega.
Qed.

Local Ltac eq_Proper_t :=
  let H := fresh in
  let H' := fresh in
  intros ?? H ?? H';
    apply string_bl in H'; apply string_bl in H; repeat subst;
    reflexivity.

Global Instance eq_string_beq_Proper
: Proper (beq ==> beq ==> eq) (@eq String.string).
Proof. eq_Proper_t. Qed.
Global Instance eq_string_beq_Proper'
: Proper (beq ==> beq ==> eq) (@eq (@StringLike.String _ string_stringlikemin)).
Proof. eq_Proper_t. Qed.
Global Instance eq_string_beq_impl_Proper
: Proper (beq ==> beq ==> impl) (@eq String.string).
Proof. eq_Proper_t. Qed.
Global Instance eq_string_beq_impl_Proper'
: Proper (beq ==> beq ==> impl) (@eq (@StringLike.String _ string_stringlikemin)).
Proof. eq_Proper_t. Qed.
Global Instance beq_string_Equivalence
: (@Equivalence String.string (@beq Ascii.ascii string_stringlikemin _))
  := bool_eq_Equivalence.
