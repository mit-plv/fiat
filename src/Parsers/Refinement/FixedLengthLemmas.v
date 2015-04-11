(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import Coq.Program.Equality.
Require Import ADTSynthesis.Common.
Require Import ADTSynthesis.Common.Wf.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Parsers.BaseTypes.

Set Implicit Arguments.

Inductive length_result := same_length (n : nat) | different_lengths | cyclic_length | not_yet_handled_empty_rule.

Fixpoint length_of_any_production' {Char} (length_of_any_nt : String.string -> length_result)
         (its : production Char) : length_result
  := match its with
       | nil => same_length 0
       | (Terminal _)::xs => match length_of_any_production' length_of_any_nt xs with
                               | same_length n => same_length (S n)
                               | different_lengths => different_lengths
                               | cyclic_length => cyclic_length
                               | not_yet_handled_empty_rule => not_yet_handled_empty_rule
                             end
       | (NonTerminal nt)::xs => match length_of_any_nt nt, length_of_any_production' length_of_any_nt xs with
                                   | same_length n1, same_length n2 => same_length (n1 + n2)
                                   | cyclic_length, _ => cyclic_length
                                   | _, cyclic_length => cyclic_length
                                   | different_lengths, _ => different_lengths
                                   | _, different_lengths => different_lengths
                                   | not_yet_handled_empty_rule, _ => not_yet_handled_empty_rule
                                   | _, not_yet_handled_empty_rule => not_yet_handled_empty_rule
                                 end
     end.

Lemma length_of_any_production'_ext {Char}
      f g
      (ext : forall b, f b = g b)
      b
: @length_of_any_production' Char f b = length_of_any_production' g b.
Proof.
  induction b as [ | x ]; try reflexivity; simpl.
  destruct x; rewrite ?IHb, ?ext; reflexivity.
Qed.

Definition length_of_any_productions'_f
  := (fun x1 x2
      => match x1, x2 with
           | same_length n1, same_length n2 => if Nat.eq_dec n1 n2 then same_length n1 else different_lengths
           | cyclic_length, _ => cyclic_length
           | _, cyclic_length => cyclic_length
           | _, different_lengths => different_lengths
           | different_lengths, _ => different_lengths
           | not_yet_handled_empty_rule, _ => not_yet_handled_empty_rule
           | _, not_yet_handled_empty_rule => not_yet_handled_empty_rule
         end).

Arguments length_of_any_productions'_f !_ !_ / .

Lemma length_of_any_productions'_f_same_length {n x1 x2}
: length_of_any_productions'_f x1 x2 = same_length n
  <-> (x1 = same_length n /\ x2 = same_length n).
Proof.
  destruct x1, x2; simpl in *;
  repeat match goal with
           | _ => reflexivity
           | [ H : context[Nat.eq_dec ?x ?y] |- _ ] => destruct (Nat.eq_dec x y)
           | [ |- context[Nat.eq_dec ?x ?y] ] => destruct (Nat.eq_dec x y)
           | _ => progress subst
           | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
           | _ => intro
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- _ /\ _ ] => split
           | [ |- _ <-> _ ] => split
           | _ => congruence
           | _ => tauto
         end.
Qed.

Lemma length_of_any_productions'_f_same_length_fold_right {n x1 x2}
: fold_right length_of_any_productions'_f x1 x2 = same_length n
  <-> (x1 = same_length n /\ fold_right and True (map (fun k => k = same_length n) x2)).
Proof.
  induction x2; simpl in *; eauto; try tauto.
  rewrite length_of_any_productions'_f_same_length.
  rewrite IHx2.
  tauto.
Qed.

Definition length_of_any_productions' {Char} (length_of_any_nt : String.string -> length_result)
           (prods : productions Char)
: length_result
  := match prods with
       | nil => not_yet_handled_empty_rule
       | p::ps => fold_right
                    length_of_any_productions'_f
                    (length_of_any_production' length_of_any_nt p)
                    (map (length_of_any_production' length_of_any_nt) ps)
     end.

Lemma length_of_any_productions'_ext {Char}
      f g
      (ext : forall b, f b = g b)
      b
: @length_of_any_productions' Char f b = length_of_any_productions' g b.
Proof.
  unfold length_of_any_productions'.
  destruct b as [ | ? b]; trivial; [].
  induction b; try reflexivity; simpl;
  erewrite length_of_any_production'_ext by eassumption; trivial; [].
  edestruct (length_of_any_production' g);
    rewrite IHb; reflexivity.
Qed.

Definition length_of_any_nt_step {Char} (G : grammar Char) (predata := @rdp_list_predata _ G)
           (valid0 : nonterminals_listT)
           (length_of_any_nt : forall valid, nonterminals_listT_R valid valid0
                                             -> String.string -> length_result)
           (nt : String.string)
: length_result.
Proof.
  refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal valid0 nt)
          then length_of_any_productions'
                 (@length_of_any_nt (remove_nonterminal valid0 nt) (remove_nonterminal_dec _ _ _))
                 (Lookup G nt)
          else different_lengths);
  assumption.
Defined.

Lemma length_of_any_nt_step_ext {Char G}
      x0 f g
      (ext : forall y p b, f y p b = g y p b)
      b
: @length_of_any_nt_step Char G x0 f b = length_of_any_nt_step g b.
Proof.
  unfold length_of_any_nt_step.
  edestruct Sumbool.sumbool_of_bool; trivial.
  apply length_of_any_productions'_ext; eauto.
Qed.

Definition length_of_any_nt {Char} (G : grammar Char) initial : String.string -> length_result
  := let predata := @rdp_list_predata _ G in
     @Fix _ _ ntl_wf _
          (@length_of_any_nt_step _ G)
          initial.

Definition length_of_any {Char} (G : grammar Char) : String.string -> length_result
  := @length_of_any_nt Char G initial_nonterminals_data.

Definition length_of_any_productions {Char} G := @length_of_any_productions' Char (@length_of_any Char G).

Lemma has_only_terminals_parse_of_production_length (G : grammar Ascii.ascii) {n}
      f pat
      (H_f : forall nt str n', f nt = same_length n' -> parse_of G str (Lookup G nt) -> String.length str = n')
      (H : length_of_any_production' f pat = same_length n)
      str
      (p : parse_of_production G str pat)
: String.length str = n.
Proof.
  revert n H; induction p; simpl in *.
  { congruence. }
  { edestruct (_ : item _).
    { match goal with
        | [ H : context[length_of_any_production' ?f ?p] |- _ ] => revert H; case_eq (length_of_any_production' f p); intros
      end;
      repeat match goal with
               | [ H : ?x = ?x |- _ ] => clear H
               | [ H : ?x = _ :> length_result, H' : context[?x] |- _ ] => rewrite H in H'
               | _ => exfalso; discriminate
               | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
               | _ => progress subst
               | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
               | [ H : is_true (_ ~= [ _ ])%string_like |- _ ] => apply length_singleton in H
               | [ H : _ |- _ ] => progress rewrite ?(@take_length _ string_stringlike _), ?(@drop_length _ string_stringlike _), ?substring_length, ?Plus.plus_0_r, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.add_sub in H
               | [ H : context[min ?x (?y + ?z) - ?z] |- _ ] => rewrite <- (@NPeano.Nat.sub_min_distr_r x (y + z) z) in H
               | [ H : context[min ?x ?y], H' : ?x <= ?y |- _ ] => rewrite (@Min.min_l x y) in H by assumption
               | [ H : context[min ?x ?y], H' : ?y <= ?x |- _ ] => rewrite (@Min.min_r x y) in H by assumption
               | [ H : context[min (?x - ?y) ?x] |- _ ] => rewrite (@Min.min_l (x - y) x) in H by (clear; omega)
               | [ H : forall n, same_length _ = same_length n -> _ |- _ ] => specialize (H _ eq_refl)
               | [ H : context[min _ _] |- _ ] => revert H; apply Min.min_case_strong; intros; omega
             end. }
    { intros.
      match goal with
        | [ H : context[f ?x] |- _ ] => revert H; case_eq (f x); intros
      end;
        match goal with
          | [ H : context[length_of_any_production' ?f ?p] |- _ ] => revert H; case_eq (length_of_any_production' f p); intros
        end;
        repeat match goal with
                 | [ H : ?x = ?x |- _ ] => clear H
                 | [ H : ?x = _ :> length_result, H' : context[?x] |- _ ] => rewrite H in H'
                 | _ => exfalso; discriminate
                 | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
                 | _ => progress subst
                 | [ H : forall n, same_length _ = same_length n -> _ |- _ ] => specialize (H _ eq_refl)
                 | _ => progress rewrite ?(@take_length _ string_stringlike _), ?(@drop_length _ string_stringlike _), ?substring_length, ?Plus.plus_0_r, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.add_sub
                 | [ |- context[min ?x (?y + ?z) - ?z] ] => rewrite <- (@NPeano.Nat.sub_min_distr_r x (y + z) z)
                 | [ |- context[min (?x - ?y) ?x] ] => rewrite (@Min.min_l (x - y) x) by (clear; omega)
                 | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
                 | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
                 | [ H : parse_of _ _ _ |- _ ] => eapply H_f in H; [ | eassumption.. ]
                 | _ => apply Min.min_case_strong; omega
               end. } }
Qed.

Lemma has_only_terminals_parse_of_length (G : grammar Ascii.ascii) {n}
      nt
      (H : length_of_any G nt = same_length n)
      str
      (p : parse_of G str (Lookup G nt))
: String.length str = n.
Proof.
  unfold length_of_any, length_of_any_nt in H.
  revert n nt H str p.
  match goal with
    | [ |- forall a b, Fix ?wf _ _ ?x _ = _ -> _ ]
      => induction (wf x)
  end.
  intros ? ?.
  rewrite Fix1_eq by apply length_of_any_nt_step_ext.
  unfold length_of_any_nt_step at 1; simpl.
  edestruct dec; simpl;
  [
  | solve [ intros; discriminate ] ].
  generalize dependent (G nt).
  intros.
  unfold length_of_any_productions' in *.
  let p := match goal with H : parse_of _ _ _ |- _ => constr:H end in
  let H := fresh in
  rename p into H;
    induction H; simpl in *.
  { match goal with
      | [ H : context[length_of_any_production' ?f ?p] |- _ ] => revert H; case_eq (length_of_any_production' f p); intros
    end;
    repeat match goal with
             | [ H' : rdp_list_is_valid_nonterminal ?x ?nt = true,
                      H : forall y, rdp_list_nonterminals_listT_R y ?x -> _ |- _ ]
               => specialize (fun nt' str0 n' H0 => H _ (@rdp_list_remove_nonterminal_dec _ nt H') n' nt' H0 str0)
             | [ H : length_of_any_production' _ _ = same_length _ |- _ ] => eapply has_only_terminals_parse_of_production_length in H; [ | eassumption.. ]
             | _ => reflexivity
             | _ => discriminate
             | _ => progress subst
             | [ H : length_of_any_productions'_f _ _ = same_length _ |- _ ] => apply length_of_any_productions'_f_same_length in H
             | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ \/ _ |- _ ] => destruct H; [ (discriminate || congruence) | ]
             | [ H : _ \/ _ |- _ ] => destruct H; [ | (discriminate || congruence) ]
             | [ H : ?x = same_length _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : fold_right length_of_any_productions'_f _ _ = same_length _ |- _ ] => apply length_of_any_productions'_f_same_length_fold_right in H
           end. }
  { edestruct (_ : productions _).
    { match goal with
        | [ H : parse_of _ _ [] |- _ ] => inversion H
      end. }
    { repeat match goal with
               | _ => progress simpl in *
               | [ H : length_of_any_productions'_f _ _ = same_length _ |- _ ] => apply length_of_any_productions'_f_same_length in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : fold_right length_of_any_productions'_f _ _ = same_length _ |- _ ] => apply length_of_any_productions'_f_same_length_fold_right in H
               | [ H : fold_right length_of_any_productions'_f _ _ = same_length _ -> _ |- _ ]
                 => specialize (fun H' => H (proj2 length_of_any_productions'_f_same_length_fold_right H'))
               | _ => progress eauto
             end. } }
Qed.
