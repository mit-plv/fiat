(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Definition String_with_no_state {CharType} (String : string_like CharType) := StringWithSplitState String (fun _ => True).

Definition default_String_with_no_state {CharType} (String : string_like CharType) (s : String) : String_with_no_state String
  := {| string_val := s ; state_val := I |}.

Coercion default_string_with_no_state (s : string) : String_with_no_state string_stringlike
  := default_String_with_no_state string_stringlike s.

Identity Coercion unfold_String_with_no_state : String_with_no_state >-> StringWithSplitState.

Section brute_force_splitter.
  Fixpoint make_all_single_splits' (str : string) : list (String_with_no_state string_stringlike * String_with_no_state string_stringlike)
    := ((""%string : String_with_no_state string_stringlike),
        (str : String_with_no_state string_stringlike))
         ::(match str with
              | ""%string => nil
              | String.String ch str' =>
                map (fun p : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                     => ((String.String ch (string_val (fst p)) : String_with_no_state string_stringlike),
                         snd p))
                    (make_all_single_splits' str')
            end).

  Definition make_all_single_splits (str : String_with_no_state string_stringlike)
    := make_all_single_splits' (string_val str).

  Lemma make_all_single_splits_correct_eq (str : String_with_no_state string_stringlike)
  : List.Forall (fun strs : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                 => string_val (fst strs) ++ string_val (snd strs) = string_val str)%string (make_all_single_splits str).
  Proof.
    destruct str as [str ?].
    induction str; simpl in *; constructor; auto.
    apply Forall_map.
    unfold compose; simpl in *.
    revert IHstr; apply Forall_impl; intros.
    subst; trivial.
  Qed.

  Local Opaque string_dec.
  Lemma make_all_single_splits_correct_seq (str : String_with_no_state string_stringlike)
  : List.Forall (fun strs : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                 => (fst strs ++ snd strs =s str) = true)%string_like (make_all_single_splits str).
  Proof.
    destruct str as [str ?].
    induction str; simpl; constructor; simpl; auto.
    { rewrite string_dec_refl; reflexivity. }
    { apply Forall_map.
      unfold compose; simpl.
      revert IHstr; apply Forall_impl; intros.
      match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end.
      simpl in *; subst; rewrite string_dec_refl; reflexivity. }
  Qed.

  Lemma make_all_single_splits_correct_str_le (str : String_with_no_state string_stringlike)
  : List.Forall (fun strs : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                 => fst strs ≤s str /\ snd strs ≤s str)%string (make_all_single_splits str).
  Proof.
    generalize (make_all_single_splits_correct_eq str).
    apply Forall_impl.
    destruct str as [str ?]; simpl.
    intros; subst; split;
    first [ apply @str_le1_append
          | apply @str_le2_append ].
  Qed.

  Local Hint Resolve NPeano.Nat.lt_lt_add_l NPeano.Nat.lt_lt_add_r NPeano.Nat.lt_add_pos_r NPeano.Nat.lt_add_pos_l : arith.
  Local Hint Resolve str_le1_append str_le2_append.

  Context (G : grammar Ascii.ascii).

  Global Instance brute_force_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ G)
    := { split_string_for_production str0 valid it its := make_all_single_splits;
         split_string_for_production_correct str0 valid it its := make_all_single_splits_correct_seq }.

  Global Instance brute_force_data : @boolean_parser_dataT _ string_stringlike
    := { predata := @rdp_list_predata _ G;
         split_stateT str := True;
         split_string_for_production it its := make_all_single_splits;
         split_string_for_production_correct it its := make_all_single_splits_correct_seq }.

  Lemma make_all_single_splits_complete_helper
  : forall (str : String_with_no_state string_stringlike)
           (s1s2 : String_with_no_state string_stringlike * String_with_no_state string_stringlike),
      fst s1s2 ++ snd s1s2 =s str -> In s1s2 (make_all_single_splits str).
  Proof.
    intros [str [] ] [ [s1 [] ] [s2 [] ] ] H.
    apply bool_eq_correct in H; simpl in *; subst.
    revert s2.
    induction s1; simpl in *.
    { intros.
      destruct s2; left; simpl; reflexivity. }
    { intros; right.
      refine (@in_map _ _ _ _ ({| string_val := s1 |}, {| string_val := s2 |}) _).
      apply IHs1. }
  Qed.

  Lemma make_all_single_splits_complete
  : forall G str0 valid str pf it its, @split_list_completeT _ string_stringlike G brute_force_data str0 valid str pf (@make_all_single_splits str) it its.
  Proof.
    intros; hnf.
    intros [ [s1 s2] [ [ p1 p2 ] p3 ] ].
    exists ({| string_val := s1 ; state_val := I |}, {| string_val := s2 ; state_val := I |}).
    abstract (
        repeat split; try assumption;
        apply make_all_single_splits_complete_helper;
        assumption
      ).
  Defined.

  Global Instance brute_force_cdata : @boolean_parser_completeness_dataT' _ _ G brute_force_data
    := { remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2;
         split_string_for_production_complete str0 valid str pf it its
         := ForallT_all (fun _ => Forall_tails_all (fun prod => _)) }.
  Proof.
    destruct prod; try solve [ constructor ].
    apply (@make_all_single_splits_complete G str0 valid str pf).
  Defined.
End brute_force_splitter.
