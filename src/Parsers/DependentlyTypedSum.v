(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.DependentlyTyped.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
Require Import Parsers.DependentlyTypedOption.
Require Import Common Common.ilist Common.Wf Common.Le Common.Equality.

Start Profiling.

Set Implicit Arguments.

Local Close Scope nat_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context (CharType : Type)
          (String : string_like CharType)
          (G : grammar CharType).
  Context {leaves_extra_data : @parser_dependent_types_extra_dataT _ String G}.
  Context (remove_nonterminal_name_1
           : forall ls ps ps',
               is_valid_nonterminal_name (remove_nonterminal_name ls ps) ps' = true
               -> is_valid_nonterminal_name ls ps' = true)
          (remove_nonterminal_name_2
           : forall ls ps ps',
               is_valid_nonterminal_name (remove_nonterminal_name ls ps) ps' = false
               <-> is_valid_nonterminal_name ls ps' = false \/ ps = ps').
  Variable gen_state : forall str0 valid g s, split_stateT str0 valid g s.

  Variable top_methods' : @parser_computational_dataT' _ String _.
  Definition leaf_methods' : @parser_computational_dataT' _ String _
    := @methods' _ _ (@methods _ _ (@stypes _ _ (@types _ _ _ leaves_extra_data))).

  (** some helper lemmas to help Coq with inference *)
  Hint Unfold compose : dtp_sum_db.
  Hint Extern 1 => apply split_string_for_production_correct' : dtp_sum_db.

  Local Ltac t_sum' :=
    idtac;
    match goal with
      | _ => progress simpl
      | _ => progress intros
      | _ => progress destruct_head' @StringWithSplitState
      | _ => progress destruct_head' sum
      | [ |- Forall _ (map _ _) ] => apply Forall_map
      | _ => progress autounfold with dtp_sum_db in *
      | _ => solve [ eauto with dtp_sum_db ]
    end.

  Local Ltac t_sum := repeat t_sum'.

  Local Instance sum_methods' : @parser_computational_dataT' _ String premethods
    := { split_stateT str0 valid g s
         := @split_stateT _ _ _ top_methods' str0 valid g s
            + @split_stateT _ _ _ leaf_methods' str0 valid g s;

         split_string_for_production str0 valid it its s
         := match state_val s with
              | inl st
                => map (fun s1s2 =>
                          (lift_StringWithSplitState (fst s1s2) (@inl _ _),
                           lift_StringWithSplitState (snd s1s2) (@inl _ _)))
                       (@split_string_for_production _ _ _ top_methods' str0 valid it its {| string_val := string_val s ; state_val := st |})
              | inr st
                => map (fun s1s2 =>
                          (lift_StringWithSplitState (fst s1s2) (@inr _ _),
                           lift_StringWithSplitState (snd s1s2) (@inr _ _)))
                       (@split_string_for_production _ _ _ leaf_methods' str0 valid it its {| string_val := string_val s ; state_val := st |})
            end }.
  Proof. clear; abstract t_sum. Defined.

  Definition top_methods : @parser_computational_dataT _ String
    := {| DependentlyTyped.methods' := top_methods' |}.
  Definition leaf_methods : @parser_computational_dataT _ String
    := @methods _ _ (@stypes _ _ (@types _ _ _ leaves_extra_data)).

  Variable top_prestrdata : @parser_computational_prestrdataT _ String G top_methods option.
  Definition leaf_strdata : @parser_computational_strdataT _ String G leaf_methods
    := @strdata _ _ _ leaves_extra_data.

  Local Instance sum_methods : parser_computational_dataT := { methods' := sum_methods' }.

  Definition functor_cross_sum {A A' B B'} (f : A -> option A') (g : B -> B') (default : B') (x : sum A B) : sum A' B' :=
    match x with
      | inl a => match f a with
                   | Some a' => inl a'
                   | None => inr default
                 end
      | inr b => inr (g b)
    end.

  Definition sum_rect_str {A B} {P : StringWithSplitState String (fun s => A s + B s) -> Type}
             (f : forall x : StringWithSplitState String A, P (lift_StringWithSplitState x (@inl _ _)))
             (g : forall x : StringWithSplitState String B, P (lift_StringWithSplitState x (@inr _ _)))
             x
  : P x
    := match x return P x with
         | {| string_val := s ; state_val := inl st |}
           => f {| string_val := s ; state_val := st |}
         | {| string_val := s ; state_val := inr st |}
           => g {| string_val := s ; state_val := st |}
       end.

  Local Instance sum_prestrdata : @parser_computational_prestrdataT _ String G sum_methods idM
    := { prelower_nonterminal_name_state str0 valid nonterminal_name str
         := functor_cross_sum
              (@prelower_nonterminal_name_state _ _ _ _ _ top_prestrdata _ _ _ _)
              (@lower_nonterminal_name_state _ _ _ _ leaf_strdata _ _ _ _)
              (gen_state _ _ _ _);
         prelower_string_head str0 valid prod prods str
         := functor_cross_sum
              (@prelower_string_head _ _ _ _ _ top_prestrdata _ _ _ _ _)
              (@lower_string_head _ _ _ _ leaf_strdata _ _ _ _ _)
              (gen_state _ _ _ _);
         prelower_string_tail str0 valid prod prods str
         := functor_cross_sum
              (@prelower_string_tail _ _ _ _ _ top_prestrdata _ _ _ _ _)
              (@lower_string_tail _ _ _ _ leaf_strdata _ _ _ _ _)
              (gen_state _ _ _ _);
         prelift_lookup_nonterminal_name_state_lt str0 valid nonterminal_name str pf
         := functor_cross_sum
              (@prelift_lookup_nonterminal_name_state_lt _ _ _ _ _ top_prestrdata _ _ _ _ pf)
              (@lift_lookup_nonterminal_name_state_lt _ _ _ _ leaf_strdata _ _ _ _ pf)
              (gen_state _ _ _ _);
         prelift_lookup_nonterminal_name_state_eq str0 valid nonterminal_name str pf
         := functor_cross_sum
              (@prelift_lookup_nonterminal_name_state_eq _ _ _ _ _ top_prestrdata _ _ _ _ pf)
              (@lift_lookup_nonterminal_name_state_eq _ _ _ _ leaf_strdata _ _ _ _ pf)
              (gen_state _ _ _ _) }.

  Local Instance sum_strdata : @parser_computational_strdataT _ String G sum_methods := sum_prestrdata.

  Context (top_stypes' : @parser_dependent_types_success_dataT' _ String top_methods).
  Definition top_stypes : @parser_dependent_types_success_dataT _ String
    := {| stypes' := top_stypes' |}.
  Context (top_ftypes' : @parser_dependent_types_failure_dataT' _ String top_stypes).
  Definition leaf_stypes' : @parser_dependent_types_success_dataT' _ String leaf_methods
    := @stypes' _ _ (@stypes _ _ (@types _ _ _ leaves_extra_data)).
  Definition leaf_ftypes' : @parser_dependent_types_failure_dataT' _ String _
    := @ftypes' _ _ (@types _ _ _ leaves_extra_data).
  Definition leaf_stypes : @parser_dependent_types_success_dataT _ String
    := @stypes _ _ (@types _ _ _ leaves_extra_data).
  Definition top_types : @parser_dependent_types_dataT _ String
    := {| ftypes' := top_ftypes' |}.
  Definition leaf_types : @parser_dependent_types_dataT _ String
    := @types _ _ _ leaves_extra_data.

  Local Instance sum_stypes' : @parser_dependent_types_success_dataT' _ String sum_methods
    := { T_nonterminal_name_success str0 valid name
         := sum_rect_str
              (@T_nonterminal_name_success _ _ _ top_stypes' _ _ _)
              (@T_nonterminal_name_success _ _ _ leaf_stypes' _ _ _);
         T_item_success str0 valid it
         := sum_rect_str
              (@T_item_success _ _ _ top_stypes' _ _ _)
              (@T_item_success _ _ _ leaf_stypes' _ _ _);
         T_production_success str0 valid prod
         := sum_rect_str
              (@T_production_success _ _ _ top_stypes' _ _ _)
              (@T_production_success _ _ _ leaf_stypes' _ _ _);
         T_productions_success str0 valid prods
         := sum_rect_str
              (@T_productions_success _ _ _ top_stypes' _ _ _)
              (@T_productions_success _ _ _ leaf_stypes' _ _ _) }.
  Local Instance sum_stypes : @parser_dependent_types_success_dataT _ String
    := {| stypes' := sum_stypes' |}.
  Local Instance sum_ftypes' : @parser_dependent_types_failure_dataT' _ String sum_stypes
    := { T_nonterminal_name_failure str0 valid name
         := sum_rect_str
              (@T_nonterminal_name_failure _ _ _ top_ftypes' _ _ _)
              (@T_nonterminal_name_failure _ _ _ leaf_ftypes' _ _ _);
         T_item_failure str0 valid it
         := sum_rect_str
              (@T_item_failure _ _ _ top_ftypes' _ _ _)
              (@T_item_failure _ _ _ leaf_ftypes' _ _ _);
         T_production_failure str0 valid prod
         := sum_rect_str
              (@T_production_failure _ _ _ top_ftypes' _ _ _)
              (@T_production_failure _ _ _ leaf_ftypes' _ _ _);
         T_productions_failure str0 valid prods
         := sum_rect_str
              (@T_productions_failure _ _ _ top_ftypes' _ _ _)
              (@T_productions_failure _ _ _ leaf_ftypes' _ _ _) }.
  Local Instance sum_types : @parser_dependent_types_dataT _ String
    := { ftypes' := sum_ftypes' }.

  Context (top_success_data' : @parser_dependent_types_extra_success_dataT' _ String _ (option_stypes top_stypes') (option_strdata top_prestrdata)).
  Definition leaf_success_data' : @parser_dependent_types_extra_success_dataT' _ String _ (@stypes _ _ (@types _ _ _ leaves_extra_data)) _
    := @extra_success_data _ _ _ leaves_extra_data.

  Local Notation eta s := {| string_val := string_val s ; state_val := state_val s |}.
  Local Notation etas s := (lift_StringWithSplitState s Some).

  Local Ltac t_impossible :=
    repeat match goal with
             | _ => intro
             | [ H : False |- _ ] => destruct H
             | _ => progress subst
             | _ => progress simpl in *
             | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H
             | _ => progress destruct_head ex
             | _ => progress destruct_head and
             | _ => progress destruct_head prod
             | [ H : (_, _) = (_, _) |- _ ] => apply path_prod' in H
           end.

  Section impossible.
    Context {A A' B B'}
            {s0s1 : StringWithSplitState String (fun s => A s + B s) * StringWithSplitState String (fun s => A' s + B' s)}.
    Local Notation discr_T refl refr s0s1
      := (match (refl : unit + unit), (refr : unit + unit), state_val (fst s0s1), state_val (snd s0s1) with
            | inr _, _, inr _, _ => True
            | _, inr _, _, inr _ => True
            | inl _, _, inl _, _ => True
            | _, inl _, _, inl _ => True
            | _, _, _, _ => False
          end) (only parsing).
    Local Notation retT s0s1 f g ls
      := (~(In s0s1
               (map
                  (fun s1s2 =>
                     (lift_StringWithSplitState (fst s1s2) f,
                      lift_StringWithSplitState (snd s1s2) g))
                  ls))) (only parsing).

    Lemma impossible_in_str_ll {ls} (H : discr_T (inr tt) (inr tt) s0s1)
    : retT s0s1 (@inl _ _) (@inl _ _) ls.
    Proof. t_impossible. Qed.

    Lemma impossible_in_str_lr {ls} (H : discr_T (inr tt) (inl tt) s0s1)
    : retT s0s1 (@inl _ _) (@inr _ _) ls.
    Proof. t_impossible. Qed.

    Lemma impossible_in_str_rl {ls} (H : discr_T (inl tt) (inr tt) s0s1)
    : retT s0s1 (@inr _ _) (@inl _ _) ls.
    Proof. t_impossible. Qed.

    Lemma impossible_in_str_rr {ls} (H : discr_T (inl tt) (inl tt) s0s1)
    : retT s0s1 (@inr _ _) (@inr _ _) ls.
    Proof. t_impossible. Qed.
  End impossible.

  Local Obligation Tactic :=
    simpl;
    try (intros;
         solve [ repeat intro; exact I
               | assumption
               | apply Some_injective; assumption
               | apply inl_injective; assumption
               | apply inr_injective; assumption
               | simpl;
                 match goal with | [ |- _ = _ ] => idtac end;
                 rewrite !map_map; apply map_ext; simpl;
                 intros [ [? ?] [? ?] ]; reflexivity
               | exfalso; eapply impossible_in_str_ll; eauto; simpl; eauto
               | exfalso; eapply impossible_in_str_lr; eauto; simpl; eauto
               | exfalso; eapply impossible_in_str_rl; eauto; simpl; eauto
               | exfalso; eapply impossible_in_str_rr; eauto; simpl; eauto ]).

  Global Program Instance sum_extra_success_data
         lift_success_cross
         lift_prods_success_head_cross lift_prods_success_tail_cross
         lift_parse_nonterminal_name_success_lt_cross
         lift_parse_nonterminal_name_success_eq_cross
  : @parser_dependent_types_extra_success_dataT' _ String G sum_stypes sum_strdata
    := { lift_success str0 valid nonterminal_name
         := sum_rect_str
              (fun str => impl_sum_match_match_option
                            (@lift_success _ _ _ _ _ top_success_data' _ _ _ (etas str))
                            (lift_success_cross str0 valid nonterminal_name str))
              (fun str => @lift_success _ _ _ _ _ leaf_success_data' _ _ _ (eta str));
         parse_terminal_success str0 valid ch
         := sum_rect_str
              (fun str => @parse_terminal_success _ _ _ _ _ top_success_data' _ _ _ (etas str))
              (fun str => @parse_terminal_success _ _ _ _ _ leaf_success_data' _ _ _ (eta str));
         parse_empty_success str0 valid
         := sum_rect_str
              (fun str => @parse_empty_success _ _ _ _ _ top_success_data' _ _ (etas str))
              (fun str => @parse_empty_success _ _ _ _ _ leaf_success_data' _ _ (eta str));
         cons_success str0 valid it its
         := sum_rect_str
              (fun s1 =>
                 sum_rect_str
                   (fun s2 =>
                      sum_rect_str
                        (fun str pf H' H'' =>
                           @cons_success
                             _ _ _ _ _ top_success_data' _ _ _ _ (etas s1) (etas s2) (etas str) pf H'
                             (in_lift_pair_StringWithSplitState_iff_injective
                                (lift := fun _ => Some) (lift' := fun _ => Some)
                                _))
                        _)
                   (fun s2 => sum_rect_str _ _))
              (fun s1 =>
                 sum_rect_str
                   (fun s2 => sum_rect_str _ _)
                   (fun s2 =>
                      sum_rect_str
                        _
                        (fun str pf H' H'' =>
                           @cons_success
                             _ _ _ _ _ leaf_success_data' _ _ _ _ (eta s1) (eta s2) (eta str) pf H'
                             (in_lift_pair_StringWithSplitState_iff_injective
                                (lift := fun _ => Some) (lift' := fun _ => Some)
                                _))));
         lift_prods_success_head str0 valid prod prods
         := sum_rect_str
              (fun str => impl_sum_match_match_option
                            (@lift_prods_success_head _ _ _ _ _ top_success_data' _ _ _ _ (etas str))
                            (lift_prods_success_head_cross str0 valid prod prods str))
              (fun str => @lift_prods_success_head _ _ _ _ _ leaf_success_data' _ _ _ _ (eta str));
         lift_prods_success_tail str0 valid prod prods
         := sum_rect_str
              (fun str => impl_sum_match_match_option
                            (@lift_prods_success_tail _ _ _ _ _ top_success_data' _ _ _ _ (etas str))
                            (lift_prods_success_tail_cross str0 valid prod prods str))
              (fun str => @lift_prods_success_tail _ _ _ _ _ leaf_success_data' _ _ _ _ (eta str));
         lift_parse_nonterminal_name_success_lt str0 valid nonterminal_name
         := sum_rect_str
              (fun str pf => impl_sum_match_match_option
                               (@lift_parse_nonterminal_name_success_lt _ _ _ _ _ top_success_data' _ _ _ (etas str) pf)
                                 (lift_parse_nonterminal_name_success_lt_cross str0 valid nonterminal_name str pf))
              (fun str => @lift_parse_nonterminal_name_success_lt _ _ _ _ _ leaf_success_data' _ _ _ (eta str));
         lift_parse_nonterminal_name_success_eq str0 valid nonterminal_name
         := sum_rect_str
              (fun str pf H => impl_sum_match_match_option
                               (@lift_parse_nonterminal_name_success_eq _ _ _ _ _ top_success_data' _ _ _ (etas str) pf H)
                               (lift_parse_nonterminal_name_success_eq_cross str0 valid nonterminal_name str pf H))
              (fun str => @lift_parse_nonterminal_name_success_eq _ _ _ _ _ leaf_success_data' _ _ _ (eta str))
       }.
  Next Obligation.
  Proof.
    simpl.
    intros.
    rewrite !map_map; simpl.
    apply in_map_iff; eexists (_, _); split; [ reflexivity | ].
    refine (in_lift_pair_StringWithSplitState_iff_injective (lift := fun _ => inl) (lift' := fun _ => inl) _); [ | | pre_eassumption; assumption ].
    { intros; eapply inl_injective; eassumption. }
    { intros; eapply inl_injective; eassumption. }
  Defined.
  Next Obligation.
  Proof.
    simpl.
    intros.
    apply in_map_iff; eexists (eta s1, eta s2); split; [ reflexivity | ].
    refine (in_lift_pair_StringWithSplitState_iff_injective (lift := fun _ => inr) (lift' := fun _ => inr) _); [ | | pre_eassumption; assumption ].
    { intros; eapply inr_injective; eassumption. }
    { intros; eapply inr_injective; eassumption. }
  Defined.

  Context (top_failure_data' : @parser_dependent_types_extra_failure_dataT' _ String G (option_types (@ftypes' _ _ top_types)) (option_strdata top_prestrdata)).

  Definition leaf_failure_data' : @parser_dependent_types_extra_failure_dataT' _ String _ (@types _ _ _ leaves_extra_data) _
    := @extra_failure_data _ _ _ leaves_extra_data.

  Global Program Instance sum_extra_failure_data
         lift_failure_cross
         lift_prods_failure_cross0 lift_prods_failure_cross1
         lift_parse_nonterminal_name_failure_lt_cross
         lift_parse_nonterminal_name_failure_eq_cross
  : @parser_dependent_types_extra_failure_dataT' _ String G sum_types sum_strdata
    := { lift_failure str0 valid nonterminal_name
         := sum_rect_str
              (fun str => impl_sum_match_match_option
                            (@lift_failure _ _ _ _ _ top_failure_data' _ _ _ (etas str))
                            (lift_failure_cross str0 valid nonterminal_name str))
              (fun str => @lift_failure _ _ _ _ _ leaf_failure_data' _ _ _ (eta str));
       parse_terminal_failure str0 valid ch
         := sum_rect_str
              (fun str => @parse_terminal_failure _ _ _ _ _ top_failure_data' _ _ _ (etas str))
              (fun str => @parse_terminal_failure _ _ _ _ _ leaf_failure_data' _ _ _ (eta str));
         parse_empty_failure str0 valid
         := sum_rect_str
              (fun str => @parse_empty_failure _ _ _ _ _ top_failure_data' _ _ (etas str))
              (fun str => @parse_empty_failure _ _ _ _ _ leaf_failure_data' _ _ (eta str));
         fail_parse_nil_productions str0 valid
         := sum_rect_str
              (fun str => @fail_parse_nil_productions _ _ _ _ _ top_failure_data' _ _ (etas str))
              (fun str => @fail_parse_nil_productions _ _ _ _ _ leaf_failure_data' _ _ (eta str));
         lift_prods_failure str0 valid prod prods
         := sum_rect_str
              (fun str => impl_sum_match_match_option
                            (fun H0 =>
                               impl_sum_match_match_option
                                 (@lift_prods_failure _ _ _ _ _ top_failure_data' str0 valid prod prods (etas str) H0)
                                 (lift_prods_failure_cross0 str0 valid prod prods str H0))
                            (lift_prods_failure_cross1 str0 valid prod prods str))
              (fun str => @lift_prods_failure _ _ _ _ _ leaf_failure_data' _ _ _ _ (eta str));

         H_prod_split str0 valid it its
         := sum_rect_str
              (fun str pf => (@H_prod_split _ _ _ _ _ top_failure_data' _ _ _ _ (etas str) pf)
                               ∘ (fun H => eq_rect _ _ H _ _))
              (fun str pf => (@H_prod_split _ _ _ _ _ leaf_failure_data' _ _ _ _ (eta str) pf)
                               ∘ (fun H => eq_rect _ _ H _ _));

         lift_parse_nonterminal_name_failure_lt str0 valid nonterminal_name
         := sum_rect_str
              (fun str pf => impl_sum_match_match_option
                               (@lift_parse_nonterminal_name_failure_lt _ _ _ _ _ top_failure_data' _ _ _ (etas str) pf)
                                 (lift_parse_nonterminal_name_failure_lt_cross str0 valid nonterminal_name str pf))
              (fun str => @lift_parse_nonterminal_name_failure_lt _ _ _ _ _ leaf_failure_data' _ _ _ (eta str));
         lift_parse_nonterminal_name_failure_eq str0 valid nonterminal_name
         := sum_rect_str
              (fun str pf => impl_sum_match_match_option
                               (@lift_parse_nonterminal_name_failure_eq _ _ _ _ _ top_failure_data' _ _ _ (etas str) pf)
                               (lift_parse_nonterminal_name_failure_eq_cross str0 valid nonterminal_name str pf))
              (fun str => @lift_parse_nonterminal_name_failure_eq _ _ _ _ _ leaf_failure_data' _ _ _ (eta str));
         elim_parse_nonterminal_name_failure str0 valid nonterminal_name
         := sum_rect_str
              (fun str => @elim_parse_nonterminal_name_failure _ _ _ _ _ top_failure_data' _ _ _ (etas str))
              (fun str => @elim_parse_nonterminal_name_failure _ _ _ _ _ leaf_failure_data' _ _ _ (eta str))

         }.

  Definition sum_extra_data
             lift_success_cross
             lift_prods_success_head_cross lift_prods_success_tail_cross
             lift_parse_nonterminal_name_success_lt_cross
             lift_parse_nonterminal_name_success_eq_cross
             lift_failure_cross
             lift_prods_failure_cross0 lift_prods_failure_cross1
             lift_parse_nonterminal_name_failure_lt_cross
             lift_parse_nonterminal_name_failure_eq_cross
  : @parser_dependent_types_extra_dataT _ String G
    := {| DependentlyTyped.types := sum_types;
          DependentlyTyped.strdata := sum_strdata;
          DependentlyTyped.extra_success_data
          := sum_extra_success_data
               lift_success_cross
               lift_prods_success_head_cross lift_prods_success_tail_cross
               lift_parse_nonterminal_name_success_lt_cross
               lift_parse_nonterminal_name_success_eq_cross;
          DependentlyTyped.extra_failure_data
          := sum_extra_failure_data
               lift_failure_cross
               lift_prods_failure_cross0 lift_prods_failure_cross1
               lift_parse_nonterminal_name_failure_lt_cross
               lift_parse_nonterminal_name_failure_eq_cross|}.
End recursive_descent_parser.
