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
  Context (leaf_predata : parser_computational_predataT).
  Local Instance leaf_types_data : @parser_computational_types_dataT _ String
    := {| predata := leaf_predata;
          split_stateT str0 valid g str := True |}.
  Context (leaf_methods' : @parser_computational_dataT' _ String leaf_types_data).
  Local Instance leaf_methods : @parser_computational_dataT _ String
    := {| methods' := leaf_methods' |}.
  Context (leaf_stypes' : @parser_dependent_types_success_dataT' _ String leaf_methods).
  Local Instance leaf_stypes : @parser_dependent_types_success_dataT _ String
    := {| stypes' := leaf_stypes' |}.
  Context (leaf_ftypes' : @parser_dependent_types_failure_dataT' _ String leaf_stypes).
  Local Instance leaf_types : @parser_dependent_types_dataT _ String
    := {| ftypes' := leaf_ftypes' |}.
  Context (leaf_strdata : @parser_computational_strdataT _ String G leaf_methods).
  Context (leaf_extra_success_data : @parser_dependent_types_extra_success_dataT' _ String G leaf_stypes leaf_strdata).
  Context (leaf_extra_failure_data : @parser_dependent_types_extra_failure_dataT' _ String G leaf_types leaf_strdata).

  Local Instance leaf_extra_data : @parser_dependent_types_extra_dataT _ String G
    := {| types := leaf_types;
          strdata := leaf_strdata;
          extra_success_data := leaf_extra_success_data;
          extra_failure_data := leaf_extra_failure_data |}.
  Context (remove_nonterminal_name_1
           : forall ls ps ps',
               is_valid_nonterminal_name (remove_nonterminal_name ls ps) ps' = true
               -> is_valid_nonterminal_name ls ps' = true)
          (remove_nonterminal_name_2
           : forall ls ps ps',
               is_valid_nonterminal_name (remove_nonterminal_name ls ps) ps' = false
               <-> is_valid_nonterminal_name ls ps' = false \/ ps = ps').

  Context top_split_stateT
          (top_methods' : @parser_computational_dataT' _ String {| split_stateT := top_split_stateT |}).
  Local Instance top_premethods : @parser_computational_types_dataT _ String
    := {| split_stateT := top_split_stateT |}.

  (** some helper lemmas to help Coq with inference *)
  Hint Unfold compose : dtp_sum_db.
  Hint Extern 1 => refine (@split_string_for_production_correct' _ String leaf_types_data leaf_methods' _ _ _ _ _ _) : dtp_sum_db.
  Hint Extern 1 => refine (@split_string_for_production_correct' _ _ _ _ _ _ _ _ _ _) : dtp_sum_db.

  Local Ltac t_sum' :=
    idtac;
    match goal with
      | _ => progress simpl
      | _ => progress intros
      | _ => progress destruct_head' @StringWithSplitState
      | _ => progress destruct_head' sum
      | _ => progress destruct_head' option
      | [ |- Forall _ (map _ _) ] => apply Forall_map
      | _ => progress autounfold with dtp_sum_db in *
      | _ => solve [ eauto with dtp_sum_db ]
    end.

  Local Ltac t_sum := repeat t_sum'.

  Local Instance sum_types_data' : @parser_computational_types_dataT _ String
    := { split_stateT str0 valid g s
         := option (@split_stateT _ _ top_premethods str0 valid g s) }.

  Local Instance sum_methods' : @parser_computational_dataT' _ String sum_types_data'
    := { split_string_for_production str0 valid it its s
         := match state_val s with
              | Some st
                => map (fun s1s2 =>
                          (lift_StringWithSplitState (fst s1s2) Some,
                           lift_StringWithSplitState (snd s1s2) Some))
                       (@split_string_for_production _ _ _ top_methods' str0 valid it its {| string_val := string_val s ; state_val := st |})
              | None
                => map (fun s1s2 =>
                          (lift_StringWithSplitState (fst s1s2) (fun _ => None),
                           lift_StringWithSplitState (snd s1s2) (fun _ => None)))
                       (@split_string_for_production _ _ _ leaf_methods' str0 valid it its {| string_val := string_val s ; state_val := I |})
            end }.
  Proof. clear; abstract t_sum. Defined.

  Definition top_methods : @parser_computational_dataT _ String
    := {| DependentlyTyped.methods' := top_methods' |}.

  Variable top_prestrdata : @parser_computational_prestrdataT _ String G top_methods option.

  Local Instance sum_methods : parser_computational_dataT := { methods' := sum_methods' }.

  Definition option_rect_str {A} {B : StringWithSplitState String (fun s => option (A s)) -> Type}
             (f : forall x : StringWithSplitState String A, B (lift_StringWithSplitState x (@Some _)))
             (none_case : forall s, B {| string_val := s; state_val := None |})
             (x : StringWithSplitState String (fun s => option (A s)))
  : B x
    := match x return B x with
         | {| string_val := s ; state_val := None |} => none_case s
         | {| string_val := s ; state_val := Some st |}
           => f {| string_val := s ; state_val := st |}
       end.

  (*Definition True_rect_str {B : StringWithSplitState String (fun s => True) -> Type}
             (f : forall s, B (lift_StringWithSplitState x (fun _ => I)))
             (x : StringWithSplitState String (fun s => True))
  : B x
    := match x return B x with
         | {| string_val := s ; state_val := I |} => f {| string_val := s ; state_val := I |}
         | {| string_val := s ; state_val := Some st |}
           => f {| string_val := s ; state_val := st |}
       end.*)

  Local Instance sum_prestrdata : @parser_computational_prestrdataT _ String G sum_methods idM
    := { prelower_nonterminal_name_state str0 valid nonterminal_name str
         := option_bind (@prelower_nonterminal_name_state _ _ _ _ _ top_prestrdata _ _ _ _);
         prelower_string_head str0 valid prod prods str
         := option_bind (@prelower_string_head _ _ _ _ _ top_prestrdata _ _ _ _ _);
         prelower_string_tail str0 valid prod prods str
         := option_bind (@prelower_string_tail _ _ _ _ _ top_prestrdata _ _ _ _ _);
         prelift_lookup_nonterminal_name_state_lt str0 valid nonterminal_name str pf
         := option_bind (@prelift_lookup_nonterminal_name_state_lt _ _ _ _ _ top_prestrdata _ _ _ _ pf);
         prelift_lookup_nonterminal_name_state_eq str0 valid nonterminal_name str pf
         := option_bind (@prelift_lookup_nonterminal_name_state_eq _ _ _ _ _ top_prestrdata _ _ _ _ pf) }.

  Local Instance sum_strdata : @parser_computational_strdataT _ String G sum_methods := sum_prestrdata.

  Local Notation eta s := {| string_val := string_val s ; state_val := state_val s |}.
  Local Notation etas str := (lift_StringWithSplitState str (fun _ => I)).

  Local Instance sum_stypes' : @parser_dependent_types_success_dataT' _ String sum_methods
    := { T_nonterminal_name_success str0 valid name str
         := @T_nonterminal_name_success _ _ _ leaf_stypes' str0 valid name (etas str);
         T_item_success str0 valid it str
         := @T_item_success _ _ _ leaf_stypes' str0 valid it (etas str);
         T_production_success str0 valid prod str
         := @T_production_success _ _ _ leaf_stypes' str0 valid prod (etas str);
         T_productions_success str0 valid prods str
         := @T_productions_success _ _ _ leaf_stypes' str0 valid prods (etas str) }.

  Local Notation Is str := {| string_val := str ; state_val := I |}.
  Local Notation T_failureT FT :=
    (fun str0 valid arg =>
       option_rect_str (fun _ => False)
                       (fun str => FT _ _ _ leaf_ftypes' str0 valid arg (Is str))) (only parsing).
  Local Instance sum_stypes : @parser_dependent_types_success_dataT _ String
    := {| stypes' := sum_stypes' |}.
  Local Instance sum_ftypes' : @parser_dependent_types_failure_dataT' _ String sum_stypes
    := { T_nonterminal_name_failure := T_failureT (@T_nonterminal_name_failure);
         T_item_failure := T_failureT (@T_item_failure);
         T_production_failure := T_failureT (@T_production_failure);
         T_productions_failure := T_failureT (@T_productions_failure) }.
  Local Instance sum_types : @parser_dependent_types_dataT _ String
    := { ftypes' := sum_ftypes' }.

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
      := (match (refl : True + True), (refr : True + True), state_val (fst s0s1), state_val (snd s0s1) with
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

    Lemma impossible_in_str_ll {ls} (H : discr_T (inr I) (inr I) s0s1)
    : retT s0s1 (@inl _ _) (@inl _ _) ls.
    Proof. t_impossible. Qed.

    Lemma impossible_in_str_lr {ls} (H : discr_T (inr I) (inl I) s0s1)
    : retT s0s1 (@inl _ _) (@inr _ _) ls.
    Proof. t_impossible. Qed.

    Lemma impossible_in_str_rl {ls} (H : discr_T (inl I) (inr I) s0s1)
    : retT s0s1 (@inr _ _) (@inl _ _) ls.
    Proof. t_impossible. Qed.

    Lemma impossible_in_str_rr {ls} (H : discr_T (inl I) (inl I) s0s1)
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
                 intros [ [? ?] [? ?] ]; reflexivity ]). (*
               | exfalso; eapply impossible_in_str_ll; eauto; simpl; eauto
               | exfalso; eapply impossible_in_str_lr; eauto; simpl; eauto
               | exfalso; eapply impossible_in_str_rl; eauto; simpl; eauto
               | exfalso; eapply impossible_in_str_rr; eauto; simpl; eauto ]).*)

  Definition liftA_str_tt {f g : StringWithSplitState String (fun _ => True) -> Type}
             {s1 s2 t0 t1}
             (F : f {| string_val := string_val s1 ; state_val := t0 |}
                  -> g {| string_val := string_val s2 ; state_val := t1 |})
  : f s1 -> g s2.
  Proof.
    destruct s1 as [ ? [] ], s2 as [ ? [] ], t0, t1. exact F.
  Defined.

  Global Program Instance sum_extra_success_data
         (*lift_success_cross
         lift_prods_success_head_cross lift_prods_success_tail_cross
         lift_parse_nonterminal_name_success_lt_cross
         lift_parse_nonterminal_name_success_eq_cross*)
  : @parser_dependent_types_extra_success_dataT' _ String G sum_stypes sum_strdata
    := { lift_success str0 valid nonterminal_name str
         := liftA_str_tt (@lift_success _ _ _ _ _ leaf_extra_success_data _ _ _ (etas str));
         parse_terminal_success str0 valid ch str
         := @parse_terminal_success _ _ _ _ _ leaf_extra_success_data _ _ _ (etas str);
         parse_empty_success str0 valid str
         := @parse_empty_success _ _ _ _ _ leaf_extra_success_data _ _ (etas str);
         cons_success str0 valid it its
         := option_rect_str
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
:= option_rect_str _ _ } .

  Next Obligation.
    simpl.
    refine (@cons_success _ _ _ _ _ leaf_extra_success_data str0 valid it its _ _ _ _ _ _ _ _).
simpl in *.
 (etas s1) (etas s2) (etas str)).
@cons_success _ _ _ _ _ leaf_extra_success_data _ _ _ _ (etas s1) (etas s2) (etas str) }.
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
