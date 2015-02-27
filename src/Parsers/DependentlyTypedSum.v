(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.DependentlyTyped.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
Require Import Common Common.Wf Common.Le Common.Equality.

(* This requires the profiling module.  *)
(* Start Profiling. *)

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
  Definition split_string_for_production_correct'
             H0 H1 str0 valid it its str st
    := @split_string_for_production_correct CharType String H0 H1 str0 valid it its {| string_val := str ; state_val := st |}.

  Hint Unfold compose : dtp_sum_db.
  Hint Extern 1 => refine (@split_string_for_production_correct' leaf_types_data leaf_methods' _ _ _ _ _ _) : dtp_sum_db.
  Hint Extern 1 => refine (@split_string_for_production_correct' _ _ _ _ _ _ _ _) : dtp_sum_db.

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

  Local Notation tts str := {| string_val := str ; state_val := I |}.
  Local Notation T_failureT FT :=
    (fun str0 valid arg =>
       option_rect_str (fun _ => False)
                       (fun str => FT _ _ _ leaf_ftypes' str0 valid arg (tts str))) (only parsing).
  Local Instance sum_stypes : @parser_dependent_types_success_dataT _ String
    := {| stypes' := sum_stypes' |}.
  Local Instance sum_ftypes' : @parser_dependent_types_failure_dataT' _ String sum_stypes
    := { T_nonterminal_name_failure := T_failureT (@T_nonterminal_name_failure);
         T_item_failure := T_failureT (@T_item_failure);
         T_production_failure := T_failureT (@T_production_failure);
         T_productions_failure := T_failureT (@T_productions_failure) }.
  Local Instance sum_types : @parser_dependent_types_dataT _ String
    := { ftypes' := sum_ftypes' }.

  Definition liftA_str_I {f g : StringWithSplitState String (fun _ => True) -> Type}
             {s1 s2 t0 t1}
             (F : f {| string_val := string_val s1 ; state_val := t0 |}
                  -> g {| string_val := string_val s2 ; state_val := t1 |})
  : f s1 -> g s2.
  Proof.
    destruct s1 as [ ? [] ], s2 as [ ? [] ], t0, t1. exact F.
  Defined.

  Definition liftA2_str_I {f g h : StringWithSplitState String (fun _ => True) -> Type}
             {s1 s2 s3 t0 t1 t2}
             (F : f {| string_val := string_val s1 ; state_val := t0 |}
                  -> g {| string_val := string_val s2 ; state_val := t1 |}
                  -> h {| string_val := string_val s3 ; state_val := t2 |})
  : f s1 -> g s2 -> h s3.
  Proof.
    destruct s1 as [ ? [] ], s2 as [ ? [] ], s3 as [ ? [] ], t0, t1, t2; exact F.
  Defined.

  Global Instance sum_extra_success_data
  : @parser_dependent_types_extra_success_dataT' _ String G sum_stypes sum_strdata
    := { lift_success str0 valid nonterminal_name str
         := liftA_str_I (@lift_success _ _ _ _ _ leaf_extra_success_data _ _ _ (etas str));
         parse_terminal_success str0 valid ch str
         := @parse_terminal_success _ _ _ _ _ leaf_extra_success_data _ _ _ (etas str);
         parse_empty_success str0 valid str
         := @parse_empty_success _ _ _ _ _ leaf_extra_success_data _ _ (etas str);
         cons_success str0 valid it its str s1 s2
         := @cons_success _ _ _ _ _ leaf_extra_success_data _ _ _ _ (etas str) (etas s1) (etas s2);
         lift_prods_success_head str0 valid prod prods str
         := liftA_str_I (@lift_prods_success_head _ _ _ _ _ leaf_extra_success_data _ _ _ _ (etas str));
         lift_prods_success_tail str0 valid prod prods str
         := liftA_str_I (@lift_prods_success_tail _ _ _ _ _ leaf_extra_success_data _ _ _ _ (etas str));
         lift_parse_nonterminal_name_success_lt str0 valid nonterminal_name str pf
         := liftA_str_I (@lift_parse_nonterminal_name_success_lt _ _ _ _ _ leaf_extra_success_data _ _ _ (etas str) pf);
         lift_parse_nonterminal_name_success_eq str0 valid nonterminal_name str pf H
         := liftA_str_I (@lift_parse_nonterminal_name_success_eq _ _ _ _ _ leaf_extra_success_data _ _ _ (etas str) pf H) }.

  Local Obligation Tactic :=
    simpl;
    try (intros;
         solve [ repeat intro; exact I
               | assumption
               | exfalso; assumption ]).

  Global Program Instance sum_extra_failure_data
         lift_failure_cross parse_terminal_failure_cross
         parse_empty_failure_cross
         fail_parse_nil_productions_cross
         lift_prods_failure_cross
         (H_prod_split_cross : forall str0 valid it its (str : StringWithSplitState String (top_split_stateT str0 valid (it :: its : production _))) (pf : str ≤s str0),
                                 @split_string_for_production _ _ _ top_methods' str0 valid it its (eta str) <> nil)
         lift_parse_nonterminal_name_failure_lt_cross
         lift_parse_nonterminal_name_failure_eq_cross
         elim_parse_nonterminal_name_failure_cross
  : @parser_dependent_types_extra_failure_dataT' _ String G sum_types sum_strdata
    := { lift_failure str0 valid nonterminal_name
         := option_rect_str
              (fun str => impl_match_option _ (lift_failure_cross str0 valid nonterminal_name str))
              (fun str => liftA_str_I (@lift_failure _ _ _ _ _ leaf_extra_failure_data _ _ _ (tts str)));
         parse_terminal_failure str0 valid ch
         := option_rect_str
              (parse_terminal_failure_cross str0 valid ch)
              (fun str => @parse_terminal_failure _ _ _ _ _ leaf_extra_failure_data _ _ _ (tts str));
         parse_empty_failure str0 valid
         := option_rect_str
              (parse_empty_failure_cross str0 valid)
              (fun str => @parse_empty_failure _ _ _ _ _ leaf_extra_failure_data _ _ (tts str));
         fail_parse_nil_productions str0 valid
         := option_rect_str
              (fail_parse_nil_productions_cross str0 valid)
              (fun str => @fail_parse_nil_productions _ _ _ _ _ leaf_extra_failure_data _ _ (tts str));
         lift_prods_failure str0 valid prod prods
         := option_rect_str
              (fun str => impl_match_option _ (fun pf1 arg1 => impl_match_option _ (lift_prods_failure_cross str0 valid prod prods str pf1 arg1)))
              (fun str => liftA2_str_I (@lift_prods_failure _ _ _ _ _ leaf_extra_failure_data _ _ _ _ (tts str)));

         H_prod_split str0 valid it its
         := option_rect_str
              (fun str pf => _)
              (fun str pf => (@H_prod_split _ _ _ _ _ leaf_extra_failure_data _ _ _ _ (tts str) pf)
                               ∘ (fun H => eq_rect _ _ H _ _));

         lift_parse_nonterminal_name_failure_lt str0 valid nonterminal_name
         := option_rect_str
              (fun str pf => impl_match_option _ (lift_parse_nonterminal_name_failure_lt_cross str0 valid nonterminal_name str pf))
              (fun str pf => liftA_str_I (@lift_parse_nonterminal_name_failure_lt _ _ _ _ _ leaf_extra_failure_data _ _ _ (tts str) pf));
         lift_parse_nonterminal_name_failure_eq str0 valid nonterminal_name
         := option_rect_str
              (fun str pf => impl_match_option _ (lift_parse_nonterminal_name_failure_eq_cross str0 valid nonterminal_name str pf))
              (fun str pf => liftA_str_I (@lift_parse_nonterminal_name_failure_eq _ _ _ _ _ leaf_extra_failure_data _ _ _ (tts str) pf));
         elim_parse_nonterminal_name_failure str0 valid nonterminal_name
         := option_rect_str
              (fun str => elim_parse_nonterminal_name_failure_cross str0 valid nonterminal_name str)
              (fun str => @elim_parse_nonterminal_name_failure _ _ _ _ _ leaf_extra_failure_data _ _ _ (tts str)) }.
  Next Obligation.
  Proof.
    intros.
    match goal with
      | [ H : fold_right _ _ _ |- _ ] => rewrite !map_map in H
    end.
    match goal with
      | [ H : fold_right _ _ (map _ ?ls), pf : _ |- _ ]
        => assert (ls <> nil) by eauto;
          destruct ls; [ exfalso; eauto | ]
    end.
    simpl in *.
    destruct_head prod.
    destruct_head sum;
      destruct_head prod;
      assumption.
  Qed.
  Next Obligation.
    intros.
    rewrite !map_map; simpl.
    apply map_ext; intro.
    destruct_head prod.
    destruct_head @StringWithSplitState.
    destruct_head True.
    reflexivity.
  Defined.

  Definition sum_extra_data
             lift_failure_cross parse_terminal_failure_cross
             parse_empty_failure_cross
             fail_parse_nil_productions_cross
             lift_prods_failure_cross
             H_prod_split_cross
             lift_parse_nonterminal_name_failure_lt_cross
             lift_parse_nonterminal_name_failure_eq_cross
             elim_parse_nonterminal_name_failure_cross
  : @parser_dependent_types_extra_dataT _ String G
    := {| DependentlyTyped.types := sum_types;
          DependentlyTyped.strdata := sum_strdata;
          DependentlyTyped.extra_success_data := sum_extra_success_data;
          DependentlyTyped.extra_failure_data
          := sum_extra_failure_data
               lift_failure_cross parse_terminal_failure_cross
               parse_empty_failure_cross
               fail_parse_nil_productions_cross
               lift_prods_failure_cross
               H_prod_split_cross
               lift_parse_nonterminal_name_failure_lt_cross
               lift_parse_nonterminal_name_failure_eq_cross
               elim_parse_nonterminal_name_failure_cross |}.
End recursive_descent_parser.
