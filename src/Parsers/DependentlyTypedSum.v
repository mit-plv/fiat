(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.DependentlyTyped.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
Require Import Parsers.DependentlyTypedOption.
Require Import Common Common.ilist Common.Wf Common.Le.

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

  Variable top_strdata : @parser_computational_strdataT _ String G (@option_methods _ _ _ top_methods').
  Definition leaf_strdata : @parser_computational_strdataT _ String G leaf_methods
    := @strdata _ _ _ leaves_extra_data.

  Local Instance sum_methods : parser_computational_dataT := { methods' := sum_methods' }.

  Definition functor_cross_sum {A A' B B'} (f : option A -> option A') (g : B -> B') (default : B') (x : sum A B) : sum A' B' :=
    match x with
      | inl a => match f (Some a) with
                   | Some a' => inl a'
                   | None => inr default
                 end
      | inr b => inr (g b)
    end.

  Definition functor_str_sum_type {A B}
             (f : StringWithSplitState String A -> Type)
             (g : StringWithSplitState String B -> Type)
             (x : StringWithSplitState String (fun s => sum (A s) (B s)))
  : Type
    := match state_val x with
         | inl st => f {| state_val := st |}
         | inr st => g {| state_val := st |}
       end.

  Local Instance sum_strdata : @parser_computational_strdataT _ String G sum_methods
    := { lower_nonterminal_name_state str0 valid nonterminal_name str
         := functor_cross_sum
              (@lower_nonterminal_name_state _ _ _ _ top_strdata _ _ _ _)
              (@lower_nonterminal_name_state _ _ _ _ leaf_strdata _ _ _ _)
              (gen_state _ _ _ _);
         lower_string_head str0 valid prod prods str
         := functor_cross_sum
              (@lower_string_head _ _ _ _ top_strdata _ _ _ _ _)
              (@lower_string_head _ _ _ _ leaf_strdata _ _ _ _ _)
              (gen_state _ _ _ _);
         lower_string_tail str0 valid prod prods str
         := functor_cross_sum
              (@lower_string_tail _ _ _ _ top_strdata _ _ _ _ _)
              (@lower_string_tail _ _ _ _ leaf_strdata _ _ _ _ _)
              (gen_state _ _ _ _);
         lift_lookup_nonterminal_name_state_lt str0 valid nonterminal_name str pf
         := functor_cross_sum
              (@lift_lookup_nonterminal_name_state_lt _ _ _ _ top_strdata _ _ _ _ pf)
              (@lift_lookup_nonterminal_name_state_lt _ _ _ _ leaf_strdata _ _ _ _ pf)
              (gen_state _ _ _ _);
         lift_lookup_nonterminal_name_state_eq str0 valid nonterminal_name str pf
         := functor_cross_sum
              (@lift_lookup_nonterminal_name_state_eq _ _ _ _ top_strdata _ _ _ _ pf)
              (@lift_lookup_nonterminal_name_state_eq _ _ _ _ leaf_strdata _ _ _ _ pf)
              (gen_state _ _ _ _) }.

  Context (top_success_types' : @parser_dependent_types_success_dataT' _ String top_methods).
  Definition top_success_types : @parser_dependent_types_success_dataT _ String
    := {| stypes' := top_success_types' |}.
  Context (top_failure_types' : @parser_dependent_types_failure_dataT' _ String top_success_types).
  Definition leaf_success_types' : @parser_dependent_types_success_dataT' _ String leaf_methods
    := @stypes' _ _ (@stypes _ _ (@types _ _ _ leaves_extra_data)).
  Definition leaf_failure_types' : @parser_dependent_types_failure_dataT' _ String _
    := @ftypes' _ _ (@types _ _ _ leaves_extra_data).
  Definition leaf_success_types : @parser_dependent_types_success_dataT _ String
    := @stypes _ _ (@types _ _ _ leaves_extra_data).
  Definition top_types : @parser_dependent_types_dataT _ String
    := {| ftypes' := top_failure_types' |}.
  Definition leaf_types : @parser_dependent_types_dataT _ String
    := @types _ _ _ leaves_extra_data.

  Local Instance sum_success_types' : @parser_dependent_types_success_dataT' _ String sum_methods
    := { T_nonterminal_name_success str0 valid name
         := functor_str_sum_type
              (@T_nonterminal_name_success _ _ _ top_success_types' _ _ _)
              (@T_nonterminal_name_success _ _ _ leaf_success_types' _ _ _);
         T_item_success str0 valid it
         := functor_str_sum_type
              (@T_item_success _ _ _ top_success_types' _ _ _)
              (@T_item_success _ _ _ leaf_success_types' _ _ _);
         T_production_success str0 valid prod
         := functor_str_sum_type
              (@T_production_success _ _ _ top_success_types' _ _ _)
              (@T_production_success _ _ _ leaf_success_types' _ _ _);
         T_productions_success str0 valid prods
         := functor_str_sum_type
              (@T_productions_success _ _ _ top_success_types' _ _ _)
              (@T_productions_success _ _ _ leaf_success_types' _ _ _) }.
  Local Instance sum_success_types : @parser_dependent_types_success_dataT _ String
    := {| stypes' := sum_success_types' |}.
  Local Instance sum_failure_types' : @parser_dependent_types_failure_dataT' _ String sum_success_types
    := { T_nonterminal_name_failure str0 valid name
         := functor_str_sum_type
              (@T_nonterminal_name_failure _ _ _ top_failure_types' _ _ _)
              (@T_nonterminal_name_failure _ _ _ leaf_failure_types' _ _ _);
         T_item_failure str0 valid it
         := functor_str_sum_type
              (@T_item_failure _ _ _ top_failure_types' _ _ _)
              (@T_item_failure _ _ _ leaf_failure_types' _ _ _);
         T_production_failure str0 valid prod
         := functor_str_sum_type
              (@T_production_failure _ _ _ top_failure_types' _ _ _)
              (@T_production_failure _ _ _ leaf_failure_types' _ _ _);
         T_productions_failure str0 valid prods
         := functor_str_sum_type
              (@T_productions_failure _ _ _ top_failure_types' _ _ _)
              (@T_productions_failure _ _ _ leaf_failure_types' _ _ _) }.
  Local Instance sum_types : @parser_dependent_types_dataT _ String
    := { ftypes' := sum_failure_types' }.

  Context (top_success_data' : @parser_dependent_types_extra_success_dataT' _ String _ top_success_types top_strdata).



        Global Program Instance minimal_parser_dependent_types_extra_data
               (H_prod_split' : forall str0 valid it its str, @H_prod_splitT' str0 valid it its str None)
        : @parser_dependent_types_extra_dataT _ String G
          := {| cons_success := cons_success;
                H_prod_split str0 valid it its str
                := match str with
                     | {| string_val := str' ; state_val := st' |}
                       => match st' with
                            | None => @H_prod_split' str0 valid it its str'
                            | Some st => @H_prod_split_helper str0 valid it its str' st
                          end
                   end |}.
        Obligation 1. t. Defined.
        Obligation 2. t. Defined.
        Obligation 3. t. Defined.
        Obligation 4. t. Defined.
        Obligation 5. t. Defined.
        Obligation 6. t. Defined.
        Obligation 7. t. Defined.
        Obligation 8. t. Defined.
        Obligation 9. t. Defined.
        Obligation 10. t. Defined.
        Obligation 11. t. Defined.
        Obligation 12. t. Defined.
        Obligation 13. t. Defined.
        Obligation 14. t. Defined.
        Obligation 15. t. Defined.
      End common.
    End parts.

    Definition minimal_parse_nonterminal_name__of__parse
               (H_prod_split' : forall str0 valid it its str, @H_prod_splitT' str0 valid it its str None)
               (nonterminal_name : string)
               (s : String)
               (p : parse_of_item String G s (NonTerminal _ nonterminal_name))
               (H : Forall_parse_of_item
                      (fun _ n => is_valid_nonterminal_name initial_nonterminal_names_data n = true)
                      p)
    : minimal_parse_of_name String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name s initial_nonterminal_names_data s nonterminal_name.
    Proof.
      pose proof (fun H' => @parse_nonterminal_name _ String G (minimal_parser_dependent_types_extra_data H_prod_split') nonterminal_name s (Some (existT _ p (expand_forall_parse_of_item H' H)))) as H0.
      simpl in *.
      unfold T_nonterminal_name_success, T_nonterminal_name_failure in *.
      simpl in *.
      edestruct H0; unfold P;
        repeat match goal with
                 | _ => assumption
                 | [ H : _ -> _ |- _ ] => specialize (H (reflexivity _))
                 | [ H : False |- _ ] => destruct H
                 | _ => intro
                 | [ |- _ /\ _ ] => split
                 | [ |- appcontext[if lt_dec ?a ?b then _ else _] ]
                   => destruct (lt_dec a b)
               end.
    Defined.
  End minimal.
End recursive_descent_parser.
