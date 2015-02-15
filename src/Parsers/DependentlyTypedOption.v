(** * Transform CFG parser into an optional one *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Parsers.DependentlyTyped.
Require Import Common.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {CharType : Type}
          {String : string_like CharType}
          {G : grammar CharType}.

  Context {predata : parser_computational_predataT}.
  Context {methods' : @parser_computational_dataT' _ String predata}.

  (** some helper lemmas to help Coq with inference *)
  Definition split_string_for_production_correct'
             H0 H1 str0 valid it its str st
    := @split_string_for_production_correct CharType String H0 H1 str0 valid it its {| string_val := str ; state_val := st |}.

  Hint Unfold compose : dtp_option_db.
  Hint Extern 1 => apply split_string_for_production_correct' : dtp_option_db.

  Local Ltac t_option' :=
    idtac;
    match goal with
      | _ => progress simpl
      | _ => progress intros
      | _ => progress destruct_head' @StringWithSplitState
      | _ => progress destruct_head' option
      | [ |- Forall _ (map _ _) ] => apply Forall_map
      | _ => progress autounfold with dtp_option_db in *
      | _ => solve [ eauto with dtp_option_db ]
    end.

  Local Ltac t_option := repeat t_option'.

  Local Instance option_methods' : @parser_computational_dataT' _ String predata
    := { split_stateT str0 valid g str := option (split_stateT str0 valid g str);
         split_string_for_production str0 valid it its str
         := match state_val str with
              | None
                => nil
              | Some st
                => map
                     (fun s1s2 =>
                        (lift_StringWithSplitState (fst s1s2) (@Some _),
                         lift_StringWithSplitState (snd s1s2) (@Some _)))
                     (split_string_for_production str0 valid it its {| string_val := string_val str ; state_val := st |})
            end }.
  Proof. clear; abstract t_option. Defined.

  Local Instance option_methods : @parser_computational_dataT _ String
    := { methods' := option_methods' }.

  Context (strdata : @parser_computational_strdataT _ String G {| DependentlyTyped.methods' := methods' |}).

  Local Instance option_strdata : @parser_computational_strdataT _ String G option_methods
    := { lower_nonterminal_name_state str0 valid nonterminal_name s
         := option_map (@lower_nonterminal_name_state _ _ _ _ strdata _ _ _ _);
         lower_string_head str0 valid prod prods s
         := option_map (@lower_string_head _ _ _ _ strdata _ _ _ _ _);
         lower_string_tail str0 valid prod prods s
         := option_map (@lower_string_tail _ _ _ _ strdata _ _ _ _ _);
         lift_lookup_nonterminal_name_state_lt str0 valid nonterminal_name s pf
         := option_map (@lift_lookup_nonterminal_name_state_lt _ _ _ _ strdata _ _ _ _ pf);
         lift_lookup_nonterminal_name_state_eq str0 valid nonterminal_name s pf
         := option_map (@lift_lookup_nonterminal_name_state_eq _ _ _ _ strdata _ _ _ _ pf) }.
End recursive_descent_parser.
