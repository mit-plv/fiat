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

  Local Notation orig_methods := {| DependentlyTyped.methods' := methods' |}.

  Context (strdata : @parser_computational_strdataT _ String G orig_methods).

  Global Instance option_strdata : @parser_computational_strdataT _ String G option_methods
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

  Context (types_success_data' : @parser_dependent_types_success_dataT' _ String orig_methods).

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

  Global Instance option_stypes' : @parser_dependent_types_success_dataT' _ String option_methods
    := { T_nonterminal_name_success str0 valid name
         := option_rect_str (@T_nonterminal_name_success _ _ _ types_success_data' str0 valid name) (fun _ => True);
         T_item_success str0 valid it
         := option_rect_str (@T_item_success _ _ _ types_success_data' str0 valid it) (fun _ => True);
         T_production_success str0 valid prod
         := option_rect_str (@T_production_success _ _ _ types_success_data' str0 valid prod) (fun _ => True) ;
         T_productions_success str0 valid prods
         := option_rect_str (@T_productions_success _ _ _ types_success_data' str0 valid prods) (fun _ => True)  }.

  Definition option_types_success_data : @parser_dependent_types_success_dataT _ String :=
    {| methods := option_methods;
       stypes' := option_stypes' |}.

  Global Instance option_types_failure_data' : @parser_dependent_types_failure_dataT' _ String option_methods
    := { T_nonterminal_name_failure str0 valid name
         := option_rect_str (@T_nonterminal_name_failure _ _ _ types_failure_data' str0 valid name) (fun _ => True);
         T_item_failure str0 valid it
         := option_rect_str (@T_item_failure _ _ _ types_failure_data' str0 valid it) (fun _ => True);
         T_production_failure str0 valid prod
         := option_rect_str (@T_production_failure _ _ _ types_failure_data' str0 valid prod) (fun _ => True) ;
         T_productions_failure str0 valid prods
         := option_rect_str (@T_productions_failure _ _ _ types_failure_data' str0 valid prods) (fun _ => True)  }.
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (name : string)
                   (str : StringWithSplitState String (split_stateT str0 valid (include_nonterminal_name _ name))),
              Type;
          T_item_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid it)),
              Type;
          T_production_success
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prod)),
              Type;

          T_productions_success
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prods)),
              Type }.

      Class parser_dependent_types_success_dataT :=
        { methods :> parser_computational_dataT;
          stypes' :> parser_dependent_types_success_dataT' }.

      Class parser_dependent_types_failure_dataT' `{parser_dependent_types_success_dataT} :=
        { T_nonterminal_name_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (name : string)
                   (str : StringWithSplitState String (split_stateT str0 valid (include_nonterminal_name _ name))),
              Type;
          T_item_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid it)),
              Type;
          T_production_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prod)),
              Type;

          split_string_lift_T
            (str0 : String) (valid : nonterminal_names_listT)
            (it : item CharType) (its : production CharType)
            (str : StringWithSplitState String (split_stateT str0 valid (it::its : production CharType)))
            (split : list
                       (StringWithSplitState String (split_stateT str0 valid it) *
                        StringWithSplitState String (split_stateT str0 valid its)))
          := str ≤s str0
             -> fold_right
                  Datatypes.prod
                  unit
                  (map (fun s1s2 =>
                          let s1 := fst s1s2 in
                          let s2 := snd s1s2 in
                          ((T_item_failure str0 valid it s1 * T_production_failure str0 valid its s2)
                           + (T_item_success str0 valid it s1 * T_production_failure str0 valid its s2)
                           + (T_item_failure str0 valid it s1 * T_production_success str0 valid its s2))%type)
                       split)
             -> T_production_failure str0 valid (it::its) str;

          T_productions_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prods)),
              Type }.

      Class parser_dependent_types_dataT :=
        { stypes :> parser_dependent_types_success_dataT;
          ftypes' :> parser_dependent_types_failure_dataT' }.

      Class parser_dependent_types_extra_success_dataT' `{types : parser_dependent_types_success_dataT, @parser_computational_strdataT (@methods types)} :=
        { lift_success
          : forall {str0 valid} nonterminal_name {str},
              @T_nonterminal_name_success _ _ str0 valid nonterminal_name (lift_StringWithSplitState str lower_nonterminal_name_state)
              -> @T_item_success _ _ str0 valid (NonTerminal _ nonterminal_name) str;
          parse_terminal_success
          : forall {str0 valid} ch {str},
              let ret := @T_item_success _ _ str0 valid (Terminal ch) str in
              [[ ch ]] =s str -> ret;
          parse_empty_success
          : forall {str0 valid str},
              let ret := @T_production_success _ _ str0 valid nil str in
              str =s Empty _ -> ret;
          cons_success
          : forall {str0 valid} it its {s1 s2 str},
              let a1 := @T_item_success _ _ str0 valid it s1 in
              let a2 := @T_production_success _ _ str0 valid its s2 in
              let ret := @T_production_success _ _ str0 valid (it::its) str in
              str ≤s str0 -> s1 ++ s2 =s str -> In (s1, s2) (split_string_for_production str0 valid it its str) -> a1 -> a2 -> ret;

          lift_prods_success_head
          : forall {str0 valid prod prods str},
              let ret := @T_productions_success _ _ str0 valid (prod::prods) str in
              let arg := @T_production_success _ _ str0 valid prod (lift_StringWithSplitState str lower_string_head) in
              arg -> ret;
          lift_prods_success_tail
          : forall {str0 valid prod prods str},
              let ret := @T_productions_success _ _ str0 valid (prod::prods) str in
              let arg := @T_productions_success _ _ str0 valid prods (lift_StringWithSplitState str lower_string_tail) in
              arg -> ret;

          lift_parse_nonterminal_name_success_lt
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_success _ _ str0 valid nonterminal_name str in
              forall (pf : Length str < Length str0),
                let arg := @T_productions_success _ _ str initial_nonterminal_names_data (Lookup G nonterminal_name) (lift_StringWithSplitState str (lift_lookup_nonterminal_name_state_lt pf)) in
                arg -> ret;
          lift_parse_nonterminal_name_success_eq
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_success _ _ str0 valid nonterminal_name str in
              forall (pf : str = str0 :> String),
                let arg := @T_productions_success _ _ str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) (lift_StringWithSplitState str (lift_lookup_nonterminal_name_state_eq pf)) in

                is_valid_nonterminal_name valid nonterminal_name = true -> arg -> ret
        }.

      Class parser_dependent_types_extra_failure_dataT' `{types : parser_dependent_types_dataT, @parser_computational_strdataT (@methods (@stypes types))} :=
        { lift_failure
          : forall {str0 valid} nonterminal_name {str},
              @T_nonterminal_name_failure _ _ str0 valid nonterminal_name (lift_StringWithSplitState str lower_nonterminal_name_state)
              -> @T_item_failure _ _ str0 valid (NonTerminal _ nonterminal_name) str;
          parse_terminal_failure
          : forall {str0 valid} ch {str},
              let ret := @T_item_failure _ _ str0 valid (Terminal ch) str in
              ([[ ch ]] =s str) = false -> ret;
          parse_empty_failure
          : forall {str0 valid str},
              let ret := @T_production_failure _ _ str0 valid nil str in
              str ≤s str0 -> (str =s Empty _) = false -> ret;

          fail_parse_nil_productions
          : forall {str0 valid str}, T_productions_failure str0 valid [] str;
          lift_prods_failure
          : forall {str0 valid prod prods str},
              let ret := @T_productions_failure _ _ str0 valid (prod::prods) str in
              let a1 := @T_production_failure _ _ str0 valid prod (lift_StringWithSplitState str lower_string_head) in
              let a2 := @T_productions_failure _ _ str0 valid prods (lift_StringWithSplitState str lower_string_tail) in
              a1 -> a2 -> ret;

          H_prod_split : forall str0 valid it its str, split_string_lift_T str0 valid it its str (split_string_for_production str0 valid it its str);


          lift_parse_nonterminal_name_failure_lt
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_failure _ _ str0 valid nonterminal_name str in
              forall (pf : Length str < Length str0),
                let arg := @T_productions_failure _ _ str initial_nonterminal_names_data (Lookup G nonterminal_name) (lift_StringWithSplitState str (lift_lookup_nonterminal_name_state_lt pf)) in
                arg -> ret;
          lift_parse_nonterminal_name_failure_eq
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_failure _ _ str0 valid nonterminal_name str in
              forall (pf : str = str0 :> String),
                let arg := @T_productions_failure _ _ str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) (lift_StringWithSplitState str (lift_lookup_nonterminal_name_state_eq pf)) in
                arg -> ret;

          elim_parse_nonterminal_name_failure
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_failure _ _ str0 valid nonterminal_name str in
              str ≤s str0
              -> ~ Length str < Length str0
              -> is_valid_nonterminal_name valid nonterminal_name = false
              -> ret
        }.

      Class parser_dependent_types_extra_dataT :=
        { types :> parser_dependent_types_dataT;
          strdata :> parser_computational_strdataT;
          extra_success_data :> parser_dependent_types_extra_success_dataT';
          extra_failure_data :> parser_dependent_types_extra_failure_dataT' }.
End recursive_descent_parser.
