(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.
(*(** We implement a generic recursive descent parser.  We parameterize
    over a number of parameters:

    - [T : Type] - the type of results of successful parsing.
      Parameterizing over this allows, e.g., higher-order parsing.

      TODO?: generalize this to use continuations instead, so we can
      do monadic side-effects when parsing.

    - [aggregate : String → T → String → T → T] - takes the results of
      two successful adjacent parses and combines them.

    - [pick_parses : String → productions → list (list String)] - A
      non-terminal is a list of production-objectss.  This function will break up
      a string into a list of possible splits; a split is an
      assignment of a part of the string to each production.


    The basic idea is that

FIXME *)*)

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

(** TODO: Replace "name" with "nonterminal" *)

Inductive any_grammar CharType :=
| include_item (_ : item CharType)
| include_production (_ : production CharType)
| include_productions (_ : productions CharType)
| include_nonterminal_name (_ : string).
Global Coercion include_item : item >-> any_grammar.
Global Coercion include_production : production >-> any_grammar.
Global Coercion include_productions : productions >-> any_grammar.

Section recursive_descent_parser.
  Context {CharType : Type}
          {String : string_like CharType}
          {G : grammar CharType}.

  Class parser_computational_predataT :=
    { nonterminal_names_listT : Type;
      initial_nonterminal_names_data : nonterminal_names_listT;
      is_valid_nonterminal_name : nonterminal_names_listT -> string -> bool;
      remove_nonterminal_name : nonterminal_names_listT -> string -> nonterminal_names_listT;
      nonterminal_names_listT_R : nonterminal_names_listT -> nonterminal_names_listT -> Prop;
      remove_nonterminal_name_dec : forall ls nonterminal_name,
                             is_valid_nonterminal_name ls nonterminal_name = true
                             -> nonterminal_names_listT_R (remove_nonterminal_name ls nonterminal_name) ls;
      ntl_wf : well_founded nonterminal_names_listT_R }.

  Class parser_computational_dataT' `{parser_computational_predataT} :=
    { split_stateT : any_grammar CharType -> String -> Type;
      split_string_for_production
      : forall (it : item CharType) (its : production CharType) (str0 : StringWithSplitState String (split_stateT (it::its : production CharType))),
          list (StringWithSplitState String (split_stateT it)
                * StringWithSplitState String (split_stateT its));
      split_string_for_production_correct
      : forall it its str0,
          let P f := List.Forall f (@split_string_for_production it its str0) in
          P (fun s1s2 => (fst s1s2 ++ snd s1s2 =s str0) = true) }.

  Class parser_computational_strdataT `{parser_computational_dataT'} :=
    { lower_nonterminal_name_state
      : forall {nonterminal_name} s,
          split_stateT (NonTerminal _ nonterminal_name) s -> split_stateT (include_nonterminal_name _ nonterminal_name) s;

      lower_string_head
      : forall {prod : production CharType}
               {prods : productions CharType}
               s,
          split_stateT (prod::prods : productions CharType) s -> split_stateT prod s;
      lower_string_tail
      : forall {prod : production CharType}
               {prods : productions CharType}
               s,
          split_stateT (prod::prods : productions CharType) s -> split_stateT prods s;

      lift_lookup_nonterminal_name_state
      : forall {nonterminal_name} s,
          split_stateT (include_nonterminal_name _ nonterminal_name) s -> split_stateT (Lookup G nonterminal_name) s }.

  Class parser_computational_dataT :=
    { premethods :> parser_computational_predataT;
      methods' :> parser_computational_dataT' }.

  Section generic.
    Section parts.
      Class parser_dependent_types_dataT :=
        { methods :> parser_computational_dataT;
          T_nonterminal_name_success
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (name : string)
                   (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ name))),
              Type;
          T_nonterminal_name_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (name : string)
                   (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ name))),
              Type;
          T_item_success
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT it)),
              Type;
          T_item_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT it)),
              Type;
          T_production_success
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT prod)),
              Type;
          T_production_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT prod)),
              Type;

          split_string_lift_T
            (str0 : String) (valid : nonterminal_names_listT)
            (it : item CharType) (its : production CharType)
            (str : StringWithSplitState String (split_stateT (it::its : production CharType)))
            (split : list
                       (StringWithSplitState String (split_stateT it) *
                        StringWithSplitState String (split_stateT its)))
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

          T_productions_success
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT prods)),
              Type;
          T_productions_failure
          : forall (str0 : String) (valid : nonterminal_names_listT)
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT prods)),
              Type }.

      Class parser_dependent_types_extra_dataT :=
        { types :> parser_dependent_types_dataT;
          strdata :> parser_computational_strdataT;
          lift_success
          : forall {str0 valid} nonterminal_name {str},
              @T_nonterminal_name_success _ str0 valid nonterminal_name (lift_StringWithSplitState lower_nonterminal_name_state str)
              -> @T_item_success _ str0 valid (NonTerminal _ nonterminal_name) str;
          lift_failure
          : forall {str0 valid} nonterminal_name {str},
              @T_nonterminal_name_failure _ str0 valid nonterminal_name (lift_StringWithSplitState lower_nonterminal_name_state str)
              -> @T_item_failure _ str0 valid (NonTerminal _ nonterminal_name) str;
          parse_terminal_success
          : forall {str0 valid} ch {str},
              let ret := @T_item_success _ str0 valid (Terminal ch) str in
              [[ ch ]] =s str -> ret;
          parse_terminal_failure
          : forall {str0 valid} ch {str},
              let ret := @T_item_failure _ str0 valid (Terminal ch) str in
              ([[ ch ]] =s str) = false -> ret;
          parse_empty_success
          : forall {str0 valid str},
              let ret := @T_production_success _ str0 valid nil str in
              str =s Empty _ -> ret;
          parse_empty_failure
          : forall {str0 valid str},
              let ret := @T_production_failure _ str0 valid nil str in
              str ≤s str0 -> (str =s Empty _) = false -> ret;
          cons_success
          : forall {str0 valid} it its {s1 s2 str},
              let a1 := @T_item_success _ str0 valid it s1 in
              let a2 := @T_production_success _ str0 valid its s2 in
              let ret := @T_production_success _ str0 valid (it::its) str in
              str ≤s str0 -> s1 ++ s2 =s str -> In (s1, s2) (split_string_for_production it its str) -> a1 -> a2 -> ret;

          fail_parse_nil_productions
          : forall {str0 valid str}, T_productions_failure str0 valid [] str;
          lift_prods_success_head
          : forall {str0 valid prod prods str},
              let ret := @T_productions_success _ str0 valid (prod::prods) str in
              let arg := @T_production_success _ str0 valid prod (lift_StringWithSplitState lower_string_head str) in
              arg -> ret;
          lift_prods_success_tail
          : forall {str0 valid prod prods str},
              let ret := @T_productions_success _ str0 valid (prod::prods) str in
              let arg := @T_productions_success _ str0 valid prods (lift_StringWithSplitState lower_string_tail str) in
              arg -> ret;
          lift_prods_failure
          : forall {str0 valid prod prods str},
              let ret := @T_productions_failure _ str0 valid (prod::prods) str in
              let a1 := @T_production_failure _ str0 valid prod (lift_StringWithSplitState lower_string_head str) in
              let a2 := @T_productions_failure _ str0 valid prods (lift_StringWithSplitState lower_string_tail str) in
              a1 -> a2 -> ret;

          H_prod_split : forall str0 valid it its str, split_string_lift_T str0 valid it its str (split_string_for_production it its str);


          lift_parse_nonterminal_name_success_lt
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_success _ str0 valid nonterminal_name str in
              let arg := @T_productions_success _ str initial_nonterminal_names_data (Lookup G nonterminal_name) (lift_StringWithSplitState lift_lookup_nonterminal_name_state str) in
              Length str < Length str0 -> arg -> ret;
          lift_parse_nonterminal_name_failure_lt
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_failure _ str0 valid nonterminal_name str in
              let arg := @T_productions_failure _ str initial_nonterminal_names_data (Lookup G nonterminal_name) (lift_StringWithSplitState lift_lookup_nonterminal_name_state str) in
              Length str < Length str0 -> arg -> ret;
          lift_parse_nonterminal_name_success_eq
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_success _ str0 valid nonterminal_name str in
              let arg := @T_productions_success _ str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) (lift_StringWithSplitState lift_lookup_nonterminal_name_state str) in
              str = str0 :> String
              -> is_valid_nonterminal_name valid nonterminal_name = true
              -> arg -> ret;
          lift_parse_nonterminal_name_failure_eq
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_failure _ str0 valid nonterminal_name str in
              let arg := @T_productions_failure _ str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) (lift_StringWithSplitState lift_lookup_nonterminal_name_state str) in
              ~Length str < Length str0 -> arg -> ret;

          elim_parse_nonterminal_name_failure
          : forall {str0 valid nonterminal_name str},
              let ret := @T_nonterminal_name_failure _ str0 valid nonterminal_name str in
              str ≤s str0
              -> ~ Length str < Length str0
              -> is_valid_nonterminal_name valid nonterminal_name = false
              -> ret
        }.

      Context `{types_data : parser_dependent_types_extra_dataT}.

      Section item.
        Context (str0 : String)
                (valid : nonterminal_names_listT).

        Let str_matches_nonterminal_nameT
            (str : String)
          := forall nonterminal_name st,
               let s := {| string_val := str ; state_val := st |} in
               sum (T_nonterminal_name_success str0 valid nonterminal_name s)
                   (T_nonterminal_name_failure str0 valid nonterminal_name s).
        Let T_item := fun it str => sum (T_item_success str0 valid it str) (T_item_failure str0 valid it str).

        Definition parse_item
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT it))
                   (str_matches_nonterminal_name : str_matches_nonterminal_nameT str)
        : T_item it str.
        Proof.
          destruct it as [ ch | nonterminal_name ].
          { refine (if Sumbool.sumbool_of_bool ([[ ch ]] =s str)
                    then inl (parse_terminal_success ch _)
                    else inr (parse_terminal_failure ch _));
            assumption. }
          { refine (if str_matches_nonterminal_name nonterminal_name _
                    then inl (lift_success _ _)
                    else inr (lift_failure _ _));
            eassumption. }
        Defined.
      End item.

      Section production_and_productions.
        Context (str0 : String)
                (valid : nonterminal_names_listT).

        Context (parse_nonterminal_name
                 : forall str,
                     str ≤s str0
                     -> forall nonterminal_name st,
                          let s := {| string_val := str ; state_val := st |} in
                          sum (@T_nonterminal_name_success _ str0 valid nonterminal_name s) (@T_nonterminal_name_failure _ str0 valid nonterminal_name s)).

        Let T_production := fun prod str => sum (T_production_success str0 valid prod str) (T_production_failure str0 valid prod str).

        Let T_productions := fun prods str => sum (T_productions_success str0 valid prods str) (T_productions_failure str0 valid prods str).


        Section production.
          Section helper.
            Local Ltac left_right_t :=
              solve [ left; left_right_t
                    | right; left_right_t
                    | split; assumption ].

            Fixpoint parse_production_helper
                     (it : item CharType)
                     (its : production CharType)
                     (str : StringWithSplitState String (split_stateT (it::its : production CharType)))
                     (pf : str ≤s str0)
                     (splits : list
                                 (StringWithSplitState String (split_stateT it) *
                                  StringWithSplitState String (split_stateT its)))
                     (splits_included : forall s1s2, In s1s2 splits -> In s1s2 (split_string_for_production it its str))
                     (parse_production : forall str1,
                                           let ret := T_production its str1 in
                                           str1 ≤s str0 -> ret)
                     (H_prod_split' : split_string_lift_T str0 valid it its str splits)
                     (splits_correct : let P f := List.Forall f splits in
                                       P (fun s1s2 => (fst s1s2 ++ snd s1s2 =s str) = true))
                     {struct splits}
            : T_production (it::its) str.
            Proof.
              destruct splits as [ | [s1 s2] splits ]; simpl in *.
              { exact (inr (H_prod_split' pf tt)). }
              { refine (let Hs1 := _ in
                        let Hs2 := _ in
                        match (@parse_item str0
                                           valid
                                           it
                                           s1
                                           (@parse_nonterminal_name s1 Hs1)),
                              (@parse_production s2 Hs2) with
                          | inl p_it, inl p_its => inl (@cons_success _ str0 valid _ _ s1 s2 _ pf _ _ _ _)
                          | inl p_it, inr p_its => parse_production_helper it its str pf splits _ parse_production _ _
                          | inr p_it, inl p_its => parse_production_helper it its str pf splits _ parse_production _ _
                          | inr p_it, inr p_its => parse_production_helper it its str pf splits _ parse_production _ _
                        end);
                clear parse_production_helper;
                try solve [ assumption
                          | apply splits_included; left; reflexivity
                          | intros; apply splits_included; right; assumption
                          | clear -pf splits_correct;
                            abstract (
                                inversion splits_correct; subst;
                                simpl in *;
                                  etransitivity; [ etransitivity | exact pf ];
                                [
                                | right; apply bool_eq_correct; eassumption ];
                                first [ apply str_le1_append
                                      | apply str_le2_append ]
                              )
                          | clear -splits_correct;
                            abstract (inversion splits_correct; subst; assumption)
                          | (intros ? H'; apply H_prod_split'; try assumption; split; [ | exact H' ]);
                            left_right_t ].
              }
            Defined.
          End helper.

          Fixpoint parse_production
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT prod))
                   (pf : str ≤s str0)
                   {struct prod}
          : T_production prod str.
          Proof.
            destruct prod as [ | it its ].
            { (** 0-length production, only accept empty *)
              refine (if Sumbool.sumbool_of_bool (str =s Empty _)
                      then inl (parse_empty_success _)
                      else inr (parse_empty_failure _ _));
              assumption. }
            { exact (@parse_production_helper
                       it its str pf
                       (split_string_for_production it its str)
                       (fun _ H => H)
                       (@parse_production its)
                       (H_prod_split valid it its _)
                       (split_string_for_production_correct it its str)). }
          Defined.
        End production.

        Section productions.
          Fixpoint parse_productions
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT prods))
                   (pf : str ≤s str0)
          : T_productions prods str.
          Proof.
            destruct prods as [ | prod' prods' ].
            { exact (inr fail_parse_nil_productions). }
            { exact (match @parse_production prod' (lift_StringWithSplitState lower_string_head str) pf,
                           @parse_productions prods' (lift_StringWithSplitState lower_string_tail str) pf with
                       | inl prod_success, _
                         => inl (lift_prods_success_head prod_success)
                       | _, inl prods_success
                         => inl (lift_prods_success_tail prods_success)
                       | inr prod_failure, inr prods_failure
                         => inr (lift_prods_failure prod_failure prods_failure)
                     end). }
          Defined.
        End productions.
      End production_and_productions.

      Section nonterminal_names.
        Let T_productions := fun str0 valid prods str => sum (T_productions_success str0 valid prods str) (T_productions_failure str0 valid prods str).

        Let T_nonterminal_name := fun str0 valid nonterminal_name str => sum (@T_nonterminal_name_success _ str0 valid nonterminal_name str) (@T_nonterminal_name_failure _ str0 valid nonterminal_name str).

        Section step.
          Context (str0 : String)
                  (valid : nonterminal_names_listT).

          Context (parse_nonterminal_name
                   : forall (p : String * nonterminal_names_listT),
                       prod_relation (ltof _ Length) nonterminal_names_listT_R p (str0, valid)
                       -> forall (nonterminal_name : string)
                                 (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ nonterminal_name)))
                                 (pf : str ≤s fst p),
                            T_nonterminal_name (fst p) (snd p) nonterminal_name str).

          Definition parse_nonterminal_name_step
                     (nonterminal_name : string)
                     (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ nonterminal_name)))
                     (pf : str ≤s str0)
          : T_nonterminal_name str0 valid nonterminal_name str.
          Proof.
            refine (if lt_dec (Length str) (Length str0)
                    then (** [str] got smaller, so we reset the valid nonterminal_names list *)
                      if (@parse_productions
                            _
                            _
                            (fun str1 pf nonterminal_name st
                             => @parse_nonterminal_name
                                  (str : String, initial_nonterminal_names_data)
                                  (or_introl _)
                                  nonterminal_name
                                  {| string_val := str1 ; state_val := st |}
                                  pf)
                            (Lookup G nonterminal_name)
                            (lift_StringWithSplitState lift_lookup_nonterminal_name_state str)
                            (or_intror eq_refl))
                      then inl (lift_parse_nonterminal_name_success_lt _ _)
                      else inr (lift_parse_nonterminal_name_failure_lt _ _)
                    else (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal_name already *)
                      if Sumbool.sumbool_of_bool (is_valid_nonterminal_name valid nonterminal_name)
                      then (** It was valid, so we can remove it *)
                        if (@parse_productions
                              _ _
                              (fun str1 (pf : str1 ≤s str0) nonterminal_name' st
                               => @parse_nonterminal_name
                                    (str0, remove_nonterminal_name valid nonterminal_name)
                                    (or_intror (conj eq_refl (@remove_nonterminal_name_dec _ _ _ _)))
                                    nonterminal_name'
                                    {| string_val := str1 ; state_val := st |}
                                    pf)
                              (Lookup G nonterminal_name)
                              (lift_StringWithSplitState lift_lookup_nonterminal_name_state str)
                              (or_intror _))
                        then inl (lift_parse_nonterminal_name_success_eq _ _ _)
                        else inr (lift_parse_nonterminal_name_failure_eq _ _)
                      else (** oops, we already saw this nonterminal_name in the past.  ABORT! *)
                        inr (elim_parse_nonterminal_name_failure _ _ _));
            try solve [ assumption
                      | destruct_head_hnf or; try assumption; exfalso; eauto with nocore ].
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_name_or_abort
          : forall (p : String * nonterminal_names_listT)
                   (nonterminal_name : string)
                   (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ nonterminal_name)))
                   (pf : str ≤s fst p),
              T_nonterminal_name (fst p) (snd p) nonterminal_name str
            := @Fix3
                 (prod String nonterminal_names_listT) _ _ _
                 _ (@well_founded_prod_relation
                      String
                      nonterminal_names_listT
                      _
                      _
                      (well_founded_ltof _ Length)
                      ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_name_step (fst sl) (snd sl)).

          Definition parse_nonterminal_name
                     (nonterminal_name : string)
                     (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ nonterminal_name)))
          : T_nonterminal_name str initial_nonterminal_names_data nonterminal_name str
            := @parse_nonterminal_name_or_abort
                 (str : String, initial_nonterminal_names_data)
                 nonterminal_name
                 str
                 (or_intror eq_refl).
        End wf.
      End nonterminal_names.
    End parts.
  End generic.
End recursive_descent_parser.
