(** * Definition of the interface and implementation of the dependently-typed CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.BaseTypes.
Require Import Common Common.Wf.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

(** TODO: Replace "name" with "nonterminal" *)

Section recursive_descent_parser.
  Context {CharType : Type}
          {String : string_like CharType}
          {G : grammar CharType}.

  Section generic.
    Section parts.
      Class parser_dependent_types_success_dataT' `{@parser_computational_dataT _ String} :=
        { T_nonterminal_success
          : forall (str0 : String) (valid : nonterminals_listT)
                   (nt : string)
                   (str : StringWithSplitState String (split_stateT str0 valid (include_nonterminal _ nt))),
              Type;
          T_item_success
          : forall (str0 : String) (valid : nonterminals_listT)
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid it)),
              Type;
          T_production_success
          : forall (str0 : String) (valid : nonterminals_listT)
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prod)),
              Type;

          T_productions_success
          : forall (str0 : String) (valid : nonterminals_listT)
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prods)),
              Type }.

      Class parser_dependent_types_success_dataT :=
        { methods :> parser_computational_dataT;
          stypes' :> parser_dependent_types_success_dataT' }.

      Class parser_dependent_types_failure_dataT' `{parser_dependent_types_success_dataT} :=
        { T_nonterminal_failure
          : forall (str0 : String) (valid : nonterminals_listT)
                   (nt : string)
                   (str : StringWithSplitState String (split_stateT str0 valid (include_nonterminal _ nt))),
              Type;
          T_item_failure
          : forall (str0 : String) (valid : nonterminals_listT)
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid it)),
              Type;
          T_production_failure
          : forall (str0 : String) (valid : nonterminals_listT)
                   (prod : production CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prod)),
              Type;

          split_string_lift_T
            (str0 : String) (valid : nonterminals_listT)
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
          : forall (str0 : String) (valid : nonterminals_listT)
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prods)),
              Type }.

      Class parser_dependent_types_dataT :=
        { stypes :> parser_dependent_types_success_dataT;
          ftypes' :> parser_dependent_types_failure_dataT' }.

      Class parser_dependent_types_extra_success_dataT' `{types : parser_dependent_types_success_dataT, @parser_computational_strdataT _ _ _ (@methods types)} :=
        { lift_success
          : forall {str0 valid} nonterminal {str},
              @T_nonterminal_success _ _ str0 valid nonterminal (lift_StringWithSplitState str lower_nonterminal_state)
              -> @T_item_success _ _ str0 valid (NonTerminal _ nonterminal) str;
          parse_terminal_success
          : forall {str0 valid} ch {str},
              let ret := @T_item_success _ _ str0 valid (Terminal ch) str in
              [[ ch ]] =s str -> ret;
          parse_empty_success
          : forall {str0 valid str},
              let ret := @T_production_success _ _ str0 valid nil str in
              str =s Empty _ -> ret;
          cons_success
          : forall {str0 valid} it its {str s1 s2},
              let a1 := @T_item_success _ _ str0 valid it s1 in
              let a2 := @T_production_success _ _ str0 valid its s2 in
              let ret := @T_production_success _ _ str0 valid (it::its) str in
              str ≤s str0 -> s1 ++ s2 =s str -> a1 -> a2 -> ret;

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

          lift_parse_nonterminal_success_lt
          : forall {str0 valid nonterminal str},
              let ret := @T_nonterminal_success _ _ str0 valid nonterminal str in
              forall (pf : Length str < Length str0),
                let arg := @T_productions_success _ _ str initial_nonterminals_data (Lookup G nonterminal) (lift_StringWithSplitState str (lift_lookup_nonterminal_state_lt pf)) in
                is_valid_nonterminal initial_nonterminals_data nonterminal = true -> arg -> ret;
          lift_parse_nonterminal_success_eq
          : forall {str0 valid nonterminal str},
              let ret := @T_nonterminal_success _ _ str0 valid nonterminal str in
              forall (pf : str = str0 :> String),
                let arg := @T_productions_success _ _ str0 (remove_nonterminal valid nonterminal) (Lookup G nonterminal) (lift_StringWithSplitState str (lift_lookup_nonterminal_state_eq pf)) in

                is_valid_nonterminal initial_nonterminals_data nonterminal = true -> is_valid_nonterminal valid nonterminal = true -> arg -> ret
        }.

      Class parser_dependent_types_extra_failure_dataT' `{types : parser_dependent_types_dataT, @parser_computational_strdataT _ _ _ (@methods (@stypes types))} :=
        { lift_failure
          : forall {str0 valid} nonterminal {str},
              @T_nonterminal_failure _ _ str0 valid nonterminal (lift_StringWithSplitState str lower_nonterminal_state)
              -> @T_item_failure _ _ str0 valid (NonTerminal _ nonterminal) str;
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


          lift_parse_nonterminal_failure_lt
          : forall {str0 valid nonterminal str},
              let ret := @T_nonterminal_failure _ _ str0 valid nonterminal str in
              forall (pf : Length str < Length str0),
                let arg := @T_productions_failure _ _ str initial_nonterminals_data (Lookup G nonterminal) (lift_StringWithSplitState str (lift_lookup_nonterminal_state_lt pf)) in
                is_valid_nonterminal initial_nonterminals_data nonterminal = true -> arg -> ret;
          lift_parse_nonterminal_failure_eq
          : forall {str0 valid nonterminal str},
              let ret := @T_nonterminal_failure _ _ str0 valid nonterminal str in
              forall (pf : str = str0 :> String),
                let arg := @T_productions_failure _ _ str0 (remove_nonterminal valid nonterminal) (Lookup G nonterminal) (lift_StringWithSplitState str (lift_lookup_nonterminal_state_eq pf)) in
                is_valid_nonterminal initial_nonterminals_data nonterminal = true -> arg -> ret;

          elim_parse_nonterminal_failure_init
          : forall {str0 valid nonterminal str},
              let ret := @T_nonterminal_failure _ _ str0 valid nonterminal str in
              str ≤s str0
              -> is_valid_nonterminal initial_nonterminals_data nonterminal = false
              -> ret;
          elim_parse_nonterminal_failure
          : forall {str0 valid nonterminal str},
              let ret := @T_nonterminal_failure _ _ str0 valid nonterminal str in
              str ≤s str0
              -> ~Length str < Length str0
              -> is_valid_nonterminal valid nonterminal = false
              -> ret
        }.

      Class parser_dependent_types_extra_dataT :=
        { types :> parser_dependent_types_dataT;
          strdata :> parser_computational_strdataT;
          extra_success_data :> parser_dependent_types_extra_success_dataT';
          extra_failure_data :> parser_dependent_types_extra_failure_dataT' }.

      Context `{types_data : parser_dependent_types_extra_dataT}.

      Section item.
        Context (str0 : String)
                (valid : nonterminals_listT).

        Let str_matches_nonterminalT
            (str : String)
          := forall nonterminal st,
               let s := {| string_val := str ; state_val := st |} in
               sum (T_nonterminal_success str0 valid nonterminal s)
                   (T_nonterminal_failure str0 valid nonterminal s).
        Let T_item := fun it str => sum (T_item_success str0 valid it str) (T_item_failure str0 valid it str).

        Definition parse_item
                   (it : item CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid it))
                   (str_matches_nonterminal : str_matches_nonterminalT str)
        : T_item it str.
        Proof.
          destruct it as [ ch | nonterminal ].
          { refine (if Sumbool.sumbool_of_bool ([[ ch ]] =s str)
                    then inl (parse_terminal_success ch _)
                    else inr (parse_terminal_failure ch _));
            assumption. }
          { refine (if str_matches_nonterminal nonterminal _
                    then inl (lift_success _ _)
                    else inr (lift_failure _ _));
            eassumption. }
        Defined.
      End item.

      Section production_and_productions.
        Context (str0 : String)
                (valid : nonterminals_listT).

        Context (parse_nonterminal
                 : forall str,
                     str ≤s str0
                     -> forall nonterminal st,
                          let s := {| string_val := str ; state_val := st |} in
                          sum (@T_nonterminal_success _ _ str0 valid nonterminal s) (@T_nonterminal_failure _ _ str0 valid nonterminal s)).

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
                     (str : StringWithSplitState String (split_stateT str0 valid (it::its : production CharType)))
                     (pf : str ≤s str0)
                     (splits : list
                                 (StringWithSplitState String (split_stateT str0 valid it) *
                                  StringWithSplitState String (split_stateT str0 valid its)))
                     (splits_included : forall s1s2, In s1s2 splits -> In s1s2 (split_string_for_production str0 valid it its str))
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
                                           (@parse_nonterminal s1 Hs1)),
                              (@parse_production s2 Hs2) with
                          | inl p_it, inl p_its => inl (@cons_success _ _ _ str0 valid _ _ _ s1 s2 pf _ _ _)
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
                   (str : StringWithSplitState String (split_stateT str0 valid prod))
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
                       (split_string_for_production str0 valid it its str)
                       (fun _ H => H)
                       (@parse_production its)
                       (H_prod_split valid it its _)
                       (split_string_for_production_correct str0 valid it its str)). }
          Defined.
        End production.

        Section productions.
          Fixpoint parse_productions
                   (prods : productions CharType)
                   (str : StringWithSplitState String (split_stateT str0 valid prods))
                   (pf : str ≤s str0)
          : T_productions prods str.
          Proof.
            destruct prods as [ | prod' prods' ].
            { exact (inr fail_parse_nil_productions). }
            { exact (match @parse_production prod' (lift_StringWithSplitState str lower_string_head) pf,
                           @parse_productions prods' (lift_StringWithSplitState str lower_string_tail) pf with
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

      Section nonterminals.
        Let T_productions := fun str0 valid prods str => sum (T_productions_success str0 valid prods str) (T_productions_failure str0 valid prods str).

        Let T_nonterminal := fun str0 valid nonterminal str => sum (@T_nonterminal_success _ _ str0 valid nonterminal str) (@T_nonterminal_failure _ _ str0 valid nonterminal str).

        Section step.
          Context (str0 : String)
                  (valid : nonterminals_listT).

          Context (parse_nonterminal
                   : forall (p : String * nonterminals_listT),
                       prod_relation (ltof _ Length) nonterminals_listT_R p (str0, valid)
                       -> forall (nonterminal : string)
                                 (str : StringWithSplitState String (split_stateT _ _ (include_nonterminal _ nonterminal)))
                                 (pf : str ≤s fst p),
                            T_nonterminal (fst p) (snd p) nonterminal str).

          Definition parse_nonterminal_step
                     (nonterminal : string)
                     (str : StringWithSplitState String (split_stateT _ _ (include_nonterminal _ nonterminal)))
                     (pf : str ≤s str0)
          : T_nonterminal str0 valid nonterminal str.
          Proof.
            hnf.
            refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal initial_nonterminals_data nonterminal)
                    then
                      if lt_dec (Length str) (Length str0)
                      then (** [str] got smaller, so we reset the valid nonterminals list *)
                        if (@parse_productions
                              _
                              _
                              (fun str1 pf nonterminal st
                               => @parse_nonterminal
                                    (str : String, initial_nonterminals_data)
                                    (or_introl _)
                                    nonterminal
                                    {| string_val := str1 ; state_val := st |}
                                    pf)
                              (Lookup G nonterminal)
                              (lift_StringWithSplitState str (lift_lookup_nonterminal_state_lt _))
                              (or_intror eq_refl))
                        then inl (lift_parse_nonterminal_success_lt _ _ _)
                        else inr (lift_parse_nonterminal_failure_lt _ _ _)
                      else (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                        if Sumbool.sumbool_of_bool (is_valid_nonterminal valid nonterminal)
                        then (** It was valid, so we can remove it *)
                          if (@parse_productions
                                _ _
                                (fun str1 (pf : str1 ≤s str0) nonterminal' st
                                 => @parse_nonterminal
                                      (str0, remove_nonterminal valid nonterminal)
                                      (or_intror (conj eq_refl (@remove_nonterminal_dec _ _ _ _)))
                                      nonterminal'
                                      {| string_val := str1 ; state_val := st |}
                                      pf)
                                (Lookup G nonterminal)
                                (lift_StringWithSplitState str (lift_lookup_nonterminal_state_eq (or_not_l pf _)))
                                (or_intror _))
                          then inl (lift_parse_nonterminal_success_eq _ _ _ _)
                          else inr (lift_parse_nonterminal_failure_eq _ _ _)
                        else (** oops, we already saw this nonterminal in the past.  ABORT! *)
                          inr (elim_parse_nonterminal_failure _ _ _)
                    else (** completely invalid grammar; nonterminal not in list of nonterminals *)
                      inr (elim_parse_nonterminal_failure_init _ _));
            try solve [ pre_eassumption; instantiate_evars; eassumption
                      | intros; destruct_head_hnf or; try assumption; exfalso; eauto with nocore
                      | intros; assumption
                      | intros; destruct str_seq_lt_false; assumption ].
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_or_abort
          : forall (p : String * nonterminals_listT)
                   (nonterminal : string)
                   (str : StringWithSplitState String (split_stateT _ _ (include_nonterminal _ nonterminal)))
                   (pf : str ≤s fst p),
              T_nonterminal (fst p) (snd p) nonterminal str
            := @Fix3
                 (prod String nonterminals_listT) _ _ _
                 _ (@well_founded_prod_relation
                      String
                      nonterminals_listT
                      _
                      _
                      (well_founded_ltof _ Length)
                      ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Definition parse_nonterminal
                     (nonterminal : string)
                     (s : String)
                     (st : split_stateT s _ (include_nonterminal _ nonterminal) s)
                     (str := {| string_val := s ; state_val := st |})
          : T_nonterminal str initial_nonterminals_data nonterminal str
            := @parse_nonterminal_or_abort
                 (str : String, initial_nonterminals_data)
                 nonterminal
                 str
                 (or_intror eq_refl).
        End wf.
      End nonterminals.
    End parts.
  End generic.
End recursive_descent_parser.

Existing Class parser_computational_strdataT.
