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
    { split_stateT : String -> Type;
      split_string_for_production
      : forall (str0 : StringWithSplitState String split_stateT) (prod : production CharType),
          list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT);
      split_string_for_production_correct
      : forall (str0 : StringWithSplitState String split_stateT) prod,
          List.Forall (fun s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                       => (fst s1s2 ++ snd s1s2 =s str0) = true)
                      (split_string_for_production str0 prod) }.

  Class parser_computational_dataT :=
    { premethods :> parser_computational_predataT;
      methods' :> parser_computational_dataT' }.

  Section generic.
    Section parts.
      Class parser_dependent_types_dataT :=
        { methods :> parser_computational_dataT;
          T_nonterminal_name_success : forall (str0 str : StringWithSplitState String split_stateT) (valid : nonterminal_names_listT),
                             string -> Type;
          T_nonterminal_name_failure : forall (str0 str : StringWithSplitState String split_stateT) (valid : nonterminal_names_listT),
                             string -> Type;
          T_item_success : forall (str0 str : StringWithSplitState String split_stateT) (valid : nonterminal_names_listT),
                             item CharType -> Type;
          T_item_failure : forall (str0 str : StringWithSplitState String split_stateT) (valid : nonterminal_names_listT),
                             item CharType -> Type;
          T_production_success
          : forall (str0 str : StringWithSplitState String split_stateT)
                   (valid : nonterminal_names_listT)
                   (prod : production CharType),
              Type;
          T_production_failure
          : forall (str0 str : StringWithSplitState String split_stateT)
                   (valid : nonterminal_names_listT)
                   (prod : production CharType),
              Type;

          split_string_lift_T (str0 str : StringWithSplitState String split_stateT) (valid : nonterminal_names_listT) (it : item CharType) (its : production CharType)
                              (split : list
                                         (StringWithSplitState String split_stateT *
                                          StringWithSplitState String split_stateT))
          := str ≤s str0
             -> fold_right Datatypes.prod unit
                           (map (fun s1s2 =>
                                   let s1 := fst s1s2 in
                                   let s2 := snd s1s2 in
                                   ((T_item_failure str0 s1 valid it * T_production_failure str0 s2 valid its)
                                    + (T_item_success str0 s1 valid it * T_production_failure str0 s2 valid its)
                                    + (T_item_failure str0 s1 valid it * T_production_success str0 s2 valid its))%type)
                                split)
             -> T_production_failure str0 str valid (it::its);

          H_prod_split_T str0 str valid prod split :=
            match prod return Type with
              | nil => unit
              | it::its => split_string_lift_T str0 str valid it its split
            end;

          T_productions_success
          : forall (str0 str : StringWithSplitState String split_stateT)
                   (valid : nonterminal_names_listT)
                   (prods : productions CharType),
              Type;
          T_productions_failure
          : forall (str0 str : StringWithSplitState String split_stateT)
                   (valid : nonterminal_names_listT)
                   (prods : productions CharType),
              Type }.

      Class parser_dependent_types_extra_dataT :=
        { types :> parser_dependent_types_dataT;
          lift_success : forall {str0 str valid} nonterminal_name, @T_nonterminal_name_success _ str0 str valid nonterminal_name -> @T_item_success _ str0 str valid (NonTerminal _ nonterminal_name);
          lift_failure : forall {str0 str valid} nonterminal_name, @T_nonterminal_name_failure _ str0 str valid nonterminal_name -> @T_item_failure _ str0 str valid (NonTerminal _ nonterminal_name);
          parse_terminal_success : forall {str0 str : StringWithSplitState String split_stateT} {valid} ch,
                                     [[ ch ]] =s str -> @T_item_success _ str0 str valid (Terminal ch);
          parse_terminal_failure : forall {str0 str : StringWithSplitState String split_stateT} {valid}
                                          ch, ([[ ch ]] =s str) = false -> @T_item_failure _ str0 str valid (Terminal ch);
          parse_empty_success : forall {str0 str : StringWithSplitState String split_stateT} {valid}, str =s Empty _ -> T_production_success str0 str valid nil;
          parse_empty_failure : forall {str0 str : StringWithSplitState String split_stateT} {valid} (pf : str ≤s str0), (str =s Empty _) = false -> T_production_failure str0 str valid nil;
          cons_success : forall (str0 s1 s2 str : StringWithSplitState String split_stateT) {valid} (pf : str ≤s str0) (H : s1 ++ s2 =s str) it its,
                           @T_item_success _ str0 s1 valid it -> @T_production_success _ str0 s2 valid its -> @T_production_success _ str0 str valid (it :: its);

          fail_parse_nil_productions : forall {str0 str valid}, T_productions_failure str0 str valid [];
          lift_prods_success_head : forall {str0 str valid prod prods}, @T_production_success _ str0 str valid prod -> @T_productions_success _ str0 str valid (prod::prods);
          lift_prods_success_tail : forall {str0 str valid prod prods}, @T_productions_success _ str0 str valid prods -> @T_productions_success _ str0 str valid (prod::prods);
          lift_prods_failure : forall {str0 str valid prod prods}, @T_production_failure _ str0 str valid prod -> @T_productions_failure _ str0 str valid prods -> @T_productions_failure _ str0 str valid (prod::prods);

          H_prod_split : forall str0 str valid prod, H_prod_split_T str0 str valid prod (split_string_for_production str prod);

          lift_parse_nonterminal_name_success_lt : forall {str0 str : StringWithSplitState String split_stateT} {valid nonterminal_name}, Length str < Length str0 -> @T_productions_success _ str str initial_nonterminal_names_data (Lookup G nonterminal_name) -> @T_nonterminal_name_success _ str0 str valid nonterminal_name;
          lift_parse_nonterminal_name_failure_lt : forall {str0 str : StringWithSplitState String split_stateT} {valid nonterminal_name}, Length str < Length str0 -> @T_productions_failure _ str str initial_nonterminal_names_data (Lookup G nonterminal_name) -> @T_nonterminal_name_failure _ str0 str valid nonterminal_name;
          lift_parse_nonterminal_name_success_eq : forall {str0 str : StringWithSplitState String split_stateT} {valid nonterminal_name},
                                         str = str0 :> String -> is_valid_nonterminal_name valid nonterminal_name = true -> @T_productions_success _ str0 str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) -> @T_nonterminal_name_success _ str0 str valid nonterminal_name;
          lift_parse_nonterminal_name_failure_eq : forall {str0 str : StringWithSplitState String split_stateT} {valid nonterminal_name},
                                         ~Length str < Length str0 -> @T_productions_failure _ str0 str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) -> @T_nonterminal_name_failure _ str0 str valid nonterminal_name;
          elim_parse_nonterminal_name_failure : forall {str0 str : StringWithSplitState String split_stateT} {valid nonterminal_name},
                                      str ≤s str0 -> ~ Length str < Length str0 -> is_valid_nonterminal_name valid nonterminal_name = false -> @T_nonterminal_name_failure _ str0 str valid nonterminal_name
        }.

      Context `{types_data : parser_dependent_types_extra_dataT}.

      Section item.
        Context (str0 str : StringWithSplitState String split_stateT)
                (valid : nonterminal_names_listT)
                (str_matches_nonterminal_name : forall nonterminal_name, sum (T_nonterminal_name_success str0 str valid nonterminal_name) (T_nonterminal_name_failure str0 str valid nonterminal_name)).

        Let T_nonterminal_name := fun nonterminal_name => sum (T_nonterminal_name_success str0 str valid nonterminal_name) (T_nonterminal_name_failure str0 str valid nonterminal_name).
        Let T_item := fun it => sum (T_item_success str0 str valid it) (T_item_failure str0 str valid it).

        (** TODO: Use [refine] and [if] to make this less scary *)
        Definition parse_item (it : item CharType) : T_item it
          := match it as it return T_item it with
               | Terminal ch
                 => match Sumbool.sumbool_of_bool ([[ ch ]] =s str) with
                      | left pf => inl (@parse_terminal_success _ _ _ _ ch pf)
                      | right pf => inr (@parse_terminal_failure _ _ _ _ ch pf)
                    end
               | NonTerminal nonterminal_name
                 => match str_matches_nonterminal_name nonterminal_name with
                      | inl ret => inl (lift_success _ ret)
                      | inr ret => inr (lift_failure _ ret)
                    end
             end.
      End item.

      Section production_and_productions.
        Context (str0 : StringWithSplitState String split_stateT)
                (valid : nonterminal_names_listT).
        Context (parse_nonterminal_name : forall (str : StringWithSplitState String split_stateT),
                                str ≤s str0
                                -> forall nonterminal_name,
                                     sum (@T_nonterminal_name_success _ str0 str valid nonterminal_name) (@T_nonterminal_name_failure _ str0 str valid nonterminal_name)).

        Let T_production := fun str prod => sum (T_production_success str0 str valid prod) (T_production_failure str0 str valid prod).

        Let T_productions := fun str prods => sum (T_productions_success str0 str valid prods) (T_productions_failure str0 str valid prods).


        Section production.
          Section helper.
            Local Ltac left_right_t :=
              solve [ left; left_right_t
                    | right; left_right_t
                    | split; assumption ].

            Fixpoint parse_production_helper
                     (str : StringWithSplitState String split_stateT)
                     (pf : str ≤s str0)
                     (it : item CharType)
                     (its : production CharType)
                     (splits : list
                                 (StringWithSplitState String split_stateT *
                                  StringWithSplitState String split_stateT))
                     (parse_production : forall str1 : StringWithSplitState String split_stateT,
                                           str1 ≤s str0 -> T_production str1 its)
                     (H_prod_split' : H_prod_split_T str0 str valid (it::its) splits)
                     (splits_correct : List.Forall (fun s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                                                    => (fst s1s2 ++ snd s1s2 =s str) = true)
                                                   splits)
                     {struct splits}
            : T_production str (it::its).
            Proof.
              destruct splits as [ | [s1 s2] splits ]; simpl in *.
              { exact (inr (H_prod_split' pf tt)). }
              { refine (let Hs1 := _ in
                        let Hs2 := _ in
                        match (@parse_item str0 s1
                                           valid
                                           (@parse_nonterminal_name s1 Hs1)
                                           it),
                              (@parse_production s2 Hs2) with
                          | inl p_it, inl p_its => inl (@cons_success _ str0 s1 s2 _ valid pf _ _ _ _ _)
                          | inl p_it, inr p_its => parse_production_helper str pf it its splits parse_production _ _
                          | inr p_it, inl p_its => parse_production_helper str pf it its splits parse_production _ _
                          | inr p_it, inr p_its => parse_production_helper str pf it its splits parse_production _ _
                        end);
                clear parse_production_helper;
                try solve [ assumption
                          | clear -pf splits_correct;
                            abstract (
                                inversion splits_correct; subst;
                                simpl in *;
                                  etransitivity; [ | exact pf ];
                                etransitivity;
                                [
                                | right; apply bool_eq_correct; eassumption ];
                                first [ apply str_le1_append
                                      | apply str_le2_append ]
                              )
                          | clear -splits_correct;
                            abstract (inversion splits_correct; subst; assumption)
                          | (intros ? H'; apply H_prod_split'; try assumption; split; [ | exact H' ]);
                            left_right_t ]. }
            Defined.
          End helper.

          Fixpoint parse_production
                   (str : StringWithSplitState String split_stateT)
                   (pf : str ≤s str0)
                   (prod : production CharType)
                   {struct prod}
          : T_production str prod.
          Proof.
            (** TODO: [as] might not be needed *)
            refine match prod as prod return T_production str prod with
                     | nil
                       (** 0-length production, only accept empty *)
                       => match Sumbool.sumbool_of_bool (str =s Empty _) with
                            | left pf' => inl (@parse_empty_success _ str0 str valid pf')
                            | right pf' => inr (@parse_empty_failure _ str0 str valid pf pf')
                          end
                     | it::its
                       => let parse_production' := fun str pf => @parse_production str pf its in
                          @parse_production_helper
                            str pf it its
                            (split_string_for_production str (it::its))
                            parse_production'
                            (H_prod_split str0 _ valid (it::its))
                            (split_string_for_production_correct str (it::its))
                   end.
          Defined.
        End production.

        Section productions.
          Fixpoint parse_productions
                   (str : StringWithSplitState String split_stateT)
                   (pf : str ≤s str0)
                   (prods : productions CharType)
          : T_productions str prods.
          Proof.
            refine match prods as prods return T_productions str prods with
                     | nil => inr (@fail_parse_nil_productions _ str0 str valid)
                     | prod'::prods'
                       => match @parse_production str pf prod',
                                @parse_productions str pf prods' with
                            | inl prod_success, _
                              => inl (lift_prods_success_head prod_success)
                            | _, inl prods_success
                              => inl (lift_prods_success_tail prods_success)
                            | inr prod_failure, inr prods_failure
                              => inr (lift_prods_failure prod_failure prods_failure)
                          end
                   end.
          Defined.
        End productions.
      End production_and_productions.

      Section nonterminal_names.
        Let T_productions := fun str0 str valid prods => sum (T_productions_success str0 str valid prods) (T_productions_failure str0 str valid prods).

        Let T_nonterminal_name := fun str0 str valid nonterminal_name => sum (@T_nonterminal_name_success _ str0 str valid nonterminal_name) (@T_nonterminal_name_failure _ str0 str valid nonterminal_name).

        Section step.
          Context (str0 : StringWithSplitState String split_stateT)
                  (valid : nonterminal_names_listT).

          Context (parse_nonterminal_name
                   : forall (p : StringWithSplitState String split_stateT * nonterminal_names_listT),
                       prod_relation (ltof _ (fun s : StringWithSplitState _ _ => Length s)) nonterminal_names_listT_R p (str0, valid)
                       -> forall (str : StringWithSplitState String split_stateT)
                                 (pf : str ≤s fst p)
                                 (nonterminal_name : string),
                            T_nonterminal_name (fst p) str (snd p) nonterminal_name).

          Definition parse_nonterminal_name_step
                     (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (nonterminal_name : string)
          : T_nonterminal_name str0 str valid nonterminal_name.
          Proof.
            refine match lt_dec (Length str) (Length str0), Sumbool.sumbool_of_bool (is_valid_nonterminal_name valid nonterminal_name) with
                     | left pf', _ =>
                       (** [str] got smaller, so we reset the valid nonterminal_names list *)
                       match (@parse_productions
                                _
                                _
                                (@parse_nonterminal_name
                                   (str, initial_nonterminal_names_data)
                                   (or_introl pf'))
                                str
                                (or_intror eq_refl)
                                (Lookup G nonterminal_name)) with
                         | inl success => inl (@lift_parse_nonterminal_name_success_lt _ str0 str valid nonterminal_name pf' success)
                         | inr failure => inr (@lift_parse_nonterminal_name_failure_lt _ str0 str valid nonterminal_name pf' failure)
                       end
                     | right pf', left H' =>
                       (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal_name already *)
                       (** It was valid, so we can remove it *)
                       match (@parse_productions
                                _ _
                                (@parse_nonterminal_name
                                   (str0, remove_nonterminal_name valid nonterminal_name)
                                   (or_intror (conj eq_refl (@remove_nonterminal_name_dec _ _ _ H'))))
                                _
                                (or_intror eq_refl)
                                (Lookup G nonterminal_name)) with
                         | inl success => inl (@lift_parse_nonterminal_name_success_eq _ _ _ _ _ _ H' success)
                         | inr failure => inr (@lift_parse_nonterminal_name_failure_eq _ _ _ _ _ pf' failure)
                       end
                     | right pf', right pf''
                       => (** oops, we already saw this nonterminal_name in the past.  ABORT! *)
                         inr (@elim_parse_nonterminal_name_failure _ _ _ _ _ pf pf' pf'')
                   end;
            try solve [ destruct_head_hnf or; try assumption; exfalso; eauto with nocore ].
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_name_or_abort
          : forall (p : StringWithSplitState String split_stateT * nonterminal_names_listT) (str : StringWithSplitState String split_stateT)
                   (pf : str ≤s fst p)
                   (nonterminal_name : string),
              T_nonterminal_name (fst p) str (snd p) nonterminal_name
            := @Fix3
                 (prod (StringWithSplitState String split_stateT) nonterminal_names_listT) _ _ _
                 _ (@well_founded_prod_relation
                      (StringWithSplitState String split_stateT)
                      nonterminal_names_listT
                      _
                      _
                      (well_founded_ltof _ (fun s : StringWithSplitState String split_stateT => Length s))
                      ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_name_step (fst sl) (snd sl)).

          Definition parse_nonterminal_name (str : StringWithSplitState String split_stateT) (nonterminal_name : string)
          : T_nonterminal_name str str initial_nonterminal_names_data nonterminal_name
            := @parse_nonterminal_name_or_abort (str, initial_nonterminal_names_data) str
                                    (or_intror eq_refl) nonterminal_name.
        End wf.
      End nonterminal_names.
    End parts.
  End generic.
End recursive_descent_parser.
