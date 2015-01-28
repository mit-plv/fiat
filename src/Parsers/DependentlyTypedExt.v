(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.DependentlyTyped.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Definition bool_of_sum {A B} (x : A + B) : bool := if x then true else false.
Local Coercion bool_of_sum : sum >-> bool.

Section recursive_descent_parser.
  Context (CharType : Type)
          (String : string_like CharType)
          (G : grammar CharType).

  Local Ltac t' :=
    idtac;
    match goal with
      | _ => reflexivity
      | _ => progress subst
      | _ => progress destruct_head @StringWithSplitState
      | _ => progress simpl in *
      | [ H : inl _ = inr _ |- _ ] => solve [ inversion H ]
      | [ H : inr _ = inl _ |- _ ] => solve [ inversion H ]
      | [ H : true = false |- _ ] => solve [ inversion H ]
      | [ H : false = true |- _ ] => solve [ inversion H ]
      | [ H : inl _ = inl _ |- _ ] => inversion H; clear H
      | [ H : inr _ = inr _ |- _ ] => inversion H; clear H
      | [ H : ?f _ = ?x, H' : ?f' _ = ?y, ext : forall k, bool_of_sum (?f k) = bool_of_sum (?f' k) |- _]
        => assert (x = y :> bool) by (rewrite <- H, <- H', ext; reflexivity); clear H H'
      | [ H : (?x =s ?y) = true |- _ ]
        => not constr_eq x y;
          let H' := fresh in
          pose proof H as H';
            apply bool_eq_correct in H';
            progress subst
      | [ |- appcontext[match ?E with _ => _ end] ]
        => case_eq E
      | _ => intro
    end.

  Local Ltac t := repeat t'.

  Lemma parse_item_ext
        (extra_types extra_types' : @parser_dependent_types_extra_dataT _ _ G)
        str0 str valid str_matches_name
        str0' str' valid' str_matches_name'
        (it : item CharType)
        (pi := @parse_item CharType String G extra_types str0 str valid str_matches_name it)
        (pi' := @parse_item CharType String G extra_types' str0' str' valid' str_matches_name' it)
        (str_ext : str = str' :> String)
        (str_matches_name_ext : forall name, str_matches_name name = str_matches_name' name :> bool)
  : pi = pi' :> bool.
  Proof.
    subst pi pi'.
    unfold parse_item.
    t.
  Qed.

  Lemma parse_production_helper_ext

                     (str : StringWithSplitState String split_stateT)
                     (pf : str ≤s str0)
                     (it : item CharType)
                     (its : production CharType)
                     (splits : list
                                 (StringWithSplitState String split_stateT *
                                  StringWithSplitState String split_stateT))
                     (parse_production : forall str1 : StringWithSplitState String split_stateT,
                                           str1 ≤s str0 -> T_production str1 its)
                     (H_prod_split' : H_prod_split_T str0 str valid (it::its) (fun _ => splits))
                     (splits_correct : List.Forall (fun s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                                                    => (fst s1s2 ++ snd s1s2 =s str) = true)
                                                   splits)


        (methods methods' : parser_computational_dataT String)
        (types : @parser_dependent_types_dataT _ _ G methods)
        (types' : @parser_dependent_types_dataT _ _ G methods')
        str0 str valid str_matches_name
        str0' str' valid' str_matches_name'
        (it : item CharType)
        (pi := @parse_item CharType String G methods types str0 str valid str_matches_name it)
        (pi' := @parse_item CharType String G methods' types' str0' str' valid' str_matches_name' it)
        (str_ext : str = str' :> String)
        (str_matches_name_ext : forall name, str_matches_name name = str_matches_name' name :> bool)
  : pi = pi' :> bool.
  Proof.

  Section generic.
    Section parts.
      Context `{types : parser_dependent_types_dataT}.

      Section item.
        Context (str0 str : StringWithSplitState String split_stateT)
                (valid : names_listT)
                (str_matches_name : forall name, sum (T_name_success str0 str valid name) (T_name_failure str0 str valid name)).

        Let T_name := fun name => sum (T_name_success str0 str valid name) (T_name_failure str0 str valid name).
        Let T_item := fun it => sum (T_item_success str0 str valid it) (T_item_failure str0 str valid it).

        Definition parse_item (it : item CharType) : T_item it
          := match it as it return T_item it with
               | Terminal ch
                 => match Sumbool.sumbool_of_bool ([[ ch ]] =s str) with
                      | left pf => inl (@parse_terminal_success _ _ _ _ ch pf)
                      | right pf => inr (@parse_terminal_failure _ _ _ _ ch pf)
                    end
               | NonTerminal name
                 => match str_matches_name name with
                      | inl ret => inl (lift_success _ ret)
                      | inr ret => inr (lift_failure _ ret)
                    end
             end.
      End item.

      Section production_and_productions.
        Context (str0 : StringWithSplitState String split_stateT)
                (valid : names_listT).
        Context (parse_name : forall (str : StringWithSplitState String split_stateT),
                                str ≤s str0
                                -> forall name,
                                     sum (@T_name_success _ str0 str valid name) (@T_name_failure _ str0 str valid name)).

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
                     (H_prod_split' : H_prod_split_T str0 str valid (it::its) (fun _ => splits))
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
                                           (@parse_name s1 Hs1)
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

      Section names.
        Let T_productions := fun str0 str valid prods => sum (T_productions_success str0 str valid prods) (T_productions_failure str0 str valid prods).

        Let T_name := fun str0 str valid name => sum (@T_name_success _ str0 str valid name) (@T_name_failure _ str0 str valid name).

        Section step.
          Context (str0 : StringWithSplitState String split_stateT)
                  (valid : names_listT).

          Context (parse_name
                   : forall (p : StringWithSplitState String split_stateT * names_listT),
                       prod_relation (ltof _ (fun s : StringWithSplitState _ _ => Length s)) names_listT_R p (str0, valid)
                       -> forall (str : StringWithSplitState String split_stateT)
                                 (pf : str ≤s fst p)
                                 (name : string),
                            T_name (fst p) str (snd p) name).

          Definition parse_name_step
                     (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (name : string)
          : T_name str0 str valid name.
          Proof.
            refine match lt_dec (Length str) (Length str0), Sumbool.sumbool_of_bool (is_valid_name valid name) with
                     | left pf', _ =>
                       (** [str] got smaller, so we reset the valid names list *)
                       match (@parse_productions
                                _
                                _
                                (@parse_name
                                   (str, initial_names_data)
                                   (or_introl pf'))
                                str
                                (or_intror eq_refl)
                                (Lookup G name)) with
                         | inl success => inl (@lift_parse_name_success_lt _ str0 str valid name pf' success)
                         | inr failure => inr (@lift_parse_name_failure_lt _ str0 str valid name pf' failure)
                       end
                     | right pf', left H' =>
                       (** [str] didn't get smaller, so we cache the fact that we've hit this name already *)
                       (** It was valid, so we can remove it *)
                       match (@parse_productions
                                _ _
                                (@parse_name
                                   (str0, remove_name valid name)
                                   (or_intror (conj eq_refl (@remove_name_dec _ _ _ H'))))
                                _
                                (or_intror eq_refl)
                                (Lookup G name)) with
                         | inl success => inl (@lift_parse_name_success_eq _ _ _ _ _ _ H' success)
                         | inr failure => inr (@lift_parse_name_failure_eq _ _ _ _ _ pf' failure)
                       end
                     | right pf', right pf''
                       => (** oops, we already saw this name in the past.  ABORT! *)
                         inr (@elim_parse_name_failure _ _ _ _ _ pf pf' pf'')
                   end;
            try solve [ destruct_head_hnf or; try assumption; exfalso; eauto with nocore ].
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_name_or_abort
          : forall (p : StringWithSplitState String split_stateT * names_listT) (str : StringWithSplitState String split_stateT)
                   (pf : str ≤s fst p)
                   (name : string),
              T_name (fst p) str (snd p) name
            := @Fix3
                 (prod (StringWithSplitState String split_stateT) names_listT) _ _ _
                 _ (@well_founded_prod_relation
                      (StringWithSplitState String split_stateT)
                      names_listT
                      _
                      _
                      (well_founded_ltof _ (fun s : StringWithSplitState String split_stateT => Length s))
                      ntl_wf)
                 _
                 (fun sl => @parse_name_step (fst sl) (snd sl)).

          Definition parse_name (str : StringWithSplitState String split_stateT) (name : string)
          : T_name str str initial_names_data name
            := @parse_name_or_abort (str, initial_names_data) str
                                    (or_intror eq_refl) name.
        End wf.
      End names.
    End parts.
  End generic.
End recursive_descent_parser.
