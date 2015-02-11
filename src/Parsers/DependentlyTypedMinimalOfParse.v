(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.DependentlyTyped Parsers.MinimalParse.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context (CharType : Type)
          (String : string_like CharType)
          (G : grammar CharType).
  Context {premethods : parser_computational_predataT}.
  Variable orig_methods : @parser_computational_dataT' CharType String premethods.
  Variable gen_state : forall (prod : production CharType) s, split_stateT prod s.

  Definition split_parse_of_production {str it its} (p : parse_of_production String G str (it::its))
  : { s1s2 : String * String & (fst s1s2 ++ snd s1s2 =s str)
                               * parse_of_item String G (fst s1s2) it
                               * parse_of_production String G (snd s1s2) its }%type.
  Proof.
    inversion p; subst.
    eexists (_, _); simpl.
    repeat esplit; try eassumption.
    apply bool_eq_correct; reflexivity.
  Defined.

  Local Instance methods' : @parser_computational_dataT' _ String premethods
    := {| split_stateT g s
          := option (match g return Type with
                       | include_item it => parse_of_item String G s it
                       | include_production p => parse_of_production String G s p
                       | include_productions prods => parse_of String G s prods
                       | include_nonterminal_name nonterminal_name => parse_of_item String G  s (NonTerminal _ nonterminal_name)
                     end);
          split_string_for_production it its s
          := let orig_splits := map (fun s1s2 =>
                                       ({| string_val := string_val (fst s1s2);
                                           state_val := None |},
                                        {| string_val := string_val (snd s1s2);
                                           state_val := None |}))
                                    (@split_string_for_production _ _ _ orig_methods it its {| state_val := (gen_state (it::its) (string_val s)) |}) in
             match state_val s with
               | None => orig_splits
               | Some st => let st' := split_parse_of_production st in
                            ({| string_val := fst (projT1 st') ; state_val := Some (snd (fst (projT2 st'))) |},
                             {| string_val := snd (projT1 st') ; state_val := Some (snd (projT2 st')) |})::nil
             end |}.
  Proof.
    intros; subst_body; simpl in *.
    abstract (
        destruct_head @StringWithSplitState;
        destruct_head option;
        repeat match goal with
                 | _ => progress simpl in *
                 | _ => progress unfold compose
                 | [ |- Forall _ (?f _ _ _) ] => unfold f
                 | [ |- Forall _ nil ] => constructor
                 | [ |- Forall _ (_::_) ] => constructor
                 | [ |- Forall _ (map _ _) ] => apply Forall_map
                 | _ => refine (split_string_for_production_correct _ _ {| state_val := _ |})
                 | _ => exact (fst (fst (projT2 (split_parse_of_production _))))
               end
      ).
  Defined.

  Definition parse_of__of__parse_of_item {str nonterminal_name}
             (p : parse_of_item String G str (NonTerminal CharType nonterminal_name))
  : parse_of String G str (Lookup G nonterminal_name).
  Proof.
    inversion_clear p; assumption.
  Defined.

  Local Instance strdata : @parser_computational_strdataT _ String G _ _
    := {| lower_nonterminal_name_state nonterminal_name str st := st;
          lower_string_head prod prods str st
          := match st with
               | None => None
               | Some p => match p in parse_of _ _ str' prods' return option (parse_of_production _ _ str' (hd prod prods')) with
                             | ParseHead _ _ _ p' => Some p'
                             | ParseTail _ _ _ _ => None
                           end
             end;
          lower_string_tail prod prods str st
          := match st with
               | None => None
               | Some p => match p in parse_of _ _ str' prods' return option (parse_of _ _ str' (tl prods')) with
                             | ParseTail _ _ _ p' => Some p'
                             | ParseHead _ _ _ _ => None
                           end
             end;
          lift_lookup_nonterminal_name_state nonterminal_name str := option_map parse_of__of__parse_of_item |}.

  Section minimal.
    Local Ltac t' :=
      idtac;
      match goal with
        | _ => intro
        | _ => progress hnf in *
        | _ => progress simpl in *
        | _ => progress subst_body
        | _ => progress subst
        | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
        | [ H : ?A -> ?B |- _ ] => let A' := (eval hnf in A) in
                                   progress change (A' -> B) in H
        | _ => progress destruct_head StringWithSplitState
        | _ => progress destruct_head False
        | [ H : context[?x =s ?x] |- _ ]
          => rewrite (proj2 (bool_eq_correct _ x x) eq_refl) in H
        | [ H : true = false |- _ ] => exfalso; discriminate
        | _ => progress inversion_head @minimal_parse_of_item
        | _ => progress inversion_head @minimal_parse_of_production
      end.

    Section parts.
      Let P : string -> Prop
        := fun p => is_valid_nonterminal_name initial_nonterminal_names_data p = true.

      Let alt_option h valid str
        := { nonterminal_name : _ & (is_valid_nonterminal_name valid nonterminal_name = false /\ P nonterminal_name)
                                    * { p : parse_of String G str (Lookup G nonterminal_name)
                                            & (size_of_parse p < h)
                                              * Forall_parse_of P p } }%type.

      Section common.
        Section types.
          Context (str0 : String)
                  (valid : nonterminal_names_listT).

          Definition T_nonterminal_name_success (name : string) (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ name))) : Type
            := let ret := minimal_parse_of_name String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str name in
               match state_val str with
                 | None => ret
                 | Some p =>
                   (*size_of_parse_item (ParseNonTerminal name p) < h
                         ->*) str ≤s str0
                              -> sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                              -> Forall_parse_of_item P p
                              -> ({ p' : ret
                                         & (size_of_parse_item (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) <= size_of_parse_item p)
                                           * Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) })%type
               end.

          Definition T_nonterminal_name_failure (name : string) str : Type
            := match state_val str with
                 | None => @T_nonterminal_name_success name str -> False
                 | Some p =>
                   (*size_of_parse_item (ParseNonTerminal name p) < h
                         ->*) str ≤s str0
                              -> sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                              -> Forall_parse_of_item P p
                              -> alt_option (size_of_parse_item p) valid str
               end.

          Definition T_item_success (it : item CharType) (str : StringWithSplitState String (split_stateT it)) : Type
            := let ret := minimal_parse_of_item String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str it in
               match state_val str with
                 | None => ret
                 | Some p =>
                   (*size_of_parse_item (ParseNonTerminal name p) < h
                         ->*) str ≤s str0
                              -> sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                              -> Forall_parse_of_item P p
                              -> ({ p' : ret
                                         & (size_of_parse_item (parse_of_item__of__minimal_parse_of_item p') <= size_of_parse_item p)
                                           * Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item p') })%type
               end.
          Definition T_item_failure (it : item CharType) str : Type
            := match state_val str with
                 | None => @T_item_success it str -> False
                 | Some p =>
                   (*size_of_parse_item (ParseNonTerminal name p) < h
                         ->*) str ≤s str0
                              -> sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                              -> Forall_parse_of_item P p
                              -> alt_option (size_of_parse_item p) valid str
               end.

          Definition T_production_success (prod : production CharType) (str : StringWithSplitState String (split_stateT prod)) : Type
            := let ret := minimal_parse_of_production String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str prod in
               match state_val str with
                 | None => ret
                 | Some p =>
                   (*forall (p_small : size_of_parse_production p < h),*)
                   sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                   -> Forall_parse_of_production P p
                   -> ({ p' : ret
                              & (size_of_parse_production (parse_of_production__of__minimal_parse_of_production p') <= size_of_parse_production p)
                                * Forall_parse_of_production P (parse_of_production__of__minimal_parse_of_production p') })%type
               end.

          Definition T_production_failure (prod : production CharType) str : Type
            := match state_val str with
                 | None => @T_production_success prod str -> False
                 | Some p =>
                   (*forall (p_small : size_of_parse_production p < h),*)
                   sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                   -> Forall_parse_of_production P p
                   -> alt_option (size_of_parse_production p) valid str
               end.

          Definition T_productions_success (prods : productions CharType) (str : StringWithSplitState String (split_stateT prods)) : Type
            := let ret := minimal_parse_of String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str prods in
               match state_val str with
                 | None => ret
                 | Some p =>
                   (*forall (p_small : size_of_parse p < h),*)
                   sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                   -> Forall_parse_of P p
                   -> ({ p' : ret
                              & (size_of_parse (parse_of__of__minimal_parse_of p') <= size_of_parse p)
                                * Forall_parse_of P (parse_of__of__minimal_parse_of p') })%type
               end.

          Definition T_productions_failure (prods : productions CharType) str : Type
            := match state_val str with
                 | None => @T_productions_success prods str -> False
                 | Some p =>
                   (*forall (p_small : size_of_parse p < h),*)
                   sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                   -> Forall_parse_of P p
                   -> alt_option (size_of_parse p) valid str
               end.
        End types.

        Global Instance minimal_parser_dependent_types_data
        : @parser_dependent_types_dataT _ String
          := {| methods := Build_parser_computational_dataT methods';
                T_nonterminal_name_success := T_nonterminal_name_success;
                T_nonterminal_name_failure := T_nonterminal_name_failure;
                T_item_success := T_item_success;
                T_item_failure := T_item_failure;
                T_production_success := T_production_success;
                T_production_failure := T_production_failure;
                T_productions_success := T_productions_success;
                T_productions_failure := T_productions_failure |}.


        (*Definition split_list_completeT
                   (str0 : String)
                   valid1 valid2
                   (it : item CharType) (its : production CharType)
                   (str : StringWithSplitState String (split_stateT (it::its : production CharType)))
                   (pf : str ≤s str0)
                   (split_list : list (StringWithSplitState String (split_stateT it) * StringWithSplitState String (split_stateT its)))
          := ({ s1s2 : String * String
                       & (fst s1s2 ++ snd s1s2 =s str)
                         * (minimal_parse_of_item _ G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid1 (fst s1s2) it)
                         * (minimal_parse_of_production _ G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid2 (snd s1s2) its) }%type)
             -> ({ s1s2 : _
                          & (In s1s2 split_list)
                            * (minimal_parse_of_item _ G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid1 (fst s1s2) it)
                            * (minimal_parse_of_production _ G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid2 (snd s1s2) its) }%type).

        Lemma H_prod_split'_helper
              (str0 : String)
              (valid : nonterminal_names_listT)
              (it : item CharType) (its : production CharType)
              (str : StringWithSplitState String (split_stateT it))
              (strs : StringWithSplitState String (split_stateT its))
              (p_it : minimal_parse_of_item String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str it)
              (p_its : minimal_parse_of_production String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid strs its)
              (ls : list
                      (StringWithSplitState String (split_stateT it) *
                       StringWithSplitState String (split_stateT its)))
              (Hin : In (str, strs) ls)
              (H : fold_right
                     Datatypes.prod
                     unit
                     (map
                        (fun s1s2 =>
                           let s1 := fst s1s2 in
                           let s2 := snd s1s2 in
                           ((@T_item_failure str0 valid it s1 * @T_production_failure str0 valid its s2)
                            + (@T_item_success str0 valid it s1 * @T_production_failure str0 valid its s2)
                            + (@T_item_failure str0 valid it s1 * @T_production_success str0 valid its s2))%type)
                        ls))
        : False.
        Proof.
          induction ls; simpl in *; trivial; [].
          destruct_head or; subst;
          destruct_head prod; eauto; [].
          destruct_head sum; destruct_head prod;
          unfold T_item_failure, T_item_success, T_production_failure, T_production_success in *;
          eauto.
        Qed.

        Definition H_prod_split'
                   (str0 : String)
                   (valid : nonterminal_names_listT)
                   it its
                   (str : StringWithSplitState String (split_stateT (it::its : production CharType)))
                   pf
                   (split_list_complete : @split_list_completeT str0 valid valid it its str pf (split_string_for_production it its str))
        : @split_string_lift_T _ String _ str0 valid it its str (split_string_for_production it its str).
        Proof.
          clear -split_list_complete.
          intros H pf' H'; hnf in H', split_list_complete.
          destruct str as [str st]; simpl in *.
          inversion H'; clear H'; subst.
          specialize (fun s1 s2 b
                      => split_list_complete
                           (existT _ (s1, s2) b));
            simpl in *.
          let p_it := hyp_with_head @minimal_parse_of_item in
          let p_its := hyp_with_head @minimal_parse_of_production in
          specialize (fun pf => split_list_complete _ _ (pf, p_it, p_its)).
          repeat match goal with
                   | [ H : ?T -> ?A |- _ ]
                     => let H' := fresh in
                        assert (H' : T) by (apply bool_eq_correct; reflexivity);
                          specialize (H H'); clear H'
                   | _ => progress destruct_sig
                   | _ => progress destruct_head option
                   | _ => progress destruct_head or
                   | _ => progress destruct_head False
                   | _ => progress subst
                   | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
                 end.
          { eapply H_prod_split'_helper; try eassumption;
            try match goal with H : _ |- _ => exact H end;
            try instantiate (1 := [(_, _)]);
            [ left; reflexivity | split; assumption ]. }
          { eapply H_prod_split'_helper; try eassumption;
            try match goal with H : _ |- _ => exact H end. }
        Qed.*)

        Hint Constructors minimal_parse_of minimal_parse_of_name minimal_parse_of_production minimal_parse_of_item unit : minimal_instance_db.

        Local Ltac t'' :=
          first [ intro
                | progress hnf in *
                | progress eauto with minimal_instance_db
                | progress destruct_head @StringWithSplitState
                | progress simpl in *
                | progress subst
                | match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end ].

        Local Ltac t' :=
          first [ t''
                | congruence
                | omega
                | match goal with H : (?x =s ?x) = false |- _ => erewrite (proj2 (bool_eq_correct _ _ _)) in H by reflexivity end ].

        Local Ltac t :=
          repeat intro;
          match goal with
            | [ |- False ]
              => abstract (
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of_name;
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of_item;
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of_production;
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of;
                     repeat t'
                   )
            | _ => try solve [ repeat t'' ]
          end.

        Local Obligation Tactic := t.

        Global Program Instance minimal_parser_dependent_types_extra_data
               (*(split_list_complete : forall str0 valid it its str pf, @split_list_completeT str0 valid valid it its str pf (split_string_for_production it its str))*)
        : @parser_dependent_types_extra_dataT _ String G.
        Next Obligation.

          eapply H_prod_split'; eauto.
          Grab Existential Variables.
          assumption.
        Defined.
      End common.

      Definition minimal_parse_nonterminal_name
                 (split_list_complete
                  : forall str0 valid it its str pf,
                      @split_list_completeT str0 valid valid it its str pf (split_string_for_production it its str))
      : forall (nonterminal_name : string)
               (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ nonterminal_name))),
          sum (T_nonterminal_name_success str initial_nonterminal_names_data nonterminal_name str)
              (T_nonterminal_name_failure str initial_nonterminal_names_data nonterminal_name str)
        := @parse_nonterminal_name _ String G (minimal_parser_dependent_types_extra_data split_list_complete).
    End parts.
  End minimal.
End recursive_descent_parser.
    Section parts.
      Section common.
        Section types.
          Context (str0 : String)
                  (valid : nonterminal_names_listT).

          Definition T_name_success  (name : string) : Type
            := minimal_parse_of_name String G initial_names_data is_valid_name remove_name
                                     str0 valid str name.
          Definition T_name_failure (name : string) : Type
            := T_name_success name -> False.

          Definition T_item_success (it : item CharType) : Type
            := minimal_parse_of_item String G initial_names_data is_valid_name remove_name
                                     str0 valid str it.
          Definition T_item_failure (it : item CharType) : Type
            := T_item_success it -> False.

          Definition T_production_success (prod : production CharType) : Type
            := minimal_parse_of_production String G initial_names_data is_valid_name remove_name
                                           str0 valid str prod.

          Definition T_production_failure (prod : production CharType) : Type
            := T_production_success prod -> False.

          Definition T_productions_success (prods : productions CharType) : Type
            := minimal_parse_of String G initial_names_data is_valid_name remove_name
                                str0 valid str prods.

          Definition T_productions_failure (prods : productions CharType) : Type
            := T_productions_success prods -> False.
        End types.

        Global Instance minimal_parser_dependent_types_data
        : @parser_dependent_types_dataT _ String
          := {| T_name_success := T_name_success;
                T_name_failure := T_name_failure;
                T_item_success := T_item_success;
                T_item_failure := T_item_failure;
                T_production_success := T_production_success;
                T_production_failure := T_production_failure;
                T_productions_success := T_productions_success;
                T_productions_failure := T_productions_failure |}.


        Definition split_list_completeT
                   (str0 : StringWithSplitState String split_stateT)
                   valid1 valid2
                   (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                   (split_list : list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
                   (prod : production CharType)
          := match prod return Type with
               | nil => True
               | it::its => ({ s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                                      & (fst s1s2 ++ snd s1s2 =s str)
                                        * (minimal_parse_of_item _ G initial_names_data is_valid_name remove_name str0 valid1 (fst s1s2) it)
                                        * (minimal_parse_of_production _ G initial_names_data is_valid_name remove_name str0 valid2 (snd s1s2) its) }%type)
                            -> ({ s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                                         & (In s1s2 split_list)
                                           * (minimal_parse_of_item _ G initial_names_data is_valid_name remove_name str0 valid1 (fst s1s2) it)
                                           * (minimal_parse_of_production _ G initial_names_data is_valid_name remove_name str0 valid2 (snd s1s2) its) }%type)
             end.

        Lemma H_prod_split'_helper
              (str0 : StringWithSplitState String split_stateT)
              (valid : names_listT)
              (it : item CharType) (its : list (item CharType))
              (str strs : StringWithSplitState String split_stateT)
              (p_it : minimal_parse_of_item String G initial_names_data is_valid_name remove_name str0 valid str it)
              (p_its : minimal_parse_of_production String G initial_names_data is_valid_name remove_name str0 valid strs its)
              (ls : list
                      (StringWithSplitState String split_stateT *
                       StringWithSplitState String split_stateT))
              (Hin : In (str, strs) ls)
              (H : fold_right
                     Datatypes.prod
                     unit
                     (map
                        (fun s1s2 =>
                           let s1 := fst s1s2 in
                           let s2 := snd s1s2 in
                           ((@T_item_failure str0 s1 valid it * @T_production_failure str0 s2 valid its)
                            + (@T_item_success str0 s1 valid it * @T_production_failure str0 s2 valid its)
                            + (@T_item_failure str0 s1 valid it * @T_production_success str0 s2 valid its))%type)
                        ls))
        : False.
        Proof.
          induction ls; simpl in *; trivial; [].
          destruct_head or; subst;
          destruct_head prod; eauto; [].
          destruct_head sum; destruct_head prod;
          unfold T_item_failure, T_item_success, T_production_failure, T_production_success in *;
          eauto.
        Qed.

        Definition H_prod_split'
                   (str0 str : StringWithSplitState String split_stateT)
                   (valid : names_listT)
                   pf it its
                   (split_list_complete : @split_list_completeT str0 valid valid str pf (split_string_for_production str (it::its)) (it::its))
        : @split_string_lift_T _ String _ str0 str valid it its (split_string_for_production str).
        Proof.
          clear -split_list_complete.
          intros H pf' H'; hnf in H', split_list_complete.
          destruct str as [str st]; simpl in *.
          inversion H'; clear H'; subst.
          specialize (fun s1 s2 b
                      => split_list_complete
                           (existT _ ({| string_val := s1 ; state_val := st |},
                                      {| string_val := s2 ; state_val := st |})
                                   b)); simpl in *.
          let p_it := hyp_with_head @minimal_parse_of_item in
          let p_its := hyp_with_head @minimal_parse_of_production in
          specialize (fun pf => split_list_complete _ _ (pf, p_it, p_its)).
          repeat match goal with
                   | [ H : ?T -> ?A |- _ ]
                     => let H' := fresh in
                        assert (H' : T) by (apply bool_eq_correct; reflexivity);
                          specialize (H H'); clear H'
                   | _ => progress destruct_sig
                 end.
          eapply H_prod_split'_helper; eassumption.
        Qed.

        Definition H_prod_split''
                   (str0 str : StringWithSplitState String split_stateT)
                   (valid : names_listT)
                   prod
                   (split_list_complete : forall pf, @split_list_completeT str0 valid valid str pf (split_string_for_production str prod) prod)
        : match prod return Type with
            | nil => unit
            | it::its => @split_string_lift_T _ String _ str0 str valid it its (split_string_for_production str)
          end.
        Proof.
          unfold split_string_lift_T.
          destruct prod.
          { constructor. }
          { intro pf. apply H_prod_split' with (pf := pf); try apply split_list_complete; assumption. }
        Defined.

        Hint Constructors minimal_parse_of minimal_parse_of_name minimal_parse_of_production minimal_parse_of_item unit : minimal_instance_db.

        Local Ltac t'' :=
          first [ intro
                | progress hnf in *
                | progress eauto with minimal_instance_db
                | progress destruct_head @StringWithSplitState
                | progress simpl in *
                | progress subst
                | match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end ].

        Local Ltac t' :=
          first [ t''
                | congruence
                | omega
                | match goal with H : (?x =s ?x) = false |- _ => erewrite (proj2 (bool_eq_correct _ _ _)) in H by reflexivity end ].

        Local Ltac t :=
          repeat intro;
          match goal with
            | [ |- False ]
              => abstract (
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of_name;
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of_item;
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of_production;
                     repeat t';
                     do 2 try inversion_one_head_hnf @minimal_parse_of;
                     repeat t'
                   )
            | _ => try solve [ repeat t'' ]
          end.

        Local Obligation Tactic := t.

        Global Program Instance minimal_parser_dependent_types_extra_data
                (split_list_complete : forall str0 str valid prod pf, @split_list_completeT str0 valid valid str pf (split_string_for_production str prod) prod)
        : @parser_dependent_types_extra_dataT _ String G.
        Next Obligation.
          hnf; apply H_prod_split''.
          eauto.
        Defined.
      End common.

      Definition minimal_parse_name
                 (split_list_complete
                  : forall str0 str valid prod pf,
                      @split_list_completeT str0 valid valid str pf (split_string_for_production str prod) prod)
      : forall (str : StringWithSplitState String split_stateT)
               (name : string),
          sum (T_name_success str str initial_names_data name)
              (T_name_failure str str initial_names_data name)
        := @parse_name _ String G (minimal_parser_dependent_types_extra_data split_list_complete).
    End parts.
  End minimal.
End recursive_descent_parser.
