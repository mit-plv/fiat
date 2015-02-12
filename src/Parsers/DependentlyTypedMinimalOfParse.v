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

  Let P : string -> Prop
    := fun p => is_valid_nonterminal_name initial_nonterminal_names_data p = true.

  Let p_parse_item s it
    := { p' : parse_of_item String G s it & Forall_parse_of_item P p' }.
  Let p_parse_production s p
    := { p' : parse_of_production String G s p & Forall_parse_of_production P p' }.
  Let p_parse s prods
    := { p' : parse_of String G s prods & Forall_parse_of P p' }.
  Let p_parse_nonterminal_name s nonterminal_name
    := { p' : parse_of_item String G  s (NonTerminal _ nonterminal_name) & Forall_parse_of_item P p' }.

  Definition split_parse_of_production {str it its}
             (p : p_parse_production str (it::its))
  : { s1s2 : String * String & (fst s1s2 ++ snd s1s2 =s str)
                               * p_parse_item (fst s1s2) it
                               * p_parse_production (snd s1s2) its }%type.
  Proof.
    destruct p as [p H]; revert p H.
    pattern (it :: its).
    match goal with
      | [ |- ?P ?ls ]
        => set (prods := ls);
          change it with (hd it prods);
          change its with (tl prods);
          assert (H' : ls = prods) by reflexivity;
          clearbody prods;
          simpl
    end.
    intro p.
    destruct p.
    { exfalso; clear -H'; abstract inversion H'. }
    { intro H''.
      eexists (_, _); simpl.
      repeat split; try match goal with H : _ |- _ => exists H end.
      { apply bool_eq_correct; reflexivity. }
      { exact (fst H''). }
      { exact (snd H''). } }
  Defined.

  Local Instance methods' : @parser_computational_dataT' _ String premethods
    := {| split_stateT g s
          := option (match g return Type with
                       | include_item it => p_parse_item s it
                       | include_production p => p_parse_production s p
                       | include_productions prods => p_parse s prods
                       | include_nonterminal_name nonterminal_name => p_parse_nonterminal_name s nonterminal_name
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

  Definition parse_of__of__parse_of_item' {str nonterminal_name}
             (p : p_parse_nonterminal_name str nonterminal_name)
  : P nonterminal_name * p_parse str (Lookup G nonterminal_name).
  Proof.
    refine (match projT1 p as p' in parse_of_item _ _ str' it'
                  return match it' with
                           | Terminal _ => True
                           | NonTerminal nonterminal_name' => Forall_parse_of_item P p' -> P nonterminal_name' * p_parse str' (Lookup G nonterminal_name')
                         end
            with
              | ParseTerminal _ => I
              | ParseNonTerminal _ _ p' => fun H' => (fst H', existT _ p' (snd H'))
            end (projT2 p)).
  Defined.
  Definition parse_of__of__parse_of_item {str nonterminal_name} p
    := snd (@parse_of__of__parse_of_item' str nonterminal_name p).

  Local Instance strdata : @parser_computational_strdataT _ String G _ _
    := {| lower_nonterminal_name_state nonterminal_name str st := st;
          lower_string_head prod prods str st
          := match st with
               | None => None
               | Some p => match projT1 p as p' in parse_of _ _ str' prods' return Forall_parse_of P p' -> option (p_parse_production str' (hd prod prods')) with
                             | ParseHead _ _ _ p' => fun H => Some (existT _ p' H)
                             | ParseTail _ _ _ _ => fun _ => None
                           end (projT2 p)
             end;
          lower_string_tail prod prods str st
          := match st with
               | None => None
               | Some p => match projT1 p as p' in parse_of _ _ str' prods' return Forall_parse_of P p' -> option (p_parse str' (tl prods')) with
                             | ParseTail _ _ _ p' => fun H => Some (existT _ p' H)
                             | ParseHead _ _ _ _ => fun _ => None
                           end (projT2 p)
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
      Let alt_option valid str
        := { nonterminal_name : _ & (is_valid_nonterminal_name valid nonterminal_name = false /\ P nonterminal_name)
                                    * p_parse str (Lookup G nonterminal_name) }%type.

      Section common.
        Section types.
          Context (str0 : String)
                  (valid : nonterminal_names_listT).

          Let prefix str T := (*size_of_parse_item (ParseNonTerminal name p) < h
                         ->*) str ≤s str0
                              -> sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                              -> T.

          Section T_nonterminal_name.
            Context (name : string) (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ name))).
            Let ret := minimal_parse_of_name String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str name.

            Definition T_nonterminal_name_success  : Type
              := prefix str match state_val str with
                              | None => ret
                              | Some p => ({ p' : ret
                                                  & Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) })%type
                            end.

            Definition T_nonterminal_name_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt_option valid str
                            end.
          End T_nonterminal_name.

          Section T_item.
            Context (it : item CharType) (str : StringWithSplitState String (split_stateT it)).

            Let ret := minimal_parse_of_item String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str it.

            Definition T_item_success : Type
              := prefix str match state_val str with
                              | None => ret
                              | Some p => ({ p' : ret
                                                  & Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item p') })%type
                            end.
            Definition T_item_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt_option valid str
                            end.
          End T_item.

          Section T_production.
            Context (prod : production CharType) (str : StringWithSplitState String (split_stateT prod)).

            Let ret := minimal_parse_of_production String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str prod.

            Definition T_production_success : Type
              := prefix str match state_val str with
                              | None => ret
                              | Some p => ({ p' : ret
                                                  & Forall_parse_of_production P (parse_of_production__of__minimal_parse_of_production p') })%type
                            end.
            Definition T_production_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt_option valid str
                            end.
          End T_production.

          Section T_productions.
            Context (prods : productions CharType) (str : StringWithSplitState String (split_stateT prods)).

            Let ret := minimal_parse_of String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str prods.

            Definition T_productions_success : Type
              := prefix str match state_val str with
                              | None => ret
                              | Some p => ({ p' : ret
                                                  & Forall_parse_of P (parse_of__of__minimal_parse_of p') })%type
                            end.

            Definition T_productions_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt_option valid str
                            end.
          End T_productions.
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

        Hint Constructors minimal_parse_of minimal_parse_of_name minimal_parse_of_production minimal_parse_of_item unit prod unit : minimal_instance_db.

        Local Ltac t''0 :=
          first [ intro
                | match goal with
                    | [ H : StringWithSplitState _ _ |- _ ] => destruct H; simpl in *
                    | [ H : ?T |- _ ] => match eval hnf in T with
                                           | StringWithSplitState _ _ => destruct H; simpl in *
                                         end
                    | [ H : option _ |- _ ] => destruct H; simpl in *
                  end ].

        Local Ltac t'' :=
          idtac;
          match goal with
            | _ => intro
            | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
            | [ H : _ ≤s _ -> ?B, H' : _ |- _ ]
              => first [ specialize (H (transitivity (str_le1_append _ _ _) H'))
                       | specialize (H (transitivity (str_le2_append _ _ _) H')) ]
            | _ => progress hnf in *
            | _ => progress eauto with minimal_instance_db
            | [ H : sigT _ |- _ ] => destruct H
            | [ H : prod _ _ |- _ ] => destruct H
            | _ => progress subst
            | _ => change unit; constructor
            | _ => progress simpl in *
            | [ H : _ |- _ ] =>
              match goal with
                | [ H' : _ = H |- _ ] => destruct H'
              end
            | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
            | [ H : is_true (_ =s _) |- _ ] => apply bool_eq_correct in H
            | [ H : ?A -> False |- _ ] => let A' := (eval hnf in A) in change (A' -> False) in H
            | [ x : _ |- @sigT ?A _ ]
              => exists (MinParseNonTerminal x : A)
            | [ |- @sigT ?A _ ]
              => first [ (exists (MinParseTerminal _ _ _ _ _ _ _ _ : A))
                       | (exists (MinParseProductionNil _ _ _ _ _ _ _ : A)) ]
            | [ x : minimal_parse_of_item _ _ _ _ _ _ _ _ _, y : minimal_parse_of_production _ _ _ _ _ _ _ _ _, H : _ \/ _ |- @sigT ?A _ ]
              => exists (MinParseProductionCons H x y : A)
            | [ H : parse_of_item _ _ ?s (Terminal ?ch) |- _ ] => atomic s; inversion H
            | [ H : parse_of_production _ _ ?s []  |- _ ] => atomic s; inversion H
            | [ H : parse_of _ _ _ []  |- _ ] => exfalso; clear -H; abstract inversion H
            | _ => progress trivial
            | _ => progress auto with arith
            | [ a : _, b : Forall_parse_of_production _ _ |- Forall_parse_of_production _ _ ]
              => exact (a, b)
            | _ => t''0
            | [ |- (_ * _)%type ] => split
          end.

        (*Local Ltac should_
        Local Ltac pre_congruence_avoid_anomalies
          := repeat match goal with
                      | [ H : ?T |- _ ]*)

        Local Ltac t' :=
          first [ t''
                (*| congruence*)
                | match goal with H : true = false |- _ => exfalso; clear -H; congruence end
                | omega
                | match goal with H : (?x =s ?x) = false |- _ => erewrite (proj2 (bool_eq_correct _ _ _)) in H by reflexivity end ].

        Local Ltac t_false :=
          idtac;
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
          end.

        Local Ltac t :=
          repeat t''0;
          try solve [ exfalso; t_false
                    | repeat t''; try t_false ].

        Local Obligation Tactic := idtac.

        Start Profiling.
        Time Global Program Instance minimal_parser_dependent_types_extra_data
               (*(split_list_complete : forall str0 valid it its str pf, @split_list_completeT str0 valid valid it its str pf (split_string_for_production it its str))*)
        : @parser_dependent_types_extra_dataT _ String G.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Obligation 8. t. Defined.
        repeat t''.
        inversion x.
 Defined.
        Obligations.
        Next Obligation. Show Profile.
                         repeat t''.

                         Time match goal with

                         end.

                         exact (f2, f0).
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         subst_body.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.

                         repeat t''.
                         subst_body.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         dest
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
                         progress t''.
Time match goal with
                           .
Show

 Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Show Profile.
        Obligations.
        Next Obligation.
          repeat t''.
          subst_body; simpl in *.
          specialize (X (transitivity (str_le1_append _ _ _) H)).
          SearchAbout (_ ≤s _).
          subst_body; simpl.

          do 2 try inversion_one_head_hnf @minimal_parse_of_production.

          repeat t''.
          change unit.
          unfold parse_of_production__of__minimal_parse_of_production.
          hnf.
          unfold Forall_parse_of_production.

          constructor.
          unfold parse_of_production__of__minimal_parse_of_production.
          constructor.
        Solve Obligation 1 using t.
        Solve Obligation 2 using t.
        Solve Obligation 3 using t.
        Solve Obligation 4 using t.
        Solve Obligation 5 using t.
        Solve Obligation 6 using t.
        Solve Obligation 7 using t.
        Solve Obligation 8 using t.
        Solve Obligation 9 using t.
        Solve Obligation 10 using t.
        Solve Obligation 11 using t.
        Solve Obligation 12 using t.
        Solve Obligation 13 using t.
        Solve Obligation 14 using t.
        Solve Obligation 1 using t.
        Solve Obligation 1 using t.
        Obligations.
        Next Obligation.
          t.
          repeat t''.
          Print minimal_parse_of_production.
          exists (MinParseProductionNil _ _ _ _ _ _ _).
          exists (MinParseProductionNil _ _ _ _ _ _ _).
          exfalso.
          repeat t'.
          t''.
          t''.
          t''.
          t''.
          t''.
          t''.
          t''.
          t''.

          repeat t''.
          t'.
          exfalso; t.

          SearchAbout (?x =s _).

          t''.
          t''.


          t''.
          t''.
          t''.
          t''.
          t''.
          t''.
          t''.
          t''.

          exfalso; t.
        Defined.
        Next Obligation.
          t.
        Defined.
        Next Obligation.
          t.
        Defined.
        Next Obligation.

          t.
          repeat t''; t.
        Defined.

        Next Obligation.
          t.

          repeat t''.
          match goal with |- _ * _ => split end.
          t''.
          repeat t''.



          match goal with
            | [ H : parse_of_item _ _ ?s (Terminal ch) |- _ ] => atomic s; inversion H
          end.
          subst x.
          destruct H2.
        Defined.

          repeat t''.
          t.
          unfold T_nonterminal_name_success in *.
          t''.
          t.
          t''.
        Defined.

          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          t'.
          first [ t''
                | congruence
                | omega
                | match goal with x : _ |- _ => exists (MinParseNonTerminal x) end
                | match goal with H : (?x =s ?x) = false |- _ => erewrite (proj2 (bool_eq_correct _ _ _)) in H by reflexivity end ].
          first [ intro
                | match goal with H : ?A -> ?B, H' : ?A |- _ => specialize (H H') end
                | progress hnf in *
                | progress eauto with minimal_instance_db
                | progress destruct_head @StringWithSplitState
                | progress destruct_head option
                | progress destruct_head sigT
                | progress destruct_head prod
                | progress simpl in *
                | progress subst ].

          t'.
          t'.
          t'.

          Print minimal_parse_of_item.
          destruct x.
          unfold parse_of_item_name__of__minimal_parse_of_name' in f.
          hnf in f.
          unfold parse_of_item

          t'.

          simpl in *.

          unfold T_nonterminal_name_success
          hnf in *.

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
