(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.DependentlyTyped.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
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
  Variable gen_state : forall str0 valid (prod : production CharType) s, split_stateT str0 valid prod s.

  Variable top_methods' : @parser_computational_dataT' _ String _.
  Definition leaf_methods' : @parser_computational_dataT' _ String _
    := @methods' _ _ (@methods _ _ (@types _ _ _ leaves_extra_data)).

  (** some helper lemmas to help Coq with inference *)
  Definition split_string_for_production_correct'
             H0 H1 str0 valid it its str st
    := @split_string_for_production_correct CharType String H0 H1 str0 valid it its {| string_val := str ; state_val := st |}.

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

  Local Instance methods' : @parser_computational_dataT' _ String premethods
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

  Check @parser_computational_strdataT.

  Definition top_methods : @parser_computational_dataT _ String
    := {| DependentlyTyped.methods' := top_methods' |}.
  Definition leaf_methods : @parser_computational_dataT _ String
    := @methods _ _ (@types _ _ _ leaves_extra_data).

  Record top_strdataT :=
    { top_lower_nonterminal_name_state
      : forall {str0 valid nonterminal_name s},
          @split_stateT _ _ _ top_methods' str0 valid (NonTerminal _ nonterminal_name) s -> option (@split_stateT _ _ _ top_methods' str0 valid (include_nonterminal_name _ nonterminal_name) s);

      top_lower_string_head
      : forall {str0 valid}
               {prod : production CharType}
               {prods : productions CharType}
               {s},
          @split_stateT _ _ _ top_methods' str0 valid (prod::prods : productions CharType) s -> option (@split_stateT _ _ _ top_methods' str0 valid prod s);
      top_lower_string_tail
      : forall {str0 valid}
               {prod : production CharType}
               {prods : productions CharType}
               {s},
          @split_stateT _ _ _ top_methods' str0 valid (prod::prods : productions CharType) s -> option (@split_stateT _ _ _ top_methods' str0 valid prods s);

      top_lift_lookup_nonterminal_name_state_lt
      : forall {str0 valid nonterminal_name s} (pf : Length s < Length str0),
          @split_stateT _ _ _ top_methods' str0 valid (include_nonterminal_name _ nonterminal_name) s -> @split_stateT _ _ _ top_methods' s initial_nonterminal_names_data (Lookup G nonterminal_name) s;

      lift_lookup_nonterminal_name_state_eq
      : forall {str0 valid nonterminal_name s}
               (pf : s = str0 :> String),
          split_stateT str0 valid (include_nonterminal_name _ nonterminal_name) s -> split_stateT str0 (remove_nonterminal_name valid nonterminal_name) (Lookup G nonterminal_name) s }.

  Variable top_strdata : @parser_computational_strdataT _ String G top_methods.
  Definition leaf_strdata : @parser_computational_strdataT _ String G leaf_methods
    := @strdata _ _ _ leaves_extra_data.

  Local Instance methods : parser_computational_dataT := { methods' := methods' }.

Definition functor_sum {A A' B B'} (f : A -> A') (g : B -> B') (x : sum A B) : sum A' B' :=
  match x with
    | inl a => inl (f a)
    | inr b => inr (g b)
  end.

  Local Instance strdata : @parser_computational_strdataT _ String G methods
    := { lower_nonterminal_name_state str0 valid nonterminal_name str
         := functor_sum
              (@lower_nonterminal_name_state _ _ _ _ top_strdata _ _ _ _)
              (@lower_nonterminal_name_state _ _ _ _ leaf_strdata _ _ _ _) }.
         (lower_nonterminal_name_state str0 valid nonterminal_name str) }.
                                                                         ;
          lower_string_head str0 valid prod prods str st
          := match st with
               | None => None
               | Some p => match projT1 p as p' in parse_of _ _ str' prods' return Forall_parse_of (P str0 valid) p' -> option (p_parse_production str0 valid str' (hd prod prods')) with
                             | ParseHead _ _ _ p' => fun H => Some (existT _ p' H)
                             | ParseTail _ _ _ _ => fun _ => None
                           end (projT2 p)
             end;
          lower_string_tail str0 valid prod prods str st
          := match st with
               | None => None
               | Some p => match projT1 p as p' in parse_of _ _ str' prods' return Forall_parse_of (P str0 valid) p' -> option (p_parse str0 valid str' (tl prods')) with
                             | ParseTail _ _ _ p' => fun H => Some (existT _ p' H)
                             | ParseHead _ _ _ _ => fun _ => None
                           end (projT2 p)
             end;
          lift_lookup_nonterminal_name_state_lt str0 valid nonterminal_name str pf := option_map (parse_of__of__parse_of_item_lt pf);
          lift_lookup_nonterminal_name_state_eq str0 valid nonterminal_name str pf := option_map (parse_of__of__parse_of_item_eq pf) |}.

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
      Section common.
        Section types.
          Context (str0 : String)
                  (valid : nonterminal_names_listT).

          Let prefix str T := (*size_of_parse_item (ParseNonTerminal name p) < h
                         ->*) str ≤s str0
                              -> sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
                              -> T.

          Let alt := False (*{ nonterminal_name : string
                     | is_valid_nonterminal_name initial_nonterminal_names_data nonterminal_name = true
                       /\ is_valid_nonterminal_name valid nonterminal_name = false }*).

          Section T_nonterminal_name.
            Context (name : string) (str : StringWithSplitState String (split_stateT str0 valid (include_nonterminal_name _ name))).
            Let ret := mp_parse_nonterminal_name str0 valid str name.

            Definition T_nonterminal_name_success  : Type
              := prefix str ret.

            Definition T_nonterminal_name_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt
                            end.
          End T_nonterminal_name.

          Section T_item.
            Context (it : item CharType) (str : StringWithSplitState String (split_stateT str0 valid it)).

            Let ret := mp_parse_item str0 valid str it.

            Definition T_item_success : Type
              := prefix str ret.
            Definition T_item_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt
                            end.
          End T_item.

          Section T_production.
            Context (prod : production CharType) (str : StringWithSplitState String (split_stateT str0 valid prod)).

            Let ret := mp_parse_production str0 valid str prod.

            Definition T_production_success : Type
              := prefix str ret.
            Definition T_production_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt
                            end.
          End T_production.

          Section T_productions.
            Context (prods : productions CharType) (str : StringWithSplitState String (split_stateT str0 valid prods)).

            Let ret := mp_parse str0 valid str prods.

            Definition T_productions_success : Type
              := prefix str ret.

            Definition T_productions_failure : Type
              := prefix str match state_val str with
                              | None => ret -> False
                              | Some p => alt
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

        Hint Constructors minimal_parse_of minimal_parse_of_name minimal_parse_of_production minimal_parse_of_item unit prod unit : minimal_instance_db.
        Hint Unfold T_item_success T_item_failure T_production_success T_production_failure T_productions_success T_productions_failure T_nonterminal_name_success T_nonterminal_name_failure
             DependentlyTyped.T_item_success DependentlyTyped.T_item_failure DependentlyTyped.T_production_success DependentlyTyped.T_production_failure DependentlyTyped.T_productions_success DependentlyTyped.T_productions_failure DependentlyTyped.T_nonterminal_name_success DependentlyTyped.T_nonterminal_name_failure
             p_parse_production p_parse p_parse_item p_parse_nonterminal_name
             mp_parse_production mp_parse mp_parse_item mp_parse_nonterminal_name : minimal_instance_db.

        Local Ltac t''0 :=
          first [ progress cbv zeta
                | intro
                (*| progress subst_body*)
                | let H := (match goal with
                              | [ H : StringWithSplitState _ _ |- _ ] => constr:H
                              | [ H : ?T |- _ ] => match eval hnf in T with
                                                     | StringWithSplitState _ _
                                                       => constr:H
                                                   end
                            end) in
                  let s := fresh "s" in
                  let st := fresh "st" in
                  destruct H as [s st];
                    change (StringLike.Core.string_val {| string_val := s |}) with s in *;
                    change (StringLike.Core.state_val {| state_val := st |}) with st in *;
                    simpl
                | match goal with
                    | [ H : option _ |- _ ] => destruct H; simpl
                    | [ H : ?T |- _ ] => match eval hnf in T with
                                           | option _ => destruct H; simpl
                                         end
                  end
                | match goal with
                    | [ H : appcontext[StringLike.Core.string_val {| string_val := ?s |}] |- _ ] => change (StringLike.Core.string_val {| string_val := s |}) with s in *
                    | [ H : appcontext[StringLike.Core.state_val {| state_val := ?s |}] |- _ ] => change (StringLike.Core.state_val {| state_val := s |}) with s in *
                  end ].

        Local Ltac t'' :=
          idtac;
          match goal with
            | _ => intro
            | [ H : False |- _ ] => solve [ destruct H ]
            | [ H : match _ with _ => _ end |- _ ] => progress hnf in H
            | _ => solve [ change unit; constructor ]
            | [ a : _, b : Forall_parse_of_production _ _ |- Forall_parse_of_production _ _ ]
              => exact (a, b)
            | [ H : parse_of _ _ _ []  |- _ ] => solve [ exfalso; clear -H; abstract inversion H ]
            | [ H : {| state_val := Some _ |} = {| state_val := None |} |- _ ]
              => solve [ destruct (neq_some_none_state_val H) ]
            | [ H : {| state_val := None |} = {| state_val := Some _ |} |- _ ]
              => solve [ destruct (neq_some_none_state_val (eq_sym H)) ]
            | [ H : _ \/ False |- _ ] => apply or_False in H
            | [ H : _ ≤s _ -> ?B |- _ ] => specialize (H (or_intror eq_refl))
            | [ H : _ ≤s _ -> ?B, H' : _ \/ _ |- _ ]
              => first [ specialize (H (transitivity (str_le1_append _ _ _) H'))
                       | specialize (H (transitivity (str_le2_append _ _ _) H'))
                       | specialize (H (transitivity split_parse_of_production_le1 H'))
                       | specialize (H (transitivity split_parse_of_production_le2 H')) ]
            | [ H : _ ≤s _ -> ?B, H' : _ ≤s _ |- _ ]
              => first [ specialize (H (transitivity (str_le1_append _ _ _) H'))
                       | specialize (H (transitivity (str_le2_append _ _ _) H'))
                       | specialize (H (transitivity split_parse_of_production_le1 H'))
                       | specialize (H (transitivity split_parse_of_production_le2 H')) ]
            | [ H : sub_names_listT _ ?x ?y -> _ |- _ ] => specialize (H (reflexivity _))
            | [ H : sub_names_listT _ _ _, H' : sub_names_listT _ _ _ -> _ |- _ ]
              => specialize (fun arg => H' (sub_names_listT_remove_2 _ arg _ H))
            | [ H : context[map _ nil] |- _ ] => progress simpl in H
            | [ H : context[map _ (_::_)] |- _ ] => progress simpl in H
            | [ H : appcontext[split_string_for_production _ _ {| state_val := Some _ |} ] |- _ ] => progress simpl in H
            | _ => progress autounfold with minimal_instance_db in *
            (*| _ => progress hnf in * *)
            | [ H : ?T |- _ ] => match head T with
                                   | match _ with _ => _ end => progress hnf in H
                                 end
            | [ |- ?T ] => (not constr_eq False T); solve [ eauto with minimal_instance_db ] (* work around bugged tactic universe successor anomaly *)
            | [ x : _ |- @sigT ?A _ ]
              => exists (MinParseNonTerminal x : A)
            | [ |- @sigT ?A _ ]
              => first [ (exists (MinParseTerminal _ _ _ _ _ _ _ _ : A))
                       | (exists (MinParseProductionNil _ _ _ _ _ _ _ : A)) ]
            | [ x : minimal_parse_of_item _ _ _ _ _ _ _ _ _, y : minimal_parse_of_production _ _ _ _ _ _ _ _ _, H : _ \/ _ |- @sigT ?A _ ]
              => exists (MinParseProductionCons H x y : A)
            | [ x : minimal_parse_of_production _ _ _ _ _ _ _ _ _
                |- @sigT ?A _ ]
              => exists (MinParseHead _ x : A); assumption
            | [ x : minimal_parse_of _ _ _ _ _ _ _ _ _
                |- @sigT ?A _ ]
              => exists (MinParseTail _ x : A); assumption
            | [ H : sigT _ |- _ ] => destruct H
            | [ H : sig _ |- _ ] => destruct H
            | [ H : prod _ _ |- _ ] => destruct H
            | [ H : and _ _ |- _ ] => destruct H
            | [ H : (_, _) = (_, _) |- _ ] => apply path_prod' in H
            | [ H : ?T |- _ ] => match eval hnf in T with
                                   | (_ * _)%type => destruct H
                                   | (_ /\ _)%type => destruct H
                                 end
            | _ => progress subst
            | _ => progress simpl
            | [ H : _ = _ |- _ ] => progress simpl in H (* work around [simpl in *] causing ~everything, even [admit], to error with "Anomaly: Cannot take the successor of a non variable universe:
(maybe a bugged tactic).
Please report." *)
            | [ H : _ |- _ ] =>
              match goal with
                | [ H' : _ = H |- _ ] => destruct H'
              end
            | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
            | [ H : is_true (_ =s _) |- _ ] => apply bool_eq_correct in H
            | [ H : parse_of_item _ _ _ (NonTerminal _ _) |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : parse_of_item _ _ _ (Terminal _) |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : parse_of_production _ _ _ [] |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
            | [ H : ?A -> False |- _ ] => let A' := (eval hnf in A) in progress change (A' -> False) in H
            | _ => progress trivial
            | _ => progress auto with arith
            | _ => t''0
            | [ H : (_ + _)%type |- _ ] => destruct H
            | [ |- (_ * _)%type ] => split
            | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _ _) |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : minimal_parse_of _ _ _ _ _ _ _ _ (_::_) |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : parse_of _ _ _ (_::_) |- _ ] => (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'
            | [ H : appcontext[if lt_dec ?a ?b then _ else _] |- _ ]
              => destruct (lt_dec a b)
          end.

        Local Ltac t' :=
          first [ t''
                | match goal with H : true = false |- _ => exfalso; clear -H; congruence end
                | match goal with H : ?x = false, H' : ?x = true |- _ => exfalso; clear -H H'; abstract congruence end
                | abstract omega
                | match goal with H : (?x =s ?x) = false |- _ => erewrite (proj2 (bool_eq_correct _ _ _)) in H by reflexivity end
                | match goal with H : _ -> False |- False => apply H end;
                  abstract (repeat t'') ].

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

        Lemma cons_success
              (str0 : String) (valid : nonterminal_names_listT)
              (it : item CharType) (its : production CharType)
              (s1 : StringWithSplitState String (split_stateT str0 valid it))
              (s2 : StringWithSplitState String (split_stateT str0 valid its))
              (str : StringWithSplitState String (split_stateT str0 valid (it :: its : production CharType)))
        : let a1 := DependentlyTyped.T_item_success str0 valid it s1 in
          let a2 := DependentlyTyped.T_production_success str0 valid its s2 in
          let ret :=
              DependentlyTyped.T_production_success str0 valid (it :: its) str in
          str ≤s str0 ->
          s1 ++ s2 =s str ->
          In (s1, s2) (split_string_for_production str0 valid it its str) -> a1 -> a2 -> ret.
        Proof.
          destruct str as [ ? [ ] ]; simpl.
          { intros ? ? H.
            apply or_False in H.
            apply path_prod' in H.
            simpl in H.
            destruct H as [H' H''].
            apply neq_some_none_state_val in H'.
            apply neq_some_none_state_val in H''.
            simpl in *.
            repeat t''. }
          { repeat t''. }
        Defined.

        Local Ltac t :=
          repeat t''0;
          try solve [ repeat t''; exfalso; t_false ].

        Local Obligation Tactic := idtac.

        Definition H_prod_splitT' str0 valid it its str st
          := split_string_lift_T str0 valid it its {| string_val := str ; state_val := st |} (split_string_for_production str0 valid it its {| string_val := str ; state_val := st |}).

        Lemma H_prod_split_helper str0 valid it its str st
        : @H_prod_splitT' str0 valid it its str (Some st).
        Proof.
          subst_body; simpl in *.
          intros ? H.
          simpl in H.
          destruct_head prod.
          destruct_head sum;
            destruct_head prod;
            unfold T_item_failure, T_production_failure in *;
            simpl in *.
          { repeat t''. }
          { repeat t''. }
          { repeat t''. }
        Defined.

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
