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

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT)
          (names_listT_R : names_listT -> names_listT -> Prop)
          (remove_name_dec : forall ls name,
                               is_valid_name ls name = true
                               -> names_listT_R (remove_name ls name) ls)
          (ntl_wf : well_founded names_listT_R)
          (split_stateT : Type).
  Context (split_string_for_production
           : forall (str0 : StringWithSplitState String split_stateT) (prod : production CharType), list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
          (split_string_for_production_correct
           : forall (str0 : StringWithSplitState String split_stateT) prod,
               List.Forall (fun s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                            => (fst s1s2 ++ snd s1s2 =s str0) = true)
                           (split_string_for_production str0 prod)).

  Section generic.
    Section parts.
      Context {T_name_success T_name_failure : forall (str0 str : StringWithSplitState String split_stateT) (valid : names_listT),
                                                 string -> Type}
              {T_item_success T_item_failure : forall (str0 str : StringWithSplitState String split_stateT) (valid : names_listT),
                                                 item CharType -> Type}
              (lift_success : forall {str0 str valid} name, @T_name_success str0 str valid name -> @T_item_success str0 str valid (NonTerminal _ name))
              (lift_failure : forall {str0 str valid} name, @T_name_failure str0 str valid name -> @T_item_failure str0 str valid (NonTerminal _ name))
              (parse_terminal_success : forall {str0 str : StringWithSplitState String split_stateT} {valid} ch,
                                          [[ ch ]] =s str -> @T_item_success str0 str valid (Terminal ch))
              (parse_terminal_failure : forall {str0 str : StringWithSplitState String split_stateT} {valid}
                                               ch, ([[ ch ]] =s str) = false -> @T_item_failure str0 str valid (Terminal ch))
              {T_production_success T_production_failure
               : forall (str0 str : StringWithSplitState String split_stateT)
                        (valid : names_listT)
                        (prod : production CharType),
                   Type}
              (parse_empty_success : forall {str0 str : StringWithSplitState String split_stateT} {valid}, str =s Empty _ -> T_production_success str0 str valid nil)
              (parse_empty_failure : forall {str0 str : StringWithSplitState String split_stateT} {valid} (pf : str ≤s str0), (str =s Empty _) = false -> T_production_failure str0 str valid nil)
              (cons_success : forall (str0 s1 s2 str : StringWithSplitState String split_stateT) {valid} (pf : str ≤s str0) (H : s1 ++ s2 =s str) it its,
                                @T_item_success str0 s1 valid it -> @T_production_success str0 s2 valid its -> @T_production_success str0 str valid (it :: its)).

      Definition split_string_lift_T (str0 str : StringWithSplitState String split_stateT) (valid : names_listT) (it : item CharType) (its : production CharType)
                 (split : production CharType ->
                          list
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
                              (split (it::its)))
           -> T_production_failure str0 str valid (it::its).

      Local Notation H_prod_split_T str0 str valid prod split :=
        match prod return Type with
          | nil => unit
          | it::its => split_string_lift_T str0 str valid it its split
        end.

      Context {T_productions_success T_productions_failure
               : forall (str0 str : StringWithSplitState String split_stateT)
                        (valid : names_listT)
                        (prods : productions CharType),
                   Type}.

      Context (fail_parse_nil_productions : forall {str0 str valid}, T_productions_failure str0 str valid [])
              (lift_prods_success_head : forall {str0 str valid prod prods}, @T_production_success str0 str valid prod -> @T_productions_success str0 str valid (prod::prods))
              (lift_prods_success_tail : forall {str0 str valid prod prods}, @T_productions_success str0 str valid prods -> @T_productions_success str0 str valid (prod::prods))
              (lift_prods_failure : forall {str0 str valid prod prods}, @T_production_failure str0 str valid prod -> @T_productions_failure str0 str valid prods -> @T_productions_failure str0 str valid (prod::prods)).

      Context (H_prod_split : forall str0 str valid prod, H_prod_split_T str0 str valid prod (split_string_for_production str)).

      Context (lift_parse_name_success_lt : forall {str0 str : StringWithSplitState String split_stateT} {valid name}, Length str < Length str0 -> @T_productions_success str str initial_names_data (Lookup G name) -> @T_name_success str0 str valid name)
              (lift_parse_name_failure_lt : forall {str0 str : StringWithSplitState String split_stateT} {valid name}, Length str < Length str0 -> @T_productions_failure str str initial_names_data (Lookup G name) -> @T_name_failure str0 str valid name)
              (lift_parse_name_success_eq : forall {str0 str : StringWithSplitState String split_stateT} {valid name},
                                              str = str0 :> String -> is_valid_name valid name = true -> @T_productions_success str0 str0 (remove_name valid name) (Lookup G name) -> @T_name_success str0 str valid name)
              (lift_parse_name_failure_eq : forall {str0 str : StringWithSplitState String split_stateT} {valid name},
                                              ~Length str < Length str0 -> @T_productions_failure str0 str0 (remove_name valid name) (Lookup G name) -> @T_name_failure str0 str valid name)
              (elim_parse_name_failure : forall {str0 str : StringWithSplitState String split_stateT} {valid name},
                                           str ≤s str0 -> ~ Length str < Length str0 -> is_valid_name valid name = false -> @T_name_failure str0 str valid name).

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
                      | left pf => inl (@parse_terminal_success _ _ _ ch pf)
                      | right pf => inr (@parse_terminal_failure _ _ _ ch pf)
                    end
               | NonTerminal name
                 => match str_matches_name name with
                      | inl ret => inl (lift_success ret)
                      | inr ret => inr (lift_failure ret)
                    end
             end.
      End item.

      Section production_and_productions.
        Context (str0 : StringWithSplitState String split_stateT)
                (valid : names_listT).
        Context (parse_name : forall (str : StringWithSplitState String split_stateT),
                                str ≤s str0
                                -> forall name,
                                     sum (@T_name_success str0 str valid name) (@T_name_failure str0 str valid name)).

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
              clear H_prod_split; rename H_prod_split' into H_prod_split.
              (** TODO: make this mirror BooleanRecognizer more *)
              specialize (H_prod_split pf).
              subst_body; simpl in *.
              destruct splits as [ | [s1 s2] splits ]; simpl in *.
              { right; exact (H_prod_split tt). }
              { assert (Hs1 : s1 ≤s str0).
                { clear -pf splits_correct.
                  abstract (
                      inversion splits_correct; subst;
                      simpl in *;
                        etransitivity; [ | exact pf ];
                      etransitivity; [ apply str_le1_append | ];
                      right; apply bool_eq_correct; eassumption
                    ). }
                assert (Hs2 : s2 ≤s str0).
                { clear -pf splits_correct.
                  abstract (
                      inversion splits_correct; subst;
                      simpl in *;
                        etransitivity; [ | exact pf ];
                      etransitivity; [ apply str_le2_append | ];
                      right; apply bool_eq_correct; eassumption
                    ). }
                edestruct (@parse_item str0 s1
                                       valid
                                       (@parse_name s1 Hs1)
                                       it),
                (@parse_production s2 Hs2);
                  [ left;
                    apply (@cons_success str0 s1 s2 _ valid pf); [ | eassumption | eassumption ];
                    clear -splits_correct;
                    abstract (inversion splits_correct; subst; assumption)
                  | | | ];
                  (apply (parse_production_helper str pf it its splits parse_production);
                   [ .. | clear -splits_correct; abstract (inversion splits_correct; subst; assumption) ];
                   []);
                  (intros ? H'; apply H_prod_split; split; [ | exact H' ]);
                  left_right_t. }
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
                            | left pf' => inl (parse_empty_success str0 str valid pf')
                            | right pf' => inr (parse_empty_failure str0 str valid pf pf')
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
                     | nil => inr (fail_parse_nil_productions str0 str valid)
                     | prod'::prods'
                       => match @parse_production str pf prod',
                                @parse_productions str pf prods' with
                            | inl prod_success, _
                              => inl (lift_prods_success_head _ prod_success)
                            | _, inl prods_success
                              => inl (lift_prods_success_tail _ prods_success)
                            | inr prod_failure, inr prods_failure
                              => inr (lift_prods_failure prod_failure prods_failure)
                          end
                   end.
          Defined.
        End productions.
      End production_and_productions.

      Section names.
        Let T_productions := fun str0 str valid prods => sum (T_productions_success str0 str valid prods) (T_productions_failure str0 str valid prods).

        Let T_name := fun str0 str valid name => sum (@T_name_success str0 str valid name) (@T_name_failure str0 str valid name).

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
                       match (parse_productions
                                (@parse_name
                                   (str, initial_names_data)
                                   (or_introl pf'))
                                str
                                (or_intror eq_refl)
                                (Lookup G name)) with
                         | inl success => inl (@lift_parse_name_success_lt str0 str valid name pf' success)
                         | inr failure => inr (@lift_parse_name_failure_lt str0 str valid name pf' failure)
                       end
                     | right pf', left H' =>
                       (** [str] didn't get smaller, so we cache the fact that we've hit this name already *)
                       (** It was valid, so we can remove it *)
                       match (parse_productions
                                (@parse_name
                                   (str0, remove_name valid name)
                                   (or_intror (conj eq_refl (remove_name_dec H'))))
                                _
                                (or_intror eq_refl)
                                (Lookup G name)) with
                         | inl success => inl (@lift_parse_name_success_eq _ _ _ _ _ H' success)
                         | inr failure => inr (@lift_parse_name_failure_eq _ _ _ _ pf' failure)
                       end
                     | right pf', right pf''
                       => (** oops, we already saw this name in the past.  ABORT! *)
                         inr (@elim_parse_name_failure _ _ _ _ pf pf' pf'')
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

  Require Import Parsers.MinimalParse.
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

    Local Ltac t := repeat t'.

    Section parts.
      Section common.
        Section with_str0_str_valid.
          Context (str0 str : StringWithSplitState String split_stateT)
                  (valid : names_listT).

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

          Definition lift_success name (H : T_name_success name) : T_item_success (NonTerminal _ name)
            := MinParseNonTerminal H.

          Definition lift_failure name (H : T_name_failure name) : T_item_failure (NonTerminal _ name).
          Proof.
            clear -H; abstract t.
          Defined.

          Definition parse_terminal_success ch (H : [[ ch ]] =s str)
          : T_item_success (Terminal ch).
          Proof.
            apply bool_eq_correct in H.
            hnf.
            case H.
            constructor.
          Defined.

          Definition parse_terminal_failure ch (H : ([[ ch ]] =s str) = false)
          : T_item_failure (Terminal ch).
          Proof.
            clear -H; abstract t.
          Defined.

          Definition T_production_success (prod : production CharType) : Type
            := minimal_parse_of_production String G initial_names_data is_valid_name remove_name
                                           str0 valid str prod.

          Definition T_production_failure (prod : production CharType) : Type
            := T_production_success prod -> False.

          Definition parse_empty_success (H : str =s Empty _)
          : T_production_success nil.
          Proof.
            apply bool_eq_correct in H.
            hnf.
            symmetry in H.
            case H.
            constructor.
          Defined.

          Definition parse_empty_failure (pf : str ≤s str0) (H : (str =s Empty _) = false)
          : T_production_failure nil.
          Proof.
            clear -H; abstract t.
          Defined.

          Definition T_productions_success (prods : productions CharType) : Type
            := minimal_parse_of String G initial_names_data is_valid_name remove_name
                                str0 valid str prods.

          Definition T_productions_failure (prods : productions CharType) : Type
            := T_productions_success prods -> False.

          Definition fail_parse_nil_productions : T_productions_failure [].
          Proof.
            intro H.
            inversion H.
          Qed.

          Definition lift_prods_success_head {prod prods}
          : @T_production_success prod -> @T_productions_success (prod::prods)
            := @MinParseHead _ _ _ _ _ _ _ _ _ _ _ _.

          Definition lift_prods_success_tail {prod prods}
          : @T_productions_success prods -> @T_productions_success (prod::prods)
            := @MinParseTail _ _ _ _ _ _ _ _ _ _ _ _.

          Definition lift_prods_failure {prod prods}
                     (H1 : @T_production_failure prod)
                     (H2 : @T_productions_failure prods)
          : @T_productions_failure (prod::prods).
          Proof.
            clear -H1 H2.
            intro H'.
            inversion H'; subst;
            eauto.
          Qed.
        End with_str0_str_valid.

        Definition cons_success (str0 s1 s2 str : StringWithSplitState String split_stateT) (valid : names_listT) (pf : str ≤s str0) (H : s1 ++ s2 =s str) it its
                   (p_it : @T_item_success str0 s1 valid it) (p_its : @T_production_success str0 s2 valid its)
        : @T_production_success str0 str valid (it :: its).
        Proof.
          hnf in *.
          apply bool_eq_correct in H.
          revert pf.
          case H.
          constructor (assumption).
        Defined.

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
        : @split_string_lift_T (@T_item_success) (@T_item_failure) (@T_production_success) (@T_production_failure) str0 str valid it its (split_string_for_production str).
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
            | it::its => @split_string_lift_T (@T_item_success) (@T_item_failure) (@T_production_success) (@T_production_failure) str0 str valid it its (split_string_for_production str)
          end.
        Proof.
          unfold split_string_lift_T.
          destruct prod.
          { constructor. }
          { intro pf. apply H_prod_split' with (pf := pf); try apply split_list_complete; assumption. }
        Defined.

        Definition H_prod_split
                   (split_list_complete : forall str0 str valid prod pf, @split_list_completeT str0 valid valid str pf (split_string_for_production str prod) prod)
                   str0 str valid prod :=
          H_prod_split'' str0 str valid prod (split_list_complete str0 str valid prod).

        Definition lift_parse_name_success_lt
                   (str0 str : StringWithSplitState String split_stateT) valid name
        : Length str < Length str0
          -> @T_productions_success str str initial_names_data (Lookup G name)
          -> @T_name_success str0 str valid name
          := @MinParseNonTerminalStrLt _ _ _ _ _ _ _ _ _ _ _.

        Definition lift_parse_name_success_eq
                   (str0 str : StringWithSplitState String split_stateT)
                   valid name
                   (H : str = str0 :> String)
                   (H' : is_valid_name valid name = true)
                   (p : @T_productions_success str0 str0 (remove_name valid name) (Lookup G name))
        : @T_name_success str0 str valid name.
        Proof.
          hnf; case (eq_sym H).
          exact (@MinParseNonTerminalStrEq _ String G _ initial_names_data is_valid_name remove_name str0 valid name H' p).
        Defined.

        Definition lift_parse_name_failure_lt
                   (str0 str : StringWithSplitState String split_stateT)
                   valid name
                   (pf : Length str < Length str0)
                   (p : @T_productions_failure str str initial_names_data (Lookup G name))
        : @T_name_failure str0 str valid name.
        Proof.
          clear -pf p.
          intro p'.
          apply p; clear p.
          inversion p'; subst; try assumption.
          destruct str, str0; simpl in *; subst.
          exfalso; omega.
        Qed.

        Definition lift_parse_name_failure_eq
                   (str0 str : StringWithSplitState String split_stateT)
                   valid name
                   (pf : ~Length str < Length str0)
                   (p : @T_productions_failure str0 str0 (remove_name valid name) (Lookup G name))
        : @T_name_failure str0 str valid name.
        Proof.
          clear -pf p.
          intro p'.
          apply p; clear p.
          inversion p'; subst.
          { exfalso; eauto. }
          { destruct str, str0; simpl in *; subst.
            assumption. }
        Qed.

        Definition elim_parse_name_failure
                   (str0 str : StringWithSplitState String split_stateT)
                   valid name
                   (pf : str ≤s str0)
                   (pf' : ~ Length str < Length str0)
                   (H : is_valid_name valid name = false)
        : @T_name_failure str0 str valid name.
        Proof.
          clear -pf pf' H.
          intro p.
          inversion p; subst; eauto.
          congruence.
        Qed.
      End common.

      Definition minimal_parse_name
                 (split_list_complete
                  : forall str0 str valid prod pf,
                      @split_list_completeT str0 valid valid str pf (split_string_for_production str prod) prod)
      : forall (str : StringWithSplitState String split_stateT)
               (name : string),
          sum (T_name_success str str initial_names_data name)
              (T_name_failure str str initial_names_data name)
        := @parse_name
             T_name_success T_name_failure
             T_item_success T_item_failure
             lift_success lift_failure
             parse_terminal_success
             parse_terminal_failure
             T_production_success
             T_production_failure
             parse_empty_success
             parse_empty_failure
             cons_success
             T_productions_success T_productions_failure
             fail_parse_nil_productions
             lift_prods_success_head lift_prods_success_tail
             lift_prods_failure
             (H_prod_split split_list_complete)
             lift_parse_name_success_lt lift_parse_name_failure_lt
             lift_parse_name_success_eq lift_parse_name_failure_eq
             elim_parse_name_failure.
    End parts.
  End minimal.
End recursive_descent_parser.
