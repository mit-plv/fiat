(** * Specialization of the dependently typed parser to minimal parse trees, taking in parse trees, split up with an abstraction barrier *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.DependentlyTyped Parsers.MinimalParse.
Require Import Parsers.DependentlyTypedMinimal Parsers.DependentlyTypedSum Parsers.BaseTypes.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
Require Import Common Common.Wf Common.Le.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context (CharType : Type)
          (String : string_like CharType)
          (G : grammar CharType).
  Context {predata : parser_computational_predataT}.
  Local Instance types_data : @parser_computational_types_dataT _ String
    := {| predata := predata;
          split_stateT str0 valid g str := True |}.
  Context {methods' : @parser_computational_dataT' _ String types_data}
          {strdata : @parser_computational_strdataT _ String G {| methods' := methods' |}}.

  Local Instance orig_methods : @parser_computational_dataT _ String
    := { methods' := methods' }.

  Context (remove_nonterminal_1
           : forall ls ps ps',
               is_valid_nonterminal (remove_nonterminal ls ps) ps' = true
               -> is_valid_nonterminal ls ps' = true)
          (remove_nonterminal_2
           : forall ls ps ps',
               is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
               <-> is_valid_nonterminal ls ps' = false \/ ps = ps').

  Definition P (str0 : String) valid : String -> string -> Prop
    := fun str p =>
         sub_names_listT is_valid_nonterminal valid initial_nonterminals_data
         /\ is_valid_nonterminal
              (if lt_dec (Length str) (Length str0)
               then initial_nonterminals_data
               else valid)
              p = true.

  Lemma P_remove_impl {str0 valid str name name'}
        (H0 : name <> name')
        (H : P str0 valid str name')
  : P str0 (remove_nonterminal valid name) str name'.
  Proof.
    destruct_head_hnf and.
    repeat split; try assumption.
    { apply sub_names_listT_remove_2; assumption. }
    { destruct lt_dec; try assumption.
      match goal with
        | [ |- ?b = true ] => case_eq b; try reflexivity
      end.
      intro H'; exfalso.
      apply remove_nonterminal_2 in H'.
      destruct H'; congruence. }
  Qed.

  Definition p_parse_item str0 valid s it
    := { p' : parse_of_item String G s it & Forall_parse_of_item (P str0 valid) p' }.
  Definition p_parse_production str0 valid s p
    := { p' : parse_of_production String G s p & Forall_parse_of_production (P str0 valid) p' }.
  Definition p_parse str0 valid s prods
    := { p' : parse_of String G s prods & Forall_parse_of (P str0 valid) p' }.
  Definition p_parse_nonterminal str0 valid s nonterminal
    := { p' : parse_of_item String G  s (NonTerminal _ nonterminal) & Forall_parse_of_item (P str0 valid) p' }.

  Definition split_parse_of_production {str0 valid str it its}
             (p : p_parse_production str0 valid str (it::its))
  : { s1s2 : String * String & (fst s1s2 ++ snd s1s2 =s str)
                               * p_parse_item str0 valid (fst s1s2) it
                               * p_parse_production str0 valid (snd s1s2) its }%type.
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

  Lemma split_parse_of_production_le1 {str0 valid str it its p}
  : fst (projT1 (@split_parse_of_production str0 valid str it its p)) ≤s str.
  Proof.
    etransitivity; [ eapply str_le1_append | right; apply bool_eq_correct ].
    exact (fst (fst (projT2 (split_parse_of_production p)))).
  Qed.

  Lemma split_parse_of_production_le2 {str0 valid str it its p}
  : snd (projT1 (@split_parse_of_production str0 valid str it its p)) ≤s str.
  Proof.
    etransitivity; [ eapply str_le2_append | right; apply bool_eq_correct ].
    exact (fst (fst (projT2 (split_parse_of_production p)))).
  Qed.

  Local Instance top_types_data : @parser_computational_types_dataT _ String
    := { split_stateT str0 valid g s
         := match g return Type with
              | include_item it => p_parse_item str0 valid s it
              | include_production p => p_parse_production str0 valid s p
              | include_productions prods => p_parse str0 valid s prods
              | include_nonterminal nonterminal => p_parse_nonterminal str0 valid s nonterminal
            end }.

  Local Instance top_methods' : @parser_computational_dataT' _ String top_types_data
    := { split_string_for_production str0 valid it its s
         := let st' := split_parse_of_production (state_val s) in
            ({| string_val := fst (projT1 st') ; state_val := snd (fst (projT2 st')) |},
             {| string_val := snd (projT1 st') ; state_val := snd (projT2 st') |})::nil }.
  Proof.
    intros; subst_body; simpl in *.
    abstract (do 2 try constructor; edestruct @split_parse_of_production; simpl; intuition).
  Defined.

  Definition parse_of__of__parse_of_item_lt' {str0 valid str nonterminal}
             (pf : Length str < Length str0)
             (p : p_parse_nonterminal str0 valid str nonterminal)
  : P str0 valid str nonterminal * p_parse str initial_nonterminals_data str (Lookup G nonterminal).
  Proof.
    refine (match projT1 p as p' in parse_of_item _ _ str' it'
                  return match it' with
                           | Terminal _ => True
                           | NonTerminal nonterminal' => Length str' < Length str0 -> Forall_parse_of_item (P str0 valid) p' -> P str0 valid str' nonterminal' * p_parse str' initial_nonterminals_data str' (Lookup G nonterminal')
                         end
            with
              | ParseTerminal _ => I
              | ParseNonTerminal _ _ p' => fun pf' H' => (fst H', existT _ p' (expand_forall_parse_of _ _ (snd H')))
            end pf (projT2 p)).
    clear -pf'; unfold P in *; simpl;
    abstract (intros ??; do 2 edestruct lt_dec; intuition).
  Defined.
  Definition parse_of__of__parse_of_item_lt {str0 valid str nonterminal} pf p
    := snd (@parse_of__of__parse_of_item_lt' str0 valid str nonterminal pf p).

  Definition deloop_right str0 valid str nonterminal
    := p_parse str0 (remove_nonterminal valid nonterminal) str (Lookup G nonterminal).

  Definition deloop_onceT
    := forall str0 valid str nonterminal prods
              (p : parse_of String G str prods)
              (pf : str = str0 :> String)
              (H : Forall_parse_of (P str0 valid) p),
         p_parse str0 (remove_nonterminal valid nonterminal) str prods
         + deloop_right str0 valid str nonterminal.

  Definition deloop_once_productionT
    := forall str0 valid str nonterminal prod
              (p : parse_of_production String G str prod)
              (pf : str = str0 :> String)
              (H : Forall_parse_of_production (P str0 valid) p),
         p_parse_production str0 (remove_nonterminal valid nonterminal) str prod
         + deloop_right str0 valid str nonterminal.

  Definition deloop_once_item'
             (deloop_once : deloop_onceT)
             {str0 valid str nonterminal}
             {it}
             (p : parse_of_item String G str it)
             (pf : str = str0 :> String)
             (H : Forall_parse_of_item (P str0 valid) p)
  : p_parse_item str0 (remove_nonterminal valid nonterminal) str it
    + deloop_right str0 valid str nonterminal.
  Proof.
    destruct p as [ | nonterminal' str'' p' ].
    { exact (inl (existT _ (ParseTerminal _ _ _) tt)). }
    { refine (if string_dec nonterminal nonterminal'
              then inr (if @deloop_once _ _ _ nonterminal' _ p' pf (snd H)
                        then _
                        else _)
              else match @deloop_once _ _ _ nonterminal _ p' pf (snd H) with
                     | inl p''' => inl (existT _ (ParseNonTerminal _ (projT1 p''')) (P_remove_impl _ (fst H), projT2 p'''))
                     | inr ret => inr ret
                   end);
      clear deloop_once;
      solve [ assumption
            | subst; assumption ]. }
  Defined.

  Definition deloop_once'
             (deloop_once : deloop_onceT)
             (deloop_once_production : deloop_once_productionT)
  : deloop_onceT.
  Proof.
    intros str0 valid str nonterminal pats p pf H.
    destruct p as [ str' pat' pats' p' | str' pat' pats' p' ].
    { refine match deloop_once_production str0 valid str' nonterminal _ p' pf H with
               | inl ret => inl (existT _ (ParseHead pats' (projT1 ret)) (projT2 ret))
               | inr ret => inr ret
             end. }
    { refine match deloop_once str0 valid str' nonterminal _ p' pf H with
               | inl ret => inl (existT _ (ParseTail _ (projT1 ret)) (projT2 ret))
               | inr ret => inr ret
             end. }
  Defined.

  Local Ltac deloop_t :=
    repeat match goal with
             | _ => assumption
             | _ => intro
             | [ H : ?x = ?y |- _ ] => subst x
             | [ H : ?x = ?y |- _ ] => subst y
             | [ H : _ ≤s _ |- _ ] => destruct H
             | _ => progress simpl in *
             | [ H : _ |- _ ] => rewrite Length_Empty in H
             | _ => rewrite Length_Empty
             | [ H : _ < 0 |- _ ] => destruct (Lt.lt_n_0 _ H)
             | _ => progress destruct_head and
             | [ |- _ /\ _ ] => split
             | [ H : sub_names_listT _ _ _ |- is_valid_nonterminal _ _ = true ]
               => (apply H; eapply sub_names_listT_remove; eassumption)
             | [ H : ~0 < ?n |- _ ]
               => (let H' := fresh in
                   destruct (zerop n) as [ | H' ]; [ clear H | destruct (H H') ])
             | [ H : Length _ = 0 |- _ ] => apply Empty_Length in H
             | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
             | [ H : context[Length (_ ++ _)] |- _ ] => rewrite <- Length_correct in H
             | [ H : ~_ < _ + _ |- _ ]
               => unique pose proof (proj1 (not_lt_plus H))
             | [ H : ~_ < _ + _ |- _ ]
               => unique pose proof (proj2 (not_lt_plus H))
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
             | [ H : ~ ?a < ?a + _ |- _ ] => apply not_lt_add_r in H
             | [ H : ~ ?a < _ + ?a |- _ ] => apply not_lt_add_l in H
           end.

  Definition deloop_once_production'
             (deloop_once : deloop_onceT)
             (deloop_once_production : deloop_once_productionT)
  : deloop_once_productionT.
  Proof.
    intros str0 valid str nonterminal pat p pf H.
    destruct p as [ | str' pat' strs' pats' p' p'' ].
    { refine (inl (existT _ (ParseProductionNil _ _) tt)). }
    { (** We must discriminate based on whether or not [str] has already gotten shorter *)
      destruct (stringlike_dec str' (Empty _)) as [e|e], (stringlike_dec strs' (Empty _)) as [e'|e'];
      try (assert (pf0 : str' = str0)
            by (clear -pf e'; abstract (subst strs'; rewrite ?RightId, ?LeftId in pf; exact pf));
           pose proof (@deloop_once_item' (deloop_once) str0 valid _ nonterminal pat' p' pf0 (fst H)) as deloop_once_item;
           clear deloop_once);
      try (assert (pf1 : strs' = str0)
            by (clear -pf e; abstract (subst str'; rewrite ?RightId, ?LeftId in pf; exact pf));
           specialize (deloop_once_production str0 valid _ nonterminal pats' p'' pf1 (snd H)));
      try (destruct deloop_once_item as [ret|ret];
           [ | right; repeat first [ subst str' | subst strs' ]; rewrite ?LeftId, ?RightId; assumption ]);
      try (destruct deloop_once_production as [ret'|ret'];
           [ | right; repeat first [ subst str' | subst strs' ]; rewrite ?LeftId, ?RightId; assumption ]);
      left.
      { (** empty, empty *)
        exact (existT _ (ParseProductionCons (projT1 ret) (projT1 ret'))
                      (projT2 ret, projT2 ret')). }
      { (** empty, nonempty *)
        refine (existT _ (ParseProductionCons p' (projT1 ret'))
                       (expand_forall_parse_of_item _ (fst H), projT2 ret')).
        unfold P in *; simpl.
        clear -e e' pf1 remove_nonterminal_1 remove_nonterminal_2.
        abstract (intros; edestruct lt_dec; deloop_t). }
      { (** nonempty, empty *)
        refine (existT _ (ParseProductionCons (projT1 ret) p'')
                       (projT2 ret, expand_forall_parse_of_production _ _ (snd H))).
        unfold P in *; simpl.
        clear -e e' pf0 remove_nonterminal_1 remove_nonterminal_2.
        abstract (intros; edestruct lt_dec; deloop_t). }
      { (** nonempty, nonempty *)
        refine (existT _ (ParseProductionCons p' p'')
                       (expand_forall_parse_of_item _ (fst H),
                        expand_forall_parse_of_production _ _ (snd H)));
        unfold P in *; simpl;
        clear -e e' pf remove_nonterminal_1 remove_nonterminal_2;
        abstract (intros; edestruct lt_dec; deloop_t). } }
  Defined.

  Fixpoint deloop_once {str0 valid str nonterminal pats} (p : parse_of String G str pats)
    := @deloop_once' (@deloop_once) (@deloop_once_production) str0 valid str nonterminal pats p
  with deloop_once_production {str0 valid str nonterminal pat} (p : parse_of_production String G str pat)
       := @deloop_once_production' (@deloop_once) (@deloop_once_production) str0 valid str nonterminal pat p.
  Definition deloop_once_item {str0 valid str nonterminal it} (p : parse_of_item String G str it)
    := @deloop_once_item' (@deloop_once) str0 valid str nonterminal it p.

  Definition parse_of__of__parse_of_item_eq' {str0 valid str nonterminal}
             (pf : str = str0 :> String)
             (p : p_parse_nonterminal str0 valid str nonterminal)
  : P str0 valid str nonterminal * p_parse str0 (remove_nonterminal valid nonterminal) str (Lookup G nonterminal).
  Proof.
    refine (match projT1 p as p' in parse_of_item _ _ str' it'
                  return match it' with
                           | Terminal _ => True
                           | NonTerminal nonterminal' => str' = str0 -> Forall_parse_of_item (P str0 valid) p' -> P str0 valid str' nonterminal' * p_parse str0 (remove_nonterminal valid nonterminal') str' (Lookup G nonterminal')
                         end
            with
              | ParseTerminal _ => I
              | ParseNonTerminal nonterminal' _ p'
                => fun pf' H' => (fst H', if @deloop_once str0 valid _ nonterminal' _ p' pf' (snd H') then _ else _)
            end pf (projT2 p));
    assumption.
  Defined.
  Definition parse_of__of__parse_of_item_eq {str0 valid str nonterminal} pf p
    := snd (@parse_of__of__parse_of_item_eq' str0 valid str nonterminal pf p).

  Definition top_methods : @parser_computational_dataT _ String
    := {| BaseTypes.methods' := top_methods' |}.

  Local Instance top_prestrdata : @parser_computational_prestrdataT _ String G top_methods option
    := { prelower_nonterminal_state str0 valid nonterminal str st := Some st;
         prelower_string_head str0 valid prod prods str st
         := match projT1 st as p' in parse_of _ _ str' prods' return Forall_parse_of (P str0 valid) p' -> option (p_parse_production str0 valid str' (hd prod prods')) with
              | ParseHead _ _ _ p' => fun H => Some (existT _ p' H)
              | ParseTail _ _ _ _ => fun _ => None
            end (projT2 st);
         prelower_string_tail str0 valid prod prods str st
         := match projT1 st as p' in parse_of _ _ str' prods' return Forall_parse_of (P str0 valid) p' -> option (p_parse str0 valid str' (tl prods')) with
              | ParseTail _ _ _ p' => fun H => Some (existT _ p' H)
              | ParseHead _ _ _ _ => fun _ => None
            end (projT2 st);
         prelift_lookup_nonterminal_state_lt str0 valid nonterminal str pf := Some ∘ parse_of__of__parse_of_item_lt pf;
         prelift_lookup_nonterminal_state_eq str0 valid nonterminal str pf := Some ∘ parse_of__of__parse_of_item_eq pf }.

  Context (split_list_complete : forall str0 valid it its str pf, @split_list_completeT _ String G _ str0 valid it its str pf (split_string_for_production str0 valid it its str)).

  Local Ltac ddestruct H :=
    (* work around 4035 *) let H' := fresh in rename H into H'; dependent destruction H'.

  Local Ltac t' :=
    idtac;
    match goal with
      | _ => intro
      | _ => progress simpl in *
      | _ => discriminate
      | _ => congruence
      | _ => progress destruct_head @StringWithSplitState
      | _ => progress destruct_head_hnf sigT
      | _ => progress destruct_head_hnf prod
      | _ => progress destruct_head_hnf and
      | [ H : ~?T, H' : ?T |- _ ] => destruct (H H')
      | [ H : (?x =s ?x) = false |- _ ] => erewrite (proj2 (bool_eq_correct _ _ _)) in H by reflexivity
      | [ H : parse_of_item _ _ _ (Terminal _) |- _ ] => ddestruct H
      | [ H : parse_of_item _ _ _ (NonTerminal _ _) |- _ ] => ddestruct H
      | [ H : parse_of_production _ _ _ [] |- _ ] => ddestruct H
      | [ H : parse_of _ _ _ (_::_) |- _ ] => ddestruct H
      | [ H : parse_of _ _ _ nil |- _ ] => ddestruct H
      | [ H : appcontext[if lt_dec ?a ?b then _ else _] |- _ ] => destruct (lt_dec a b)
    end.

  Local Ltac t := repeat t'.

  Local Obligation Tactic := t.

  Global Program Instance minimal_of_parse_parser_dependent_types_extra_data'
  : @parser_dependent_types_extra_dataT _ String G
    := @sum_extra_data
         _ String G
         predata
         methods'
         (@minimal_parser_dependent_types_success_data' _ String G _)
         (@minimal_parser_dependent_types_failure_data' _ String G _)
         strdata
         (@minimal_parser_dependent_types_extra_success_data' _ String G _ _)
         (@minimal_parser_dependent_types_extra_failure_data' _ String G _ _ split_list_complete)
         _
         top_methods'
         top_prestrdata
         _ _ _ _ _ _ _ _ _.

  Definition minimal_parse_nonterminal__of__parse'
             (nonterminal : string)
             (s : String)
             (p : parse_of_item String G s (NonTerminal _ nonterminal))
             (H : Forall_parse_of_item
                    (fun _ n => is_valid_nonterminal initial_nonterminals_data n = true)
                    p)
  : minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal s initial_nonterminals_data s nonterminal.
  Proof.
    pose proof (fun H' => @parse_nonterminal _ String G minimal_of_parse_parser_dependent_types_extra_data' nonterminal s (Some (existT _ p (expand_forall_parse_of_item H' H)))) as H0.
    simpl in *.
    unfold T_nonterminal_success, T_nonterminal_failure in *.
    simpl in *.
    destruct H0; destruct_head False; try assumption; [ clear ].
    unfold P in *; simpl in *.
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
End recursive_descent_parser.
