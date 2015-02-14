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
  Context (remove_nonterminal_name_1
           : forall ls ps ps',
               is_valid_nonterminal_name (remove_nonterminal_name ls ps) ps' = true
               -> is_valid_nonterminal_name ls ps' = true)
          (remove_nonterminal_name_2
           : forall ls ps ps',
               is_valid_nonterminal_name (remove_nonterminal_name ls ps) ps' = false
               <-> is_valid_nonterminal_name ls ps' = false \/ ps = ps').
  Variable orig_methods : @parser_computational_dataT' CharType String premethods.
  Variable gen_state : forall str0 valid (prod : production CharType) s, split_stateT str0 valid prod s.

  Let P (str0 : String) valid : String -> string -> Prop
    := fun str p =>
         sub_names_listT is_valid_nonterminal_name valid initial_nonterminal_names_data
         /\ is_valid_nonterminal_name
              (if lt_dec (Length str) (Length str0)
               then initial_nonterminal_names_data
               else valid)
              p = true.

  Lemma P_remove_impl {str0 valid str name name'}
        (H0 : name <> name')
        (H : P str0 valid str name')
  : P str0 (remove_nonterminal_name valid name) str name'.
  Proof.
    destruct H.
    split.
    { apply sub_names_listT_remove_2; assumption. }
    { destruct lt_dec; try assumption.
      match goal with
        | [ |- ?b = true ] => case_eq b; try reflexivity
      end.
      intro H'; exfalso.
      apply remove_nonterminal_name_2 in H'.
      destruct H'; congruence. }
  Qed.

  Let p_parse_item str0 valid s it
    := { p' : parse_of_item String G s it & Forall_parse_of_item (P str0 valid) p' }.
  Let p_parse_production str0 valid s p
    := { p' : parse_of_production String G s p & Forall_parse_of_production (P str0 valid) p' }.
  Let p_parse str0 valid s prods
    := { p' : parse_of String G s prods & Forall_parse_of (P str0 valid) p' }.
  Let p_parse_nonterminal_name str0 valid s nonterminal_name
    := { p' : parse_of_item String G  s (NonTerminal _ nonterminal_name) & Forall_parse_of_item (P str0 valid) p' }.

  Let mp_parse_item str0 valid str it
    := (*{ p' :*) minimal_parse_of_item String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str it(* & Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item p') }*).
  Let mp_parse_production str0 valid str prod
    := (*{ p' : *)minimal_parse_of_production String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str prod(* & Forall_parse_of_production P (parse_of_production__of__minimal_parse_of_production p') }*).
  Let mp_parse str0 valid str prods
    := (*{ p' : *)minimal_parse_of String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str prods(* & Forall_parse_of P (parse_of__of__minimal_parse_of p') }*).
  Let mp_parse_nonterminal_name str0 valid str nonterminal_name
    := (*{ p' : *)minimal_parse_of_name String G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name str0 valid str nonterminal_name(* & Forall_parse_of_item P (parse_of_item_name__of__minimal_parse_of_name p') }*).

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

  Local Instance methods' : @parser_computational_dataT' _ String premethods
    := {| split_stateT str0 valid g s
          := option (match g return Type with
                       | include_item it => p_parse_item str0 valid s it
                       | include_production p => p_parse_production str0 valid s p
                       | include_productions prods => p_parse str0 valid s prods
                       | include_nonterminal_name nonterminal_name => p_parse_nonterminal_name str0 valid s nonterminal_name
                     end);
          split_string_for_production str0 valid it its s
          := let orig_splits := map (fun s1s2 =>
                                       ({| string_val := string_val (fst s1s2);
                                           state_val := None |},
                                        {| string_val := string_val (snd s1s2);
                                           state_val := None |}))
                                    (@split_string_for_production _ _ _ orig_methods str0 valid it its {| state_val := (gen_state str0 valid (it::its) (string_val s)) |}) in
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
                 | _ => refine (split_string_for_production_correct _ _ _ _ {| state_val := _ |})
                 | _ => exact (fst (fst (projT2 (split_parse_of_production _))))
               end
      ).
  Defined.

  Definition parse_of__of__parse_of_item_lt' {str0 valid str nonterminal_name}
             (pf : Length str < Length str0)
             (p : p_parse_nonterminal_name str0 valid str nonterminal_name)
  : P str0 valid str nonterminal_name * p_parse str initial_nonterminal_names_data str (Lookup G nonterminal_name).
  Proof.
    refine (match projT1 p as p' in parse_of_item _ _ str' it'
                  return match it' with
                           | Terminal _ => True
                           | NonTerminal nonterminal_name' => Length str' < Length str0 -> Forall_parse_of_item (P str0 valid) p' -> P str0 valid str' nonterminal_name' * p_parse str' initial_nonterminal_names_data str' (Lookup G nonterminal_name')
                         end
            with
              | ParseTerminal _ => I
              | ParseNonTerminal _ _ p' => fun pf' H' => (fst H', existT _ p' (expand_forall_parse_of _ (snd H')))
            end pf (projT2 p)).
    clear -pf'; subst P; simpl;
    abstract (intros ??; do 2 edestruct lt_dec; intuition).
  Defined.

Definition parse_of__of__parse_of_item' {str0 valid str nonterminal_name}
           (p : p_parse_nonterminal_name str0 valid str nonterminal_name)
  : P str0 valid str nonterminal_name * p_parse str0 valid str (Lookup G nonterminal_name).
  Proof.
    refine (match projT1 p as p' in parse_of_item _ _ str' it'
                  return match it' with
                           | Terminal _ => True
                           | NonTerminal nonterminal_name' => Forall_parse_of_item (P str0 valid) p' -> P str0 valid str' nonterminal_name' * p_parse str0 valid str' (Lookup G nonterminal_name')
                         end
            with
              | ParseTerminal _ => I
              | ParseNonTerminal _ _ p' => fun H' => (fst H', existT _ p' (snd H'))
            end (projT2 p)).
  Defined.
  Definition parse_of__of__parse_of_item {str0 valid str nonterminal_name} p
    := snd (@parse_of__of__parse_of_item' str0 valid str nonterminal_name p).
  Definition parse_of__of__parse_of_item_lt {str0 valid str nonterminal_name} pf p
    := snd (@parse_of__of__parse_of_item_lt' str0 valid str nonterminal_name pf p).

  Let deloop_right str0 valid str nonterminal_name
    := p_parse str0 (remove_nonterminal_name valid nonterminal_name) str (Lookup G nonterminal_name).

  Let deloop_onceT
    := forall str0 valid str nonterminal_name prods
              (p : parse_of String G str prods)
              (pf : ~Length str < Length str0)
              (H : Forall_parse_of (P str0 valid) p),
         p_parse str0 (remove_nonterminal_name valid nonterminal_name) str prods
         + deloop_right str0 valid str nonterminal_name.

  Let deloop_once_productionT
    := forall str0 valid str nonterminal_name prod
              (p : parse_of_production String G str prod)
              (pf : ~Length str < Length str0)
              (H : Forall_parse_of_production (P str0 valid) p),
         p_parse_production str0 (remove_nonterminal_name valid nonterminal_name) str prod
         + deloop_right str0 valid str nonterminal_name.

  Definition deloop_once_item'
             (deloop_once : deloop_onceT)
             {str0 valid str nonterminal_name}
             {it}
             (p : parse_of_item String G str it)
             (pf : ~Length str < Length str0)
             (H : Forall_parse_of_item (P str0 valid) p)
  : p_parse_item str0 (remove_nonterminal_name valid nonterminal_name) str it
    + deloop_right str0 valid str nonterminal_name.
  Proof.
    refine (match p in parse_of_item _ _ str' it'
                  return ~Length str' < Length str0
                         -> Forall_parse_of_item (P str0 valid) p
                         -> p_parse_item str0 (remove_nonterminal_name valid nonterminal_name) str' it'
                            + deloop_right str0 valid str' nonterminal_name
            with
              | ParseTerminal _ => fun _ _ => inl (existT _ (ParseTerminal _ _ _) tt)
              | ParseNonTerminal nonterminal_name' str'' p' =>
                fun pf' H' =>
                  if string_dec nonterminal_name nonterminal_name'
                  then inr match @deloop_once _ _ _ nonterminal_name' _ p' pf' (snd H') with
                             | inl p''' => _
                             | inr ret => _
                           end
                  else match @deloop_once _ _ _ nonterminal_name _ p' pf' (snd H') with
                         | inl p''' => inl (existT _ (ParseNonTerminal _ (projT1 p''')) (P_remove_impl _ (fst H'), projT2 p'''))
                         | inr ret => inr ret
                       end
            end pf H);
    clear deloop_once;
    solve [ assumption
          | subst; assumption ].
  Defined.

  Definition deloop_once'
             (deloop_once : deloop_onceT)
             (deloop_once_production : deloop_once_productionT)
  : deloop_onceT.
  Proof.
    intros str0 valid str nonterminal_name pats p pf H.
    destruct p as [ str' pat' pats' p' | str' pat' pats' p' ].
    { refine match deloop_once_production str0 valid str' nonterminal_name _ p' pf H with
               | inl ret => inl (existT _ (ParseHead pats' (projT1 ret)) (projT2 ret))
               | inr ret => inr ret
             end. }
    { refine match deloop_once str0 valid str' nonterminal_name _ p' pf H with
               | inl ret => inl (existT _ (ParseTail _ (projT1 ret)) (projT2 ret))
               | inr ret => inr ret
             end. }
  Defined.

  Definition deloop_once_production'
             (deloop_once : deloop_onceT)
             (deloop_once_production : deloop_once_productionT)
  : deloop_once_productionT.
  Proof.
    intros str0 valid str nonterminal_name pat p pf H.
    destruct p as [ | str' pat' strs' pats' p' p'' ].
    { refine (inl (existT _ (ParseProductionNil _ _) tt)). }
    { (** We must discriminate based on whether or not [str] has already gotten shorter *)
      destruct (stringlike_dec str' (Empty _)) as [e|e], (stringlike_dec strs' (Empty _)) as [e'|e'];
      try (assert (pf0 : ~Length str' < Length str0)
            by (clear -pf e'; abstract (subst strs'; rewrite ?RightId, ?LeftId in pf; exact pf));
           pose proof (@deloop_once_item' (deloop_once) str0 valid _ nonterminal_name pat' p' pf0 (fst H)) as deloop_once_item);
      clear deloop_once;
      first [ assert (pf1 : ~Length strs' < Length str0)
              by (clear -pf e; abstract (subst str'; rewrite ?RightId, ?LeftId in pf; exact pf));
              specialize (deloop_once_production str0 valid _ nonterminal_name pats' p'' pf1 (snd H))
            | clear deloop_once_production ].
      { (** empty, empty *)
        destruct deloop_once_item as [ret|ret];
        [ | right; subst; rewrite ?LeftId, ?RightId; assumption ].

        Focus 2.
        specialize (fun pf X
        simpl in H.

      specialize (fun h' pf
                        => @minimal_parse_of_name__of__parse_of_name
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            change (S ((size_of_parse_item p0')
                       + (size_of_parse_production p1'))
                    < S h') in H_h.
            apply Lt.lt_S_n in H_h.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_l _ _) H_h) as H_h0.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_r _ _) H_h) as H_h1.
            clear H_h.
            pose proof (fun valid Hinit => @minimal_parse_of_item__of__parse_of_item _ h'  minimal_parse_of_name__of__parse_of_name _ (transitivity (str_le1_append _ _ _) pf) valid _ p0' H_h0 Hinit (fst H_forall)) as p_it.
            pose proof (fun valid Hinit => @minimal_parse_of_production__of__parse_of_production h' minimal_parse_of_name__of__parse_of_name _ (transitivity (str_le2_append _ _ _) pf) valid _ p1' H_h1 Hinit (snd H_forall)) as p_prod.
            destruct (stringlike_dec str' (Empty _)), (stringlike_dec str'' (Empty _));
              subst.
            { (* empty, empty *)
              specialize (p_it valid' Hinit'); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* empty, nonempty *)
              specialize (p_it initial_names_data (reflexivity _)); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t;
                min_parse_prod_pose_t;
                min_parse_prod_t. }
            { (* nonempty, empty *)
              specialize (p_it valid' Hinit'); specialize (p_prod initial_names_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t;
                min_parse_prod_pose_t;
                min_parse_prod_t. }
            { (* nonempty, nonempty *)
              specialize (p_it initial_names_data (reflexivity _)); specialize (p_prod initial_names_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t;
                min_parse_prod_pose_t;
                min_parse_prod_t. } }

refine (match
                 deloop_once_item' (@deloop_once) p' pf H,
                 deloop_once_production p'' pf H
               with
                 | _, _ => _
               end).

    { refine match deloop_once_production str0 valid str' nonterminal_name _ p' pf H with
               | inl ret => inl (existT _ (ParseHead pats' (projT1 ret)) (projT2 ret))
               | inr ret => inr ret
             end. }
    { refine match deloop_once str0 valid str' nonterminal_name _ p' pf H with
               | inl ret => inl (existT _ (ParseTail _ (projT1 ret)) (projT2 ret))
               | inr ret => inr ret
             end. }
  Defined.



  Fixpoint deloop_once
  {str0 valid str nonterminal_name}
           {pats}
           (p : parse_of String G str pats)
    := match p in parse_of _ _ str' pats'
             return ~Length str' < Length str0
                    -> Forall_parse_of (P str0 valid) p
                    -> p_parse str0 (remove_nonterminal_name valid nonterminal_name) str' pats'
                       + p_parse str0 (remove_nonterminal_name valid nonterminal_name) str' (Lookup G nonterminal_name)
       with
         | ParseHead str' pat' pats' p'
           => fun pf H
              => match deloop_once_production p' pf H with
                   | inl ret => inl (existT _ (ParseHead pats' (projT1 ret)) ((projT2 ret) : Forall_parse_of (P str0 (remove_nonterminal_name valid nonterminal_name)) (ParseHead _ (projT1 ret))))
                   | inr ret => inr ret
                 end
         | ParseTail _ _ _ p'
           => fun pf H
              => match deloop_once p' pf H with
                   | inl ret => inl (existT _ (ParseTail (projT1 ret)) (projT2 ret))
                   | inr ret => inr ret
                 end
       end
  with deloop_once_production
         {str0 valid str nonterminal_name}
         {pat}
         (p : parse_of_production String G str pat)
       := match p in parse_of_production _ _ str' pat'
                return ~Length str' < Length str0
                       -> Forall_parse_of_production (P str0 valid) p
                       -> p_parse_production str0 (remove_nonterminal_name valid nonterminal_name) str' pat'
                          + p_parse str0 (remove_nonterminal_name valid nonterminal_name) str' (Lookup G nonterminal_name)
          with
            | ParseProductionNil => fun _ _ => inl (existT _ ParseProductionNil tt)
            | ParseProductionCons str pat strs pats p' p''
              => fun pf H
                 => match
                     deloop_once_item' (@deloop_once) p' pf H,
                     deloop_once_production p'' pf H
                   with
                     | _ => admit
                   end
          end.
    with expand_forall_parse_of_production {str pat} {p : parse_of_production String G str pat}
         : Forall_parse_of_production P p -> Forall_parse_of_production P' p
         := match p return Forall_parse_of_production P p -> Forall_parse_of_production P' p with
              | ParseProductionNil => fun x => x
              | ParseProductionCons str pat strs pats p' p''
                => fun ab => (expand_forall_parse_of_item' (@expand_forall_parse_of) (fst ab),
                              expand_forall_parse_of_production (snd ab))
            end.

    Global Arguments expand_forall_parse_of : simpl never.
    Global Arguments expand_forall_parse_of_production : simpl never.

    Definition expand_forall_parse_of_item {str it} {p : parse_of_item String G str it}
      := @expand_forall_parse_of_item' _ (@expand_forall_parse_of) str it p.


  Local Instance strdata : @parser_computational_strdataT _ String G _ _
    := {| lower_nonterminal_name_state str0 valid nonterminal_name str st := st;
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
          lift_lookup_nonterminal_name_state_eq1 str0 valid nonterminal_name str pf := option_map _(*parse_of__of__parse_of_item*) |}.



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

          Let alt := False (*{ nonterminal_name : string
                     | is_valid_nonterminal_name initial_nonterminal_names_data nonterminal_name = true
                       /\ is_valid_nonterminal_name valid nonterminal_name = false }*).

          Section T_nonterminal_name.
            Context (name : string) (str : StringWithSplitState String (split_stateT (include_nonterminal_name _ name))).
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
            Context (it : item CharType) (str : StringWithSplitState String (split_stateT it)).

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
            Context (prod : production CharType) (str : StringWithSplitState String (split_stateT prod)).

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
            Context (prods : productions CharType) (str : StringWithSplitState String (split_stateT prods)).

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


        Definition split_list_completeT
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

        (*Lemma H_prod_split'_helper
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
          end.

        (*Local Ltac should_
        Local Ltac pre_congruence_avoid_anomalies
          := repeat match goal with
                      | [ H : ?T |- _ ]*)

        Local Ltac t' :=
          first [ t''
                (*| congruence*)
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
              (s1 : StringWithSplitState String (split_stateT it))
              (s2 : StringWithSplitState String (split_stateT its))
              (str : StringWithSplitState String (split_stateT (it :: its : production CharType)))
        : let a1 := DependentlyTyped.T_item_success str0 valid it s1 in
          let a2 := DependentlyTyped.T_production_success str0 valid its s2 in
          let ret :=
              DependentlyTyped.T_production_success str0 valid (it :: its) str in
          str ≤s str0 ->
          s1 ++ s2 =s str ->
          In (s1, s2) (split_string_for_production it its str) -> a1 -> a2 -> ret.
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

        Let H_prod_splitT' str0 valid it its str st
          := split_string_lift_T str0 valid it its {| string_val := str ; state_val := st |} (split_string_for_production it its {| string_val := str ; state_val := st |}).

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

        Start Profiling.
        Time Global Program Instance minimal_parser_dependent_types_extra_data
             (H_prod_split' : forall str0 valid it its str, @H_prod_splitT' str0 valid it its str None)
               (*(split_list_complete : forall str0 valid it its str pf, @split_list_completeT str0 valid valid it its str pf (split_string_for_production it its str))*)
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
        Obligation 12. t. Defined.
        Obligation 13. t. Defined.
        Obligation 14. t. Defined.
        Obligation 11. t. Defined.
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
        Obligation 15.
        simpl.
        intros.
        assert (str = str0 :> String).
        { destruct_head @str_le.
          { exfalso; eauto with nocore. }
          { assumption. } }
        subst.
        clear H H0.
        hnf.
        repeat t''0; [ | solve [ t ] ].
        clear H.
        hnf in p.
        destruct p.
        dependent destruction x.
        destruct f.

        hnf in p0.


        do 10 t''.
        t''.
        t''.
        t''.
        t''.
        t''.
        t''.
        destruct_head prod.
        destruct_head sum; repeat t''.
        t''.
        match goal with
        end.
        simpl split_string_for_production in *.
        t''.
        t''.
        simpl in X.
        destruct_head prod.
        destruct_head sum.
        repeat t''.
        repeat t''.
        repeat t''.
simpl in *.
        do 10 (simpl in *; t'').
        t''.
        t''.
        t''.
        t''.
        t''.
        t''.
        t''; simpl in *.
        t''; simpl in *.
        t''; simpl in *.
        t''; simpl in *.
        t''; simpl in *.
        t''; simpl in *.
        t''; simpl in *.
        t''; simpl in *.
        simpl in X.
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
        simpl in s.
t. Defined.
        Obligation 16. t. Defined.
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
        Next Obligation. simpl.
                        do 5 t''.
                        do 5 t''.
                        do 5 t''.
                        t''.
                        t''.
                        t''.
                        t''.
                        t''.
                        t''.
                        t''.
                        t''.
                        t''.
                        match goal with
                        end.
                        t''.
                        do 5 t''.
                        do 5 t''.
                        do 5 t''.
                        do 5 t''.
                        do 5 t''.
t. Defined.

        Obligation 15.
   (forall (str0 : String) (valid : nonterminal_names_listT)
      (it : item CharType) (its : production CharType)
      (str : String), H_prod_splitT' str0 valid None) ->
   forall (str0 : String) (valid : nonterminal_names_listT)
     (nonterminal_name : string)
     (str : StringWithSplitState String
              (split_stateT
                 (include_nonterminal_name CharType nonterminal_name))),
   let ret :=
     DependentlyTyped.T_nonterminal_name_failure str0 valid nonterminal_name
       str in
   let arg :=
     DependentlyTyped.T_productions_failure str0
       (remove_nonterminal_name valid nonterminal_name)
       (G nonterminal_name)
       (lift_StringWithSplitState lift_lookup_nonterminal_name_state str) in
   ~ Length str < Length str0 -> arg -> ret



t. repeat t''.
        apply remove_nonterminal_name_2 in H3.

        exists x.
        repeat t''.
        destruct H3.
        repeat t''.
        split.
        repeat t''.
        repeat t''.
        hnf in p0.
        repeat t''.
        hnf in p0.
        SerachAbout


        dependent destruction x.
        repeat t''.
        destruct f.
        hnf in p0.
        SearchAbout sub_names_listT.
        pose (sub_names_listT_remove is_valid_nonterminal_name remove_nonterminal_name remove_name_1 _ _ _ H3).
        SearchAbout sub_names_listT.
        unique pose proof (
 Defined.
        Obligation 16.

        t.
        { repeat t''.
          dependent destruction x.
          repeat t''.
          destruct f.
          repeat t''.
          hnf in p0.
          repeat t''.
          hnf in H3.
          specialize (H3 _ p0).
          simpl in f.
          destruct f.
          hnf in p0.

 t. Defined.
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
        Next Obligation. t. Defined.
        Next Obligation. t.
                         repeat t''.
Set Printing All.
            lazymatch goal with | [ H : sub_names_listT _ ?x ?y -> _ |- _ ] => specialize (H (reflexivity _)) end.
                         specialize (X (reflexivity _)).
                         Obligations.
 Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
          Start Profiling.
          t.
          Show Profile.

          repeat t''0.
          simpl in *.
          Show Profile.
          { repeat t''.


          repeat t''.

t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
Definition heap_is_star (H1 H2 : hprop) : hprop := ...
Open Scope heap_scope.
Bind Scope heap_scope with hprop.
Delimit Scope heap_scope with h.
Notation "P ==>+ Q" := (pred_le P (heap_is_star P Q))
  (at level 55) : heap_scope_advanced.


which I could (finally) solve by adding (non-intuitive) explicit scopes:

Notation "P ==>+ Q" := (pred_le P%h (heap_is_star P Q))
  (at level 55) : heap_scope_advanced.

 Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. repeat t''.
                         simpl in H.
                         simpl in *.
                         Focus 2.
                         simpl in *.
                         subst_body.
                         simpl in *.
                         repeat t''.
                         dependent destruction x.

                         repeat t''.
                         simpl in *.
                         t.
                         apply X.
                         exists m.
                         t.
                         t.
                         simpl in *.
                         apply X0.
                         exists x.
                         t.
                         simpl in *.
                         repeat t'.

                         dependent destruction x.
                         simpl in *.
                         repeat t''.
                         repeat t'.

                         Obligations.
Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.
        Obligations.
        Next Obligation.
          subst_body; simpl in *.

          repeat t''.
          subst_body.
          repeat t''.
          dependent destruction x; t.
          repeat t''.

          Print minimal_parse_of.
          Focus 2.
          lazymatch goal with
          end.



        Obligation 16. t. repeat t''.
        subst_body. simpl in *.
 Defined. subst_body. repeat t''.

 Defined.
        Next Obligation.
repeat t''.

 Defined.
        Next Obligation. t. Defined.
        Next Obligation. t. Defined.


        Defined.
        Next Obligation. t. Defined.

          Next Obligation
          simpl.
 do 25 try t''.
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
                         simpl in *.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         Show Profile.
                         t''.

      (s1 s2 : StringWithSplitState A (fun x => option (P x)))
:
                         match goal with
                           | [ H : {| state_val := Some _ |} = {| state_val := None |} |- _ ]
                             => exfalso; clear -H
                         end.
                         apply (f_equal_dep (@state_val _ _)) in H0.
                         refine (_, f0).
                         exact f.
                         match goal with
            | [ b : Forall_parse_of_production _ _ |- Forall_parse_of_production _ _ ]
              => refine (_, b)
end.
                         t''.

                         lazymatch goal with
                         | [ x : minimal_parse_of_item _ _ _ _ _ _ _ _ _, y : minimal_parse_of_production _ _ _ _ _ _ _ _ _, H : _ \/ _ |- _ ] => idtac end.
                         match goal with [ |- @sigT ?A _ ]
                           => idtac
                         end.

exists (MinParseProductionCons H x y : A)

t000.
Show Profile.
                         :
                         SearchAbout ((_, _) = (_, _)).
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         t''.
                         do 10 try t''.
                         t''.
                         let H := match goal with H : _ \/ False |- _ => constr:H end.

                         t''.
                         Show Profile.
          simpl.
        Obligation 8. t. Defined.
        Obligation 9. t. Defined.
        Obligation 10. t. Defined.
        Obligation 8. t. Defined.
        Obligations.
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
