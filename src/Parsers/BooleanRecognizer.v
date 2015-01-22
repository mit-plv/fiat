(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Omega.
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

(** TODO: Allow stubbing out of individual sub-parse methods *)
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

  Section bool.
    Context (split_string_for_production
             : forall (str0 : StringWithSplitState String split_stateT) (prod : production CharType), list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
            (split_string_for_production_correct
             : forall (str0 : StringWithSplitState String split_stateT) prod,
                 List.Forall (fun s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                              => (fst s1s2 ++ snd s1s2 =s str0) = true)
                             (split_string_for_production str0 prod)).

    Section parts.
      Section item.
        (** We require that the list of names be non-empty; we
            do this by passing the first element separately, rather
            than invoking dependent types and proofs. *)
        Context (str : StringWithSplitState String split_stateT)
                (str_matches_name : string -> bool).

        Definition parse_item (it : item CharType) : bool
          := match it with
               | Terminal ch => [[ ch ]] =s str
               | NonTerminal name => str_matches_name name
             end.
      End item.

      Section production.
        Variable str0 : StringWithSplitState String split_stateT.
        Variable parse_name : forall (str : StringWithSplitState String split_stateT),
                                       str ≤s str0
                                       -> string
                                       -> bool.

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Fixpoint parse_production
                 (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                 (prod : production CharType)
        : bool.
        Proof.
          refine match prod with
                   | nil =>
                     (** 0-length production, only accept empty *)
                     str =s Empty _
                   | it::its
                     => let parse_production' := fun str pf => @parse_production str pf its in
                        fold_right
                          orb
                          false
                          (map (fun s1s2p => (parse_item (fst (proj1_sig s1s2p))
                                                         (@parse_name (fst (proj1_sig s1s2p))
                                                                             _)
                                                         it)
                                               && parse_production' (snd (proj1_sig s1s2p)) _)%bool
                               (combine_sig (split_string_for_production_correct str prod)))
                 end;
          revert pf; clear; intros;
          abstract (
              destruct str;
              repeat first [ progress destruct_head sig
                           | progress destruct_head and
                           | etransitivity; eassumption
                           | etransitivity; try eassumption; []
                           | progress subst
                           | idtac; match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end
                           | apply str_le1_append
                           | apply str_le2_append ]
            ).
        Defined.
      End production.

      Section productions.
        Variable str0 : StringWithSplitState String split_stateT.
        Variable parse_name : forall (str : StringWithSplitState String split_stateT)
                                     (pf : str ≤s str0),
                                string -> bool.

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (prods : productions CharType)
        : bool
          := fold_right orb
                        false
                        (map (parse_production str0 parse_name str pf)
                             prods).
      End productions.


      Section names.
        Section step.
          Context (str0 : StringWithSplitState String split_stateT) (valid_list : names_listT)
                  (parse_name
                   : forall (p : StringWithSplitState String split_stateT * names_listT),
                       prod_relation (ltof _ (fun s : StringWithSplitState _ _ => Length s)) names_listT_R p (str0, valid_list)
                       -> forall str : StringWithSplitState String split_stateT, str ≤s fst p -> string -> bool).

          Definition parse_name_step
                     (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (name : string)
          : bool
            := match lt_dec (Length str) (Length str0), Sumbool.sumbool_of_bool (is_valid_name valid_list name) with
                 | left pf', _ =>
                   (** [str] got smaller, so we reset the valid names list *)
                   parse_productions
                     _
                     (@parse_name
                        (str, initial_names_data)
                        (or_introl pf'))
                     _
                     (or_intror eq_refl)
                     (Lookup G name)
                 | right pf', left H' =>
                   (** [str] didn't get smaller, so we cache the fact that we've hit this name already *)
                   (** It was valid, so we can remove it *)
                   parse_productions
                     _
                     (@parse_name
                        (str0, remove_name valid_list name)
                        (or_intror (conj eq_refl (remove_name_dec H'))))
                     _
                     (or_intror eq_refl)
                     (Lookup G name)
                 | right _, right _
                   => (** oops, we already saw this name in the past.  ABORT! *)
                   false
               end.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_name_or_abort
          : forall (p : StringWithSplitState String split_stateT * names_listT) (str : StringWithSplitState String split_stateT),
              str ≤s fst p
              -> string
              -> bool
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
          : bool
            := @parse_name_or_abort (str, initial_names_data) str
                                    (or_intror eq_refl) name.
        End wf.
      End names.
    End parts.
  End bool.
End recursive_descent_parser.

Section recursive_descent_parser_list.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Definition rdp_list_names_listT : Type := list string.
  Definition rdp_list_is_valid_name : rdp_list_names_listT -> string -> bool
    := fun ls nt => if in_dec string_dec nt ls then true else false.
  Definition rdp_list_remove_name : rdp_list_names_listT -> string -> rdp_list_names_listT
    := fun ls nt =>
         filter (fun x => if string_dec nt x then false else true) ls.
  Definition rdp_list_names_listT_R : rdp_list_names_listT -> rdp_list_names_listT -> Prop
    := ltof _ (@List.length _).
  Lemma filter_list_dec {T} f (ls : list T) : List.length (filter f ls) <= List.length ls.
  Proof.
    induction ls; trivial; simpl in *.
    repeat match goal with
             | [ |- context[if ?a then _ else _] ] => destruct a; simpl in *
             | [ |- S _ <= S _ ] => solve [ apply Le.le_n_S; auto ]
             | [ |- _ <= S _ ] => solve [ apply le_S; auto ]
           end.
  Qed.
  Lemma rdp_list_remove_name_dec : forall ls prods,
                                            @rdp_list_is_valid_name ls prods = true
                                            -> @rdp_list_names_listT_R (@rdp_list_remove_name ls prods) ls.
  Proof.
    intros.
    unfold rdp_list_is_valid_name, rdp_list_names_listT_R, rdp_list_remove_name, ltof in *.
    edestruct in_dec; [ | discriminate ].
    match goal with
      | [ H : In ?prods ?ls |- context[filter ?f ?ls] ]
        => assert (~In prods (filter f ls))
    end.
    { intro H'.
      apply filter_In in H'.
      destruct H' as [? H'].
      edestruct string_dec; congruence. }
    { match goal with
        | [ |- context[filter ?f ?ls] ] => generalize dependent f; intros
      end.
      induction ls; simpl in *; try congruence.
      repeat match goal with
               | [ |- context[if ?x then _ else _] ] => destruct x; simpl in *
               | [ H : _ \/ _ |- _ ] => destruct H
               | _ => progress subst
               | [ H : ~(_ \/ _) |- _ ] => apply Decidable.not_or in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : ?x <> ?x |- _ ] => exfalso; apply (H eq_refl)
               | _ => apply Lt.lt_n_S
               | _ => apply Le.le_n_S
               | _ => apply filter_list_dec
               | [ H : _ -> _ -> ?G |- ?G ] => apply H; auto
             end. }
  Qed.
  Lemma rdp_list_ntl_wf : well_founded rdp_list_names_listT_R.
  Proof.
    unfold rdp_list_names_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.

  Lemma rdp_list_remove_name_1
  : forall ls ps ps',
      rdp_list_is_valid_name (rdp_list_remove_name ls ps) ps' = true
      -> rdp_list_is_valid_name ls ps' = true.
  Proof.
    unfold rdp_list_is_valid_name, rdp_list_remove_name.
    repeat match goal with
             | _ => exfalso; congruence
             | _ => reflexivity
             | [ |- appcontext[if ?E then _ else _] ] => destruct E
             | _ => intro
             | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
           end.
  Qed.

  Lemma rdp_list_remove_name_2
  : forall ls ps ps',
      rdp_list_is_valid_name (rdp_list_remove_name ls ps) ps' = false
      <-> rdp_list_is_valid_name ls ps' = false \/ ps = ps'.
  Proof.
    unfold rdp_list_is_valid_name, rdp_list_remove_name.
    repeat match goal with
             | _ => exfalso; congruence
             | _ => reflexivity
             | _ => progress subst
             | _ => intro
             | [ H : context[In _ (filter _ _)] |- _ ] => rewrite filter_In in H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
             | [ |- true = false \/ _ ] => right
             | [ |- ?x = ?x \/ _ ] => left; reflexivity
             | [ H : ~(_ /\ ?x = ?x) |- _ ] => specialize (fun y => H (conj y eq_refl))
             | [ H : _ \/ _ |- _ ] => destruct H
             | [ |- _ <-> _ ] => split
             | [ H : appcontext[if ?E then _ else _] |- _ ] => destruct E
             | [ |- appcontext[if ?E then _ else _] ] => destruct E
           end.
  Qed.
End recursive_descent_parser_list.

Definition String_with_no_state {CharType} (String : string_like CharType) := StringWithSplitState String True.

Definition default_String_with_no_state {CharType} (String : string_like CharType) (s : String) : String_with_no_state String
  := {| string_val := s ; state_val := I |}.

Coercion default_string_with_no_state (s : string) : String_with_no_state string_stringlike
  := default_String_with_no_state string_stringlike s.

Identity Coercion unfold_String_with_no_state : String_with_no_state >-> StringWithSplitState.

(** TODO: move this elsewhere *)
Section example_parse_string_grammar.
  Fixpoint make_all_single_splits' (str : string) : list (String_with_no_state string_stringlike * String_with_no_state string_stringlike)
    := ((""%string : String_with_no_state string_stringlike),
        (str : String_with_no_state string_stringlike))
         ::(match str with
              | ""%string => nil
              | String.String ch str' =>
                map (fun p : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                     => ((String.String ch (string_val (fst p)) : String_with_no_state string_stringlike),
                         snd p))
                    (make_all_single_splits' str')
            end).

  Definition make_all_single_splits (str : String_with_no_state string_stringlike)
    := make_all_single_splits' (string_val str).

  Lemma make_all_single_splits_correct_eq (str : String_with_no_state string_stringlike)
  : List.Forall (fun strs : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                 => string_val (fst strs) ++ string_val (snd strs) = string_val str)%string (make_all_single_splits str).
  Proof.
    destruct str as [str ?].
    induction str; simpl in *; constructor; auto.
    apply Forall_map.
    unfold compose; simpl in *.
    revert IHstr; apply Forall_impl; intros.
    subst; trivial.
  Qed.

  Local Opaque string_dec.
  Lemma make_all_single_splits_correct_seq (str : String_with_no_state string_stringlike)
  : List.Forall (fun strs : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                 => (fst strs ++ snd strs =s str) = true)%string_like (make_all_single_splits str).
  Proof.
    destruct str as [str ?].
    induction str; simpl; constructor; simpl; auto.
    { rewrite string_dec_refl; reflexivity. }
    { apply Forall_map.
      unfold compose; simpl.
      revert IHstr; apply Forall_impl; intros.
      match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end.
      simpl in *; subst; rewrite string_dec_refl; reflexivity. }
  Qed.

  Lemma make_all_single_splits_correct_str_le (str : String_with_no_state string_stringlike)
  : List.Forall (fun strs : String_with_no_state string_stringlike * String_with_no_state string_stringlike
                 => fst strs ≤s str /\ snd strs ≤s str)%string (make_all_single_splits str).
  Proof.
    generalize (make_all_single_splits_correct_eq str).
    apply Forall_impl.
    destruct str as [str ?]; simpl.
    intros; subst; split;
    first [ apply str_le1_append
          | apply str_le2_append ].
  Qed.

  Local Hint Resolve NPeano.Nat.lt_lt_add_l NPeano.Nat.lt_lt_add_r NPeano.Nat.lt_add_pos_r NPeano.Nat.lt_add_pos_l : arith.
  Local Hint Resolve str_le1_append str_le2_append.

  Variable G : grammar Ascii.ascii.

  Definition brute_force_make_parse_of : @String Ascii.ascii string_stringlike
                                         -> string
                                         -> bool
    := @parse_name
         _
         _
         G
         _
         (Valid_nonterminal_symbols G)
         rdp_list_is_valid_name
         rdp_list_remove_name
         _
         rdp_list_remove_name_dec rdp_list_ntl_wf
         _
         (fun (str : String_with_no_state string_stringlike) _ => make_all_single_splits str)
         (fun str0 _ => make_all_single_splits_correct_seq str0).
End example_parse_string_grammar.

Module example_parse_empty_grammar.
  Definition make_parse_of : forall (str : string)
                                    (name : string),
                               bool
    := @brute_force_make_parse_of (trivial_grammar _).



  Definition parse : string -> bool
    := fun str => make_parse_of str (trivial_grammar string).

  Time Compute parse "".
  Check eq_refl : true = parse "".
  Time Compute parse "a".
  Check eq_refl : false = parse "a".
  Time Compute parse "aa".
  Check eq_refl : false = parse "aa".
End example_parse_empty_grammar.

Section examples.
  Section ab_star.

    Fixpoint production_of_string (s : string) : production Ascii.ascii
      := match s with
           | EmptyString => nil
           | String.String ch s' => (Terminal ch)::production_of_string s'
         end.

    Coercion production_of_string : string >-> production.

    Fixpoint list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
      := match ls with
           | nil => fun _ => default
           | (str, t)::ls' => fun s => if string_dec str s
                                       then t
                                       else list_to_productions default ls' s
         end.

    Delimit Scope item_scope with item.
    Bind Scope item_scope with item.
    Delimit Scope production_scope with production.
    Delimit Scope production_assignment_scope with prod_assignment.
    Bind Scope production_scope with production.
    Delimit Scope productions_scope with productions.
    Delimit Scope productions_assignment_scope with prods_assignment.
    Bind Scope productions_scope with productions.
    Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions _)%productions) (at level 100) : production_assignment_scope.
    Notation "[[[ x ;; .. ;; y ]]]" :=
      (list_to_productions (nil::nil) (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.

    Local Open Scope string_scope.
    Notation "<< x | .. | y >>" :=
      (@cons (production _) (x)%production .. (@cons (production _) (y)%production nil) .. ) : productions_scope.

    Notation "$< x $ .. $ y >$" := (cons (NonTerminal _ x) .. (cons (NonTerminal _ y) nil) .. ) : production_scope.

    Definition ab_star_grammar : grammar Ascii.ascii :=
      {| Start_symbol := "ab_star";
         Lookup := [[[ ("" ::== (<< "" >>)) ;;
                       ("ab" ::== << "ab" >>) ;;
                       ("ab_star" ::== << $< "" >$
                                        | $< "ab" $ "ab_star" >$ >> ) ]]]%prods_assignment;
         Valid_nonterminal_symbols := (""::"ab"::"ab_star"::nil)%string |}.

    Definition make_parse_of : forall (str : string)
                                      (name : string),
                                 bool
      := @brute_force_make_parse_of ab_star_grammar.



    Definition parse : string -> bool
      := fun str => make_parse_of str ab_star_grammar.

    Time Eval lazy in parse "".
    Check eq_refl : parse "" = true.
    Time Eval lazy in parse "a".
    Check eq_refl : parse "a" = false.
    Time Eval lazy in parse "ab".
    Check eq_refl : parse "ab" = true.
    Time Eval lazy in parse "aa".
    Check eq_refl : parse "aa" = false.
    Time Eval lazy in parse "ba".
    Check eq_refl : parse "ba" = false.
    Time Eval lazy in parse "aba".
    Check eq_refl : parse "aba" = false.
    Time Eval lazy in parse "abab".
    Time Eval lazy in parse "ababab".
    Check eq_refl : parse "ababab" = true.
  (* For debugging: *)(*
  Goal True.
    pose proof (eq_refl (parse "abab")) as s.
    unfold parse in s.
    unfold make_parse_of in s.
    unfold brute_force_make_parse_of in s.
    cbv beta zeta delta [parse_names] in s.
    cbv beta zeta delta [parse_names_or_abort] in s.
    rewrite Init.Wf.Fix_eq in s.
    Ltac do_compute_in c H :=
      let c' := (eval compute in c) in
      change c with c' in H.
    do_compute_in (lt_dec (Length string_stringlike "abab"%string) (Length string_stringlike "abab"%string)) s.
    change (if in_right then ?x else ?y) with y in s.
    cbv beta zeta delta [rdp_list_is_valid_name] in s.
                       *)
  End ab_star.
End examples.
