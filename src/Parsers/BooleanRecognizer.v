(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Omega.
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

(** TODO: move this elsewhere *)
Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT)
          (names_listT_R : names_listT -> names_listT -> Prop)
          (remove_name_dec : forall ls name, is_valid_name ls name = true
                                                     -> names_listT_R (remove_name ls name) ls)
          (ntl_wf : well_founded names_listT_R).
  Section bool.
    Context (split_string_for_production
             : forall (str0 : String) (prod : production CharType), list (String * String))
            (split_string_for_production_correct
             : forall str0 prod,
                 List.Forall (fun s1s2 => (fst s1s2 ++ snd s1s2 =s str0) = true)
                             (split_string_for_production str0 prod)).

    Section parts.
      Section item.
        Context (str : String)
                (str_matches_name : string -> bool).

        Definition parse_item (it : item CharType) : bool
          := match it with
               | Terminal ch => [[ ch ]] =s str
               | NonTerminal name => str_matches_name name
             end.
      End item.

      Section production.
        Variable str0 : String.
        Variable parse_name : forall (str : String),
                                str ≤s str0
                                -> string -> bool.

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Fixpoint parse_production
                 (str : String) (pf : str ≤s str0)
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
        Section step.
          Variable str0 : String.
          Variable parse_name : forall (str : String)
                                       (pf : str ≤s str0),
                                  string -> bool.

          (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
          Definition parse_name_step (str : String) (pf : str ≤s str0) (name : string)
          : bool
            := fold_right orb
                          false
                          (map (parse_production parse_name pf)
                               (Lookup G name)).
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_name_or_abort
          : forall (p : String * names_listT) (str : String),
              str ≤s fst p
              -> string
              -> bool
            := @Fix3
                 (prod String names_listT) _ _ _
                 _ (@well_founded_prod_relation
                      String
                      names_listT
                      _
                      _
                      (well_founded_ltof _ Length)
                      ntl_wf)
                 _
                 (fun sl parse_name str pf (name : string)
                  => let str0 := fst sl in
                     let valid_list := snd sl in
                     match Sumbool.sumbool_of_bool (is_valid_name valid_list name) with
                       | right H' (** the name isn't valid, so we say, no parse *)
                         => false
                       | left H'
                         => match lt_dec (Length str) (Length str0) with
                              | left pf' =>
                                (** [str] got smaller, so we reset the valid productions list *)
                                parse_name_step
                                  (parse_name
                                     (str, initial_names_data)
                                     (or_introl pf'))
                                  (or_intror eq_refl)
                                  name
                              | right pf' =>
                                (** [str] didn't get smaller, so we cache the fact that we've hit this name already *)
                                parse_name_step
                                  (parse_name
                                     (str0, remove_name valid_list name)
                                     (or_intror (conj eq_refl (remove_name_dec H'))))
                                  (or_intror eq_refl)
                                  name
                            end
                     end).

          Definition parse_name (str : String) (name : string)
          : bool
            := @parse_name_or_abort (str, initial_names_data) str
                                    (or_intror eq_refl) name.
        End wf.
      End productions.
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
  Lemma rdp_list_remove_name_dec
  : forall ls name,
      @rdp_list_is_valid_name ls name = true
      -> @rdp_list_names_listT_R (@rdp_list_remove_name ls name) ls.
  Proof.
    intros.
    unfold rdp_list_is_valid_name, rdp_list_names_listT_R, rdp_list_remove_name, ltof in *.
    edestruct in_dec; [ | discriminate ].
    match goal with
      | [ H : In ?name ?ls |- context[filter ?f ?ls] ]
        => assert (~In name (filter f ls))
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
End recursive_descent_parser_list.

(** TODO: move this elsewhere *)
Section example_parse_string_grammar.
  Fixpoint make_all_single_splits (str : string) : list (string * string)
    := ((""%string, str))
         ::(match str with
              | ""%string => nil
              | String.String ch str' =>
                map (fun p => (String.String ch (fst p), snd p))
                    (make_all_single_splits str')
            end).

  Lemma make_all_single_splits_correct_eq str
  : List.Forall (fun strs => fst strs ++ snd strs = str)%string (make_all_single_splits str).
  Proof.
    induction str; simpl; constructor; auto.
    apply Forall_map.
    unfold compose; simpl.
    revert IHstr; apply Forall_impl; intros.
    subst; trivial.
  Qed.

  Local Opaque string_dec.
  Lemma make_all_single_splits_correct_seq str
  : List.Forall (fun strs : string_stringlike * string_stringlike
                 => (fst strs ++ snd strs =s str) = true)%string_like (make_all_single_splits str).
  Proof.
    induction str; simpl; constructor; simpl; auto.
    { rewrite string_dec_refl; reflexivity. }
    { apply Forall_map.
      unfold compose; simpl.
      revert IHstr; apply Forall_impl; intros.
      match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end.
      subst; rewrite string_dec_refl; reflexivity. }
  Qed.

  Lemma make_all_single_splits_correct_str_le (str : string_stringlike)
  : List.Forall (fun strs => fst strs ≤s str /\ snd strs ≤s str)%string (make_all_single_splits str).
  Proof.
    generalize (make_all_single_splits_correct_eq str).
    apply Forall_impl.
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
         (fun (str : string_stringlike) _ => make_all_single_splits str)
         (fun str0 _ => make_all_single_splits_correct_seq str0).
End example_parse_string_grammar.

Module example_parse_empty_grammar.
  Definition make_parse_of : forall (str : string)
                                    (name : string),
                               bool
    := @brute_force_make_parse_of (trivial_grammar _).



  Definition parse : string -> bool
    := fun str => make_parse_of str (trivial_grammar string_stringlike).

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
  (*Goal True.
    pose proof (eq_refl (parse "ab")) as s.
    unfold parse in s.
    unfold make_parse_of in s.
    unfold brute_force_make_parse_of in s.
    cbv beta zeta delta [parse_name] in s.
    cbv beta zeta delta [parse_name_or_abort] in s.
    rewrite Fix3_eq in s.
    Opaque Fix3.
    Ltac do_compute_in c H :=
      let c' := (eval compute in c) in
      change c with c' in H.
    Opaque parse_name_step.
    simpl in s.
    Transparent parse_name_step.
    cbv beta zeta delta [parse_name_step] in s.
    Opaque parse_production.
    do_compute_in (ab_star_grammar "ab_star") s.
    unfold map in s.
    unfold fold_right in s.
    Transparent parse_production.
    unfold parse_production in s.
    Transparent Fix3.

    Opaque parse_item.

    simpl in s.
    do_compute_in (combine_sig (make_all_single_splits_correct_seq "ab")) s.
    Unset Printing Notations.
    do_compute_in ($< "" >$)%production s.
    cbv beta zeta delta [parse_production] in s.
    simpl ab_star_grammar
    unfold map in s.
    cbv beta in s.
    lazy in s.

     parse_name_step.

    simpl dec in s.
    simpl lt_dec in s.

    do_compute_in (lt_dec (Length string_stringlike "abab"%string) (Length string_stringlike "abab"%string)) s.
    change (if in_right then ?x else ?y) with y in s.
    cbv beta zeta delta [rdp_list_is_valid_name] in s.

    Check eq_refl : parse "ab" = true.*)
    Time Eval lazy in parse "aa".
    Check eq_refl : parse "aa" = false.
    Time Eval lazy in parse "ba".
    Check eq_refl : parse "ba" = false.
    Time Eval lazy in parse "aba".
    Check eq_refl : parse "aba" = false.
    Time Eval lazy in parse "abab".
    Time Eval lazy in parse "ababab".
    (*Check eq_refl : parse "ababab" = true.*)
  (* For debugging: *)(*
  Goal True.
    pose proof (eq_refl (parse "abab")) as s.
    unfold parse in s.
    unfold make_parse_of in s.
    unfold brute_force_make_parse_of in s.
    cbv beta zeta delta [parse_productions] in s.
    cbv beta zeta delta [parse_productions_or_abort] in s.
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
