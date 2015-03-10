(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Omega.
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarNotations Parsers.BaseTypes.
Require Import Parsers.Grammars.Trivial Parsers.Grammars.ABStar.
Require Import Common Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

(** TODO: Allow stubbing out of individual sub-parse methods *)
Section recursive_descent_parser.
  Context {CharType}
          {String : string_like CharType}
          {G : grammar CharType}.
  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_stateT : String -> Type;
      data' :> _ := {| BaseTypes.predata := predata ; BaseTypes.split_stateT := fun _ _ _ => split_stateT |};
      split_string_for_production
      : forall it its,
          StringWithSplitState String split_stateT
          -> list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT);
      split_string_for_production_correct
      : forall it its (str : StringWithSplitState String split_stateT),
          let P f := List.Forall f (split_string_for_production it its str) in
          P (fun s1s2 =>
               (fst s1s2 ++ snd s1s2 =s str) = true);
      premethods :> parser_computational_dataT'
      := @Build_parser_computational_dataT'
           _ String data'
           (fun _ _ => split_string_for_production)
           (fun _ _ => split_string_for_production_correct) }.
  Context `{data : boolean_parser_dataT}.

  Section bool.
    Section parts.
      Definition parse_item
                 (str_matches_nonterminal : string -> bool)
                 (str : StringWithSplitState String split_stateT)
                 (it : item CharType)
      : bool
        := match it with
             | Terminal ch => [[ ch ]] =s str
             | NonTerminal nt => str_matches_nonterminal nt
           end.

      Section production.
        Context {str0}
                (parse_nonterminal
                 : forall (str : StringWithSplitState String split_stateT),
                     str ≤s str0
                     -> string
                     -> bool).

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Fixpoint parse_production
                 (str : StringWithSplitState String split_stateT)
                 (pf : str ≤s str0)
                 (prod : production CharType)
        : bool.
        Proof.
          refine
            match prod with
              | nil =>
                (** 0-length production, only accept empty *)
                str =s Empty _
              | it::its
                => let parse_production' := fun str pf => parse_production str pf its in
                   fold_right
                     orb
                     false
                     (let mapF f := map f (combine_sig (split_string_for_production_correct it its str)) in
                      mapF (fun s1s2p =>
                              (parse_item
                                 (parse_nonterminal (fst (proj1_sig s1s2p)) _)
                                 (fst (proj1_sig s1s2p))
                                 it)
                                && parse_production' (snd (proj1_sig s1s2p)) _)%bool)
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
        Context {str0}
                (parse_nonterminal
                 : forall (str : StringWithSplitState String split_stateT)
                          (pf : str ≤s str0),
                     string -> bool).

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions
                   (str : StringWithSplitState String split_stateT)
                   (pf : str ≤s str0)
                   (prods : productions CharType)
        : bool
          := fold_right orb
                        false
                        (map (parse_production parse_nonterminal str pf)
                             prods).
      End productions.


      Section nonterminals.
        Section step.
          Context {str0 valid}
                  (parse_nonterminal
                   : forall (p : String * nonterminals_listT),
                       prod_relation (ltof _ Length) nonterminals_listT_R p (str0, valid)
                       -> forall str : StringWithSplitState String split_stateT,
                            str ≤s fst p -> string -> bool).

          Definition parse_nonterminal_step
                     (str : StringWithSplitState String split_stateT)
                     (pf : str ≤s str0)
                     (nt : string)
          : bool.
          Proof.
            refine
              (if lt_dec (Length str) (Length str0)
               then (** [str] got smaller, so we reset the valid nonterminals list *)
                 parse_productions
                   (@parse_nonterminal
                      (str : String, initial_nonterminals_data)
                      (or_introl _))
                   _
                   (or_intror eq_refl)
                   (Lookup G nt)
               else (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                 if Sumbool.sumbool_of_bool (is_valid_nonterminal valid nt)
                 then (** It was valid, so we can remove it *)
                   parse_productions
                     (@parse_nonterminal
                        (str0 : String, remove_nonterminal valid nt)
                        (or_intror (conj eq_refl (remove_nonterminal_dec _ nt _))))
                     str
                     _
                     (Lookup G nt)
                 else (** oops, we already saw this nonterminal in the past.  ABORT! *)
                   false);
            assumption.
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_or_abort
          : forall (p : String * nonterminals_listT)
                   (str : StringWithSplitState String split_stateT),
              str ≤s fst p
              -> string
              -> bool
            := Fix3
                 _ _ _
                 (well_founded_prod_relation
                    (well_founded_ltof _ Length)
                    ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Definition parse_nonterminal
                     (str : StringWithSplitState String split_stateT)
                     (nt : string)
          : bool
            := @parse_nonterminal_or_abort
                 (str : String, initial_nonterminals_data) str
                 (or_intror eq_refl) nt.
        End wf.
      End nonterminals.
    End parts.
  End bool.
End recursive_descent_parser.

Section recursive_descent_parser_list.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Definition rdp_list_nonterminals_listT : Type := list string.
  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> string -> bool
    := fun ls nt => if in_dec string_dec nt ls then true else false.
  Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> string -> rdp_list_nonterminals_listT
    := fun ls nt =>
         filter (fun x => if string_dec nt x then false else true) ls.
  Definition rdp_list_nonterminals_listT_R : rdp_list_nonterminals_listT -> rdp_list_nonterminals_listT -> Prop
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
  Lemma rdp_list_remove_nonterminal_dec : forall ls prods,
                                            @rdp_list_is_valid_nonterminal ls prods = true
                                            -> @rdp_list_nonterminals_listT_R (@rdp_list_remove_nonterminal ls prods) ls.
  Proof.
    intros.
    unfold rdp_list_is_valid_nonterminal, rdp_list_nonterminals_listT_R, rdp_list_remove_nonterminal, ltof in *.
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
  Lemma rdp_list_ntl_wf : well_founded rdp_list_nonterminals_listT_R.
  Proof.
    unfold rdp_list_nonterminals_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.

  Lemma rdp_list_remove_nonterminal_1
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = true
      -> rdp_list_is_valid_nonterminal ls ps' = true.
  Proof.
    unfold rdp_list_is_valid_nonterminal, rdp_list_remove_nonterminal.
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

  Lemma rdp_list_remove_nonterminal_2
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = false
      <-> rdp_list_is_valid_nonterminal ls ps' = false \/ ps = ps'.
  Proof.
    unfold rdp_list_is_valid_nonterminal, rdp_list_remove_nonterminal.
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

  Global Instance rdp_list_predata : parser_computational_predataT
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := Valid_nonterminals G;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_listT_R := rdp_list_nonterminals_listT_R;
         remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         ntl_wf := rdp_list_ntl_wf }.

  Global Instance rdp_list_data' : @parser_computational_types_dataT _ String
    := { predata := rdp_list_predata;
         split_stateT := fun _ _ _ _ => True }.
End recursive_descent_parser_list.

Definition String_with_no_state {CharType} (String : string_like CharType) := StringWithSplitState String (fun _ => True).

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

  Context (G : grammar Ascii.ascii).

  Global Instance brute_force_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ G)
    := { split_string_for_production str0 valid it its := make_all_single_splits;
         split_string_for_production_correct str0 valid it its := make_all_single_splits_correct_seq }.

  Global Instance brute_force_data : @boolean_parser_dataT _ string_stringlike
    := { predata := @rdp_list_predata _ G;
         split_stateT str := True;
         split_string_for_production it its := make_all_single_splits;
         split_string_for_production_correct it its := make_all_single_splits_correct_seq }.

  Definition brute_force_parse_nonterminal
  : @String Ascii.ascii string_stringlike
    -> string
    -> bool
    := parse_nonterminal (G := G).

  Definition brute_force_parse
  : string -> bool
    := fun str => brute_force_parse_nonterminal str G.
End example_parse_string_grammar.

Module example_parse_empty_grammar.
  Definition parse : string -> bool
    := brute_force_parse (trivial_grammar _).

  Time Compute parse "".
  Check eq_refl : true = parse "".
  Time Compute parse "a".
  Check eq_refl : false = parse "a".
  Time Compute parse "aa".
  Check eq_refl : false = parse "aa".
End example_parse_empty_grammar.

Section examples.
  Section ab_star.
    Local Open Scope string_scope.

    Definition parse : string -> bool
      := brute_force_parse ab_star_grammar.

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
    pose proof (eq_refl (parse "")) as s.
    unfold parse in s.
    unfold brute_force_parse, brute_force_parse_nonterminal in s.
    cbv beta zeta delta [parse_nonterminal] in s.
    cbv beta zeta delta [parse_nonterminal_or_abort] in s.
    rewrite Fix3_eq in s.
    Ltac do_compute_in c H :=
      let c' := fresh in
      set (c' := c) in H;
        compute in c';
        subst c'.
    Tactic Notation "do_compute" open_constr(c) "in" ident(H) :=
      match type of H with
        | appcontext[?c0] => unify c c0
      end;
      do_compute_in c H.
    cbv beta zeta delta [parse_nonterminal_step] in s.
    change (fst (?a, ?b)) with a in s.
    change (snd (?a, ?b)) with b in s.
    unfold split_stateT, brute_force_data, default_string_with_no_state, default_String_with_no_state in s.
    repeat change (string_val {| string_val := ?x |}) with x in s.
    do_compute_in (Start_symbol ab_star_grammar) s.
    do_compute_in (@Length Ascii.ascii string_stringlike "ab_star") s.
    do_compute (lt_dec _ _) in s.
    cbv beta iota zeta in s.
    unfold is_valid_nonterminal, initial_nonterminals_data in s.
    do_compute (is_valid_nonterminal initial_nonterminals_data "") in s.
    set (n := @Length Ascii.ascii string_stringlike ab_star_grammar) in s.
    pose ((Length ab_star_grammar)).
    do_compute_in (Length ab_star_grammar) s.
    do_compute_in (lt_dec (Length ab_star_grammar) (Length string_stringlike "abab"%string)) s.
    change (if in_right then ?x else ?y) with y in s.
    cbv beta zeta delta [rdp_list_is_valid_nonterminal] in s.*)
  End ab_star.
End examples.
