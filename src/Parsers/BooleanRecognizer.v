(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common Common.ilist.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section wf.
  Section wf_prod.
    Context A B (RA : relation A) (RB : relation B).

    Definition prod_relation : relation (A * B)
      := fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (fst a'b' = fst ab /\ RB (snd ab) (snd a'b')).

    Fixpoint well_founded_prod_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
    : Acc prod_relation (a, b)
      := match wf_A with
           | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relation (a, b')
                              := Acc_intro
                                   _
                                   (fun ab =>
                                      match ab as ab return prod_relation ab (a, b') -> Acc prod_relation ab with
                                        | (a'', b'') =>
                                          fun pf =>
                                            match pf with
                                              | or_introl pf'
                                                => @well_founded_prod_relation_helper
                                                     _ _
                                                     (fa _ pf')
                                                     wf_B
                                              | or_intror (conj pfa pfb)
                                                => match wf_B' with
                                                     | Acc_intro fb
                                                       => eq_rect
                                                            _
                                                            (fun a'' => Acc prod_relation (a'', b''))
                                                            (wf_B_rec _ (fb _ pfb))
                                                            _
                                                            pfa
                                                   end
                                            end
                                      end)
                             ) b (wf_B b)
         end.

    Definition well_founded_prod_relation : well_founded RA -> well_founded RB -> well_founded prod_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relation_helper; auto.
    Defined.
  End wf_prod.
End wf.

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (productions_listT : Type)
          (initial_productions_data : productions_listT)
          (is_valid_productions : productions_listT -> productions CharType -> bool)
          (remove_productions : productions_listT -> productions CharType -> productions_listT)
          (productions_listT_R : productions_listT -> productions_listT -> Prop)
          (remove_productions_dec : forall ls prods, is_valid_productions ls prods = true
                                                     -> productions_listT_R (remove_productions ls prods) ls)
          (ntl_wf : well_founded productions_listT_R).
  Section bool.
    Context (split_string_for_production
             : forall (str0 : String)
                      (prod : production CharType),
                 list (list { str : String | Length _ str < Length _ str0 \/ str = str0 })).

    Section parts.
      Section item.
        Context (str : String)
                (str_matches_productions : productions CharType -> bool).

        Definition parse_item (it : item CharType) : bool
          := match it with
               | Terminal ch => [[ ch ]] =s str
               | NonTerminal name => str_matches_productions (Lookup G name)
             end.
      End item.

      Section production.
        Variable str0 : String.
        Variable parse_productions : forall (str : String),
                                       Length _ str < Length _ str0 \/ str = str0
                                       -> productions CharType
                                       -> bool.

        (** To match a [production], we must match all of its items.  If the lengths do match up, we don't define the outcome. *)
        Definition parse_production_from_split_list
                   (strs : list { str : String | Length _ str < Length _ str0 \/ str = str0 })
                   (prod : production CharType)
        : bool
          := fold_left andb
                       (map (fun sp => parse_item (proj1_sig (fst sp))
                                                  (parse_productions (proj2_sig (fst sp)))
                                                  (snd sp))
                            (combine strs prod))
                       true.

        (** To match a [production], any split of the string can match. *)
        Definition parse_production_from_any_split_list
                   (strs : list (list { str : String | Length _ str < Length _ str0 \/ str = str0 }))
                   (prod : production CharType)
        : bool
          := fold_left orb
                       (map (fun strs => parse_production_from_split_list strs prod)
                            strs)
                       false.

        Definition or_transitivity {A B} `{@Transitive B R} {f : A -> B} {a0 a}
                   (pf : R (f a) (f a0) \/ a = a0) a' (pf' : R (f a') (f a) \/ a' = a)
        : R (f a') (f a0) \/ a' = a0.
        Proof.
          destruct_head or; subst;
          first [ right; reflexivity | left; assumption | left; etransitivity; eassumption ].
        Defined.

        (** We assume the splits we are given are valid (are actually splits of the string, rather than an unrelated split) and are the same length as the given [production].  Behavior in other cases is undefined *)
        (** We match a production if any split of the string matches that production *)
        Definition parse_production
                   (str : String) (pf : Length _ str < Length _ str0 \/ str = str0)
                   (prod : production CharType)
        : bool
          := if (gt_dec (Datatypes.length prod) 0)
             then (@parse_production_from_any_split_list
                     (map (map (fun sp => exist _ (proj1_sig sp) (or_transitivity pf (proj2_sig sp))))
                          (@split_string_for_production str prod))
                     prod)
             else (** 0-length production, only accept empty *)
               (str =s Empty _).
      End production.

      Section productions.
        Section step.
          Variable str0 : String.
          Variable parse_productions : forall (str : String)
                                              (pf : Length _ str < Length _ str0 \/ str = str0),
                                         productions CharType -> bool.

          (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
          Definition parse_productions_step (str : String) (pf : Length _ str < Length _ str0 \/ str = str0) (prods : productions CharType)
          : bool
            := fold_left orb
                         (map (parse_production parse_productions pf)
                              prods)
                         false.
        End step.

        Section wf.
          Definition parse_productions_or_abort (str0 str : String)
                     (valid_list : productions_listT)
                     (pf : Length _ str < Length _ str0 \/ str = str0)
                     (prods : productions CharType)
          : bool.
          Proof.
            revert str pf prods.
            change str0 with (fst (pair str0 valid_list)).
            generalize (pair str0 valid_list); clear str0 valid_list.
            refine (@Fix (prod String productions_listT)
                         _ (@well_founded_prod_relation
                              String
                              productions_listT
                              _
                              _
                              (well_founded_ltof _ (Length String))
                              ntl_wf)
                         _ _).
            intros [str0 valid_list] parse_productions str pf prods; simpl in *.
            destruct (lt_dec (Length _ str) (Length _ str0)) as [pf'|pf'].
            { (** [str] got smaller, so we reset the valid productions list *)
              specialize (parse_productions
                            (pair str initial_productions_data)
                            (or_introl pf')); simpl in *.
              exact (parse_productions_step parse_productions (or_intror eq_refl) prods). }
            { (** [str] didn't get smaller, so we cache the fact that we've hit this productions already *)
              case_eq (is_valid_productions valid_list prods).
              { (** It was valid, so we can remove it *)
                intro H'.
                specialize (fun pf' => parse_productions
                              (pair str0 (remove_productions valid_list prods))
                              (or_intror (conj eq_refl pf'))); simpl in *.
                specialize (parse_productions (remove_productions_dec H')).
                exact (parse_productions_step parse_productions (or_intror eq_refl) prods). }
              { (** oops, we already saw this productions in the past.  ABORT! *)
                intro; exact false. } }
          Defined.

          Definition parse_productions (str : String) (prods : productions CharType)
          : bool
            := @parse_productions_or_abort str str initial_productions_data
                                           (or_intror eq_refl) prods.
        End wf.
      End productions.
    End parts.
  End bool.
End recursive_descent_parser.

Section recursive_descent_parser_list.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Variable (CharType_eq_dec : forall x y : CharType, {x = y} + {x <> y}).
  Definition rdp_list_productions_listT : Type := list (productions CharType).
  Definition rdp_list_is_valid_productions : rdp_list_productions_listT -> productions CharType -> bool
    := fun ls nt => if in_dec (productions_dec CharType_eq_dec) nt ls then true else false.
  Definition rdp_list_remove_productions : rdp_list_productions_listT -> productions CharType -> rdp_list_productions_listT
    := fun ls nt =>
         filter (fun x => if productions_dec CharType_eq_dec nt x then false else true) ls.
  Definition rdp_list_productions_listT_R : rdp_list_productions_listT -> rdp_list_productions_listT -> Prop
    := ltof _ (@List.length _).
  Lemma filter_list_dec {T} f (ls : list T) : List.length (filter f ls) <= List.length ls.
  Proof.
    induction ls; trivial; simpl in *.
    repeat match goal with
             | [ |- context[if ?a then _ else _] ] => destruct a; simpl in *
             | [ |- S _ <= S _ ] => solve [ apply Le.le_n_S; auto ]
             | [ |- _ <= S _ ] => solve [ apply le_S; auto ]
           end.
  Defined.
  Lemma rdp_list_remove_productions_dec : forall ls prods,
                                            @rdp_list_is_valid_productions ls prods = true
                                            -> @rdp_list_productions_listT_R (@rdp_list_remove_productions ls prods) ls.
  Proof.
    intros.
    unfold rdp_list_is_valid_productions, rdp_list_productions_listT_R, rdp_list_remove_productions, ltof in *.
    destruct (in_dec (productions_dec CharType_eq_dec) prods ls); [ | discriminate ].
    match goal with
      | [ H : In ?prods ?ls |- context[filter ?f ?ls] ]
        => assert (~In prods (filter f ls))
    end.
    { intro H'.
      apply filter_In in H'.
      destruct H' as [? H'].
      destruct (productions_dec CharType_eq_dec prods prods); congruence. }
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
  Defined.
  Lemma rdp_list_ntl_wf : well_founded rdp_list_productions_listT_R.
  Proof.
    unfold rdp_list_productions_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.
End recursive_descent_parser_list.

Section example_parse_string_grammar.
  Fixpoint make_all_single_splits (str : string) : list { strs : string * string | (fst strs ++ snd strs = str)%string }.
  Proof.
    refine ((exist _ (""%string, str) eq_refl)::_).
    refine (match str with
              | ""%string => nil
              | String.String ch str' => map (fun p => exist _ (String.String ch (fst (proj1_sig p)),
                                                                snd (proj1_sig p))
                                                             _)
                                             (make_all_single_splits str')
            end).
    simpl; apply f_equal.
    apply proj2_sig.
  Defined.

  Lemma length_append (s1 s2 : string) : length (s1 ++ s2) = length s1 + length s2.
  Proof.
    revert s2.
    induction s1; simpl; trivial; [].
    intros.
    f_equal; auto.
  Qed.

  Fixpoint flatten1 {T} (ls : list (list T)) : list T
    := match ls with
         | nil => nil
         | x::xs => (x ++ flatten1 xs)%list
       end.

  Lemma flatten1_length_ne_0 {T} (ls : list (list T)) (H0 : Datatypes.length ls <> 0)
        (H1 : Datatypes.length (hd nil ls) <> 0)
  : Datatypes.length (flatten1 ls) <> 0.
  Proof.
    destruct ls as [| [|] ]; simpl in *; auto.
  Qed.

  Local Ltac t' :=
    match goal with
      | _ => progress simpl in *
      | _ => progress subst
      | [ H : ?a = ?b |- _ ] => progress subst a
      | [ H : ?a = ?b |- _ ] => progress subst b
      | _ => rewrite (LeftId string_stringlike _)
      | _ => rewrite (RightId string_stringlike _)
      | _ => reflexivity
      | _ => split
      | _ => right; reflexivity
      | _ => rewrite map_length
      | _ => rewrite map_map
      | _ => rewrite length_append
      | _ => progress destruct_head_hnf prod
      | _ => progress destruct_head_hnf and
      | _ => progress destruct_head_hnf or
      | _ => progress destruct_head_hnf sig
      | _ => progress auto with arith
      | _ => apply f_equal
      | _ => solve [ apply proj2_sig ]
      | _ => solve [ left; auto with arith ]
      | [ str : string |- _ ] => solve [ destruct str; simpl; auto with arith ]
      | [ str : string |- _ ] => solve [ left; destruct str; simpl; auto with arith ]
    end.
  Local Ltac t'' :=
    match goal with
      | _ => progress t'
      | [ str : string |- _ ] => solve [ destruct str; repeat t' ]
    end.
  Local Ltac t :=
    solve [ repeat t'' ].

  Local Hint Resolve NPeano.Nat.lt_lt_add_l NPeano.Nat.lt_lt_add_r NPeano.Nat.lt_add_pos_r NPeano.Nat.lt_add_pos_l : arith.

  Definition brute_force_splitter
  : forall (str : string_stringlike) (pat : production Ascii.ascii),
      list
        (list
           { str_part : string_stringlike |
             Length string_stringlike str_part < Length string_stringlike str \/
             str_part = str }).
  Proof.
    simpl.
    intros str [|pat pats];
      [ exact nil (** no patterns, no split (actually, we should never encounter this case *)
      | ].
    revert str.
    induction pats; simpl in *; intros str.
    { (** We only get one thing in the list *)
      refine (((exist _ str _)::nil)::nil).
      simpl; auto with arith. }
    { pose (make_all_single_splits str) as single_splits.
      pose proof (map (@proj1_sig _ _) single_splits).
      refine (flatten1
                (map (fun s1s2p =>
                        map
                          (fun split_list => ((exist _ (fst (proj1_sig s1s2p)) _)
                                                ::(map (fun s => exist _ (proj1_sig s) _)
                                                       split_list)))
                          (IHpats (snd (proj1_sig s1s2p))))
                     single_splits));
        subst_body;
        clear;
        abstract t. }
  Defined.

  Variable G : grammar Ascii.ascii.
  Variable all_productions : list (productions Ascii.ascii).

  Definition brute_force_make_parse_of : @String Ascii.ascii string_stringlike
                                         -> productions Ascii.ascii
                                         -> bool.
  Proof.
    eapply (@parse_productions _ _ G)
    with (productions_listT := rdp_list_productions_listT)
           (is_valid_productions := rdp_list_is_valid_productions Ascii.ascii_dec)
           (remove_productions := rdp_list_remove_productions Ascii.ascii_dec)
           (productions_listT_R := rdp_list_productions_listT_R).
    { intros; exact all_productions. }
    { apply rdp_list_remove_productions_dec. }
    { apply rdp_list_ntl_wf. }
    { intros; apply brute_force_splitter; assumption. }
  Defined.
End example_parse_string_grammar.

Module example_parse_empty_grammar.
  Definition make_parse_of : forall (str : string)
                                    (prods : productions Ascii.ascii),
                               bool
    := @brute_force_make_parse_of (trivial_grammar _) (map (Lookup (trivial_grammar _)) (""::nil)%string).



  Definition parse : string -> bool
    := fun str => make_parse_of str (trivial_grammar _).

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

    Definition ab_star_grammar : grammar Ascii.ascii :=
      {| Top_name := "ab_star";
         Lookup := fun s =>
                     if string_dec s ""
                     then nil::nil
                     else if string_dec s "ab"
                          then ("ab"%string : production _)::nil
                          else if string_dec s "ab_star"
                               then ((NonTerminal _ ""%string)::nil)
                                      ::((NonTerminal _ "ab"%string)::(NonTerminal _ "ab_star")::nil)
                                      ::nil
                               else nil::nil |}.

    Definition make_parse_of : forall (str : string)
                                      (prods : productions Ascii.ascii),
                                 bool
      := @brute_force_make_parse_of ab_star_grammar (map (Lookup ab_star_grammar) (""::"ab"::"ab_star"::nil)%string).



    Definition parse : string -> bool
      := fun str => make_parse_of str ab_star_grammar.

    Time Compute parse "".
    Check eq_refl : parse "" = true.
    Time Compute parse "a".
    Check eq_refl : parse "a" = false.
    Time Compute parse "ab".
    Check eq_refl : parse "ab" = true.
    Time Compute parse "aa".
    Check eq_refl : parse "aa" = false.
    Time Compute parse "ba".
    Check eq_refl : parse "ba" = false.
    Time Compute parse "aba".
    Check eq_refl : parse "aba" = false.
    Time Compute parse "abab".
    Check eq_refl : parse "abab" = true.
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
    cbv beta zeta delta [rdp_list_is_valid_productions] in s.
                       *)
  End ab_star.
End examples.
