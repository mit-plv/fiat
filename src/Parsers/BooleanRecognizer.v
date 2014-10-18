(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Omega.
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String Coq.Structures.Equalities.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.ListLike Parsers.ListListLike Parsers.StringStringLike.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.

Module RecursiveDescentBooleanParserHelper (S : StringLike).
  Import S.
  Module Export CFG := ContextFreeGrammar S.
  Module Productions <: Typ.
    Definition t := productions.
  End Productions.

  Module RecursiveDescentBooleanParser (Listish : ListLike Productions).
    Export Listish.
    Local Open Scope list_like_scope.
    Local Open Scope string_like_scope.
    Local Notation String := S.t.
    Local Notation productions_listT := Listish.t.
    Local Notation remove_productions_dec := Listish.lt_1.
    Section recursive_descent_parser.
      Context (G : grammar).
      Context (initial_productions_data : productions_listT).

      Section bool.
        Context (split_string_for_production
                 : forall (str0 : String) (prod : production), list (String * String))
                (split_string_for_production_correct
                 : forall str0 prod,
                     List.Forall (fun s1s2 => (fst s1s2 ++ snd s1s2 =s str0) = true)
                                 (split_string_for_production str0 prod)).

        Section parts.
          Section item.
            (** We require that the list of productions be non-empty; we
            do this by passing the first element separately, rather
            than invoking dependent types and proofs. *)
            Context (str : String)
                    (str_matches_productions : production -> productions -> bool).

            Definition parse_item (it : item) : bool
              := match it with
                   | Terminal ch => [[ ch ]] =s str
                   | NonTerminal name => match Lookup G name with
                                           | nil => (** No string can match an empty nonterminal *) false
                                           | p::ps => str_matches_productions p ps
                                         end
                 end.
          End item.

          Section production.
            Variable str0 : String.
            Variable parse_productions : forall (str : String),
                                           str ≤s str0
                                           -> production
                                           -> productions
                                           -> bool.

            (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
            Fixpoint parse_production
                     (str : String) (pf : str ≤s str0)
                     (prod : production)
            : bool.
            Proof.
              refine match prod with
                       | nil =>
                         (** 0-length production, only accept empty *)
                         str =s Empty
                       | it::its
                         => let parse_production' := fun str pf => @parse_production str pf its in
                            fold_right
                              orb
                              false
                              (map (fun s1s2p => (parse_item (fst (proj1_sig s1s2p))
                                                             (@parse_productions (fst (proj1_sig s1s2p))
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
              Variable parse_productions : forall (str : String)
                                                  (pf : str ≤s str0),
                                             production -> productions -> bool.

              (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
              Definition parse_productions_step (str : String) (pf : str ≤s str0) (prods : productions)
              : bool
                := fold_right orb
                              false
                              (map (parse_production parse_productions pf)
                                   prods).
            End step.

            Section wf.
              (** TODO: add comment explaining signature *)
              Definition parse_productions_or_abort_helper
              : forall (p : String * productions_listT) (str : String),
                  str ≤s fst p
                  -> production
                  -> productions
                  -> bool.
              Proof.
                refine (@Fix4
                          (prod String productions_listT) _ _ _ _
                          _ (@well_founded_prod_relation
                               String
                               productions_listT
                               _
                               _
                               (well_founded_ltof _ Length)
                               Listish.lt_wf)
                          _ _).
                refine (fun sl parse_productions str pf (prod : production) (prods : productions)
                        => let str0 := fst sl in
                           let valid_list := snd sl in
                           match lt_dec (Length str) (Length str0) with
                             | left pf' =>
                               (** [str] got smaller, so we reset the valid productions list *)
                               parse_productions_step
                                 (parse_productions
                                    (str, initial_productions_data)
                                    (or_introl pf'))
                                 (reflexivity _)
                                 (prod::prods)
                             | right pf' =>
                               (** [str] didn't get smaller, so we cache the fact that we've hit this productions already *)
                               (if (prod::prods) ∈ valid_list as is_valid
                                   return (prod::prods) ∈ valid_list = is_valid -> _
                                then (** It was valid, so we can remove it *)
                                  fun H' =>
                                    parse_productions_step
                                      (parse_productions
                                         (str0, remove (prod::prods) valid_list)
                                         (or_intror (conj eq_refl (remove_productions_dec H'))))
                                      (reflexivity _)
                                      (prod::prods)
                                else (** oops, we already saw this productions in the past.  ABORT! *)
                                  fun _ => false
                               ) eq_refl
                           end).
              Defined.

              Definition parse_productions_or_abort (str0 str : String)
                         (valid_list : productions_listT)
                         (pf : str ≤s str0)
                         (prods : productions)
              : bool
                := match prods with
                     | nil => false
                     | p::ps => parse_productions_or_abort_helper (str0, valid_list) pf p ps
                   end.

              Definition parse_productions (str : String) (prods : productions)
              : bool
                := @parse_productions_or_abort str str initial_productions_data
                                               (reflexivity _) prods.
            End wf.
          End productions.
        End parts.
      End bool.
    End recursive_descent_parser.
  End RecursiveDescentBooleanParser.
End RecursiveDescentBooleanParserHelper.

Module Export RecursiveDescentBooleanParserWithStringListHelper.
  Module Import RecursiveDescentBooleanParserWithStringListHelper' := RecursiveDescentBooleanParserHelper StringStringLike.
  Import CFG.
  Module ProductionsDec <: EqDecType.
    Include Productions.
    Definition eqb (x y : t) : bool
      := if productions_dec Ascii.ascii_dec x y then true else false.
    Lemma eqb_1 : forall x, eqb x x = true.
    Proof. unfold eqb; intros; edestruct productions_dec; congruence. Qed.
    Lemma eqb_2 : forall x y, eqb x y = true -> x = y.
    Proof. unfold eqb; intros; edestruct productions_dec; congruence. Qed.
  End ProductionsDec.
  Module L := ListListLike ProductionsDec.
  Local Open Scope list_like_scope.
  Local Open Scope string_like_scope.
  Import StringStringLike.
  Local Notation String := StringStringLike.t.
  Local Notation productions_listT := L.t.
  Local Notation remove_productions_dec := L.lt_1.
  Module Import RecursiveDescentBooleanParserWithStringList := RecursiveDescentBooleanParser L.
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
    : List.Forall (fun strs : String * String
                   => (fst strs ++ snd strs =s str))%string_like (make_all_single_splits str).
    Proof.
      induction str; unfold is_true in *; simpl; constructor; simpl; auto.
      { unfold "=s"; rewrite string_dec_refl; reflexivity. }
      { apply Forall_map.
        unfold compose; simpl.
        revert IHstr; apply Forall_impl; intros.
        match goal with H : (_ =s _) = true |- _ => apply bool_eq_correct in H end.
        subst; unfold "=s"; rewrite string_dec_refl; reflexivity. }
    Qed.

    Lemma make_all_single_splits_correct_str_le (str : String)
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

    Variable G : grammar.

    Definition brute_force_make_parse_of : String
                                           -> productions
                                           -> bool
      := @parse_productions
           G
           (Valid_nonterminals G)
           (fun (str : String) _ => make_all_single_splits str)
           (fun str0 _ => make_all_single_splits_correct_seq str0).
  End example_parse_string_grammar.

  Module example_parse_empty_grammar.
    Definition make_parse_of : forall (str : string)
                                      (prods : productions),
                                 bool
      := @brute_force_make_parse_of trivial_grammar.



    Definition parse : string -> bool
      := fun str => make_parse_of str trivial_grammar.

    Time Compute parse "".
    Check eq_refl : true = parse "".
    Time Compute parse "a".
    Check eq_refl : false = parse "a".
    Time Compute parse "aa".
    Check eq_refl : false = parse "aa".
  End example_parse_empty_grammar.

  Section examples.
    Section ab_star.

      Fixpoint production_of_string (s : string) : production
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
      Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions)%productions) (at level 100) : production_assignment_scope.
      Notation "[[[ x ;; .. ;; y ]]]" :=
        (list_to_productions (nil::nil) (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.

      Local Open Scope string_scope.
      Notation "<< x | .. | y >>" :=
        (@cons production (x)%production .. (@cons production (y)%production nil) .. ) : productions_scope.

        Notation "$< x $ .. $ y >$" := (cons (NonTerminal x) .. (cons (NonTerminal y) nil) .. ) : production_scope.

        Definition ab_star_grammar : grammar :=
          {| Start_symbol := "ab_star";
             Lookup := [[[ ("" ::== (<< "" >>)) ;;
                                                ("ab" ::== << "ab" >>) ;;
                                                ("ab_star" ::== << $< "" >$
                                                | $< "ab" $ "ab_star" >$ >> ) ]]]%prods_assignment;
             Valid_nonterminal_symbols := (""::"ab"::"ab_star"::nil)%string |}.

        Definition make_parse_of : forall (str : string)
                                          (prods : productions),
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
End RecursiveDescentBooleanParserWithStringListHelper.
