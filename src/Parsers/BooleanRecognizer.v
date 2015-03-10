(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Omega.
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarNotations.
Require Import Parsers.BaseTypes Parsers.BooleanBaseTypes.
Require Import Parsers.Grammars.Trivial Parsers.Grammars.ABStar.
Require Import Parsers.Splitters.RDPList Parsers.Splitters.BruteForce.
Require Import Common Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

(** TODO: Allow stubbing out of individual sub-parse methods *)
Section recursive_descent_parser.
  Context {CharType}
          {String : string_like CharType}
          {G : grammar CharType}.
  Context `{data : @boolean_parser_dataT _ String}.

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

(** TODO: move this elsewhere *)
Section example_parse_string_grammar.
  Context (G : grammar Ascii.ascii).

  Definition brute_force_parse_nonterminal
  : @String Ascii.ascii string_stringlike
    -> string
    -> bool
    := let data := @brute_force_data G in parse_nonterminal (G := G).

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
