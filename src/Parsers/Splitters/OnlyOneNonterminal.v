(** * Splitter for any part of any grammar with at most one nonterminal in a rule *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Common.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import ADTSynthesis.Common.Wf.

Require Import ADTSynthesis.Parsers.Splitters.Reflective.

Require Import ADTSynthesis.Parsers.MinimalParse.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarNotations.
Require Import ADTSynthesis.Parsers.Grammars.ABStar.

Set Implicit Arguments.
Local Open Scope type_scope.
Local Open Scope string_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.
Section StringT.
  Context {CharType} {String : string_like CharType} (split_stateT : String -> Type).

  Let String' : Type := String.
  Let StringT := (StringWithSplitState String split_stateT).
About eq_rect.
About RightId.
  Context (empty_state : split_stateT (Empty _))
          (split_state_at : forall n s,
                              split_stateT s
                              -> split_stateT (fst (SplitAt n s)) * split_stateT (snd (SplitAt n s)))
          (split_state_at_right_id
           : forall s st,
               split_state_at (Length s) (s ++ Empty _) st
               = (eq_rect
                    _ split_stateT
                    (eq_rect
                       _ split_stateT
                       st _
                       (RightId _ _))
                    _
                    (f_equal fst (eq_sym (SplitAt_concat_correct _ _ _))),
                  eq_rect
                    _ split_stateT
                    empty_state _
                    (f_equal snd (eq_sym (SplitAt_concat_correct _ _ _))))).

  Let SplitAtT (n : nat) (s : StringT) : StringT * StringT
    := ({| string_val := fst (SplitAt n s) ; state_val := fst (split_state_at n (state_val s)) |},
        {| string_val := snd (SplitAt n s) ; state_val := snd (split_state_at n (state_val s)) |}).

  Local Ltac destruct_matched_equality e :=
    subst;
    let T := type of e in
    match eval simpl in T with
      | ?a = ?b
        => generalize e; simpl;
           first [ generalize dependent b; intros; progress subst
                 | generalize dependent a; generalize dependent b; intros; progress subst
                 | generalize b; intros; progress subst
                 | generalize a; generalize dependent b; intros; progress subst
                 | generalize dependent a; generalize b; intros; progress subst
                 | generalize a; generalize b; intros; progress subst ]
    end.

  Local Ltac t_equality :=
    repeat match goal with
             | _ => intro
             | _ => reflexivity
             | [ H : is_true false |- _ ] => hnf in H; clear -H; exfalso; abstract discriminate
             | [ H : false = true |- _ ] => hnf in H; clear -H; exfalso; abstract discriminate
             | _ => progress simpl in *
             | _ => progress subst
             | _ => progress destruct_head sigT
             | _ => progress destruct_head prod
             | _ => progress destruct_head and
             | _ => progress destruct_head @StringWithSplitState
             | [ |- _ = _ :> (_ * _)%type ] => apply f_equal2
             (*| [ |- _ = _ :> StringT ] => apply StringT_eq*)
             | [ |- _ \/ False ] => left
             | _ => rewrite RightId
             | _ => rewrite LeftId
             | [ H : context[string_dec ?str ?x] |- _ ] => atomic x; destruct (string_dec str x)
             | [ |- context[match ?s with _ => _ end] ] => atomic s; destruct s
             | [ H : context[match ?s with _ => _ end] |- _ ] => atomic s; destruct s
             | _ => rewrite substring_correct3'
             | [ |- context[SplitAt ?n (?s1 ++ ?s2)] ]
               => replace n with (Length s1) by (rewrite Singleton_Length; trivial);
                 rewrite SplitAt_concat_correct
             | [ H : (_ || _ = true)%bool |- _ ] => apply Bool.orb_true_iff in H
             | [ H : (_ || _ = false)%bool |- _ ] => apply Bool.orb_false_iff in H
             | [ H : (_ && _ = true)%bool |- _ ] => apply Bool.andb_true_iff in H
             | [ H : (_ && _ = false)%bool |- _ ] => apply Bool.andb_false_iff in H
             | _ => rewrite Bool.orb_true_r
             | [ H : _ |- _ ] => rewrite Bool.orb_true_r in H
             | [ H : _ |- _ ] => rewrite H
             | _ => progress destruct_head or
             | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ nil |- _ ] => inversion H; clear H
             | _ => rewrite Singleton_Length
             | _ => progress unfold eq_rect
             | [ |- context[match ?e with eq_refl => _ end] ] => destruct_matched_equality e
             | _ => solve [ eauto ]
           end.

  Section first_char_splitter.
    Context (fallback_split
             : forall (it : item CharType)
                      (its : production CharType)
                      (str : StringT),
                 list (StringT * StringT)).

    Fixpoint has_only_terminals (its : production CharType)
    : bool
      := match its with
           | nil => true
           | (Terminal _)::xs => has_only_terminals xs
           | (NonTerminal _)::_ => false
         end.

    Definition first_char_split
               (it : item CharType)
               (its : production CharType)
               (str : StringT)
    : list (StringT * StringT)
      := match it, its with
           | _, nil
             => [(str, {| string_val := Empty _ ; state_val := empty_state |})]
           | Terminal _, _::_
             => [SplitAtT 1 str]
           | NonTerminal _, _
             => if has_only_terminals its
                then [SplitAtT (Length str - List.length its) str]
                else fallback_split it its str
         end.

    Lemma first_char_split_correct_seq {it its} {str : StringT}
          (f := fun strs : StringT * StringT => fst strs ++ snd strs =s str)
          (fallback_split_correct_eq : List.Forall f (fallback_split it its str))
    : List.Forall f (first_char_split it its str).
    Proof.
      unfold first_char_split; subst f.
      repeat match goal with
               | _ => reflexivity
               | _ => assumption
               | _ => progress simpl in *
               | [ |- context[match ?l with _ => _ end] ]
                 => atomic l; destruct l
               | [ |- is_true (_ =s _)%string_like ] => apply bool_eq_correct
               | _ => progress rewrite ?LeftId, ?RightId
               | _ => apply SplitAt_correct
               | [ |- List.Forall _ [] ] => constructor
               | [ |- List.Forall _ (_::_) ] => constructor
               | [ |- context[match ?l with _ => _ end] ]
                 => destruct l
             end.
    Qed.

    Context (G : grammar CharType).
    Context (fallback_split_correct_eq
             : forall it its (str : StringT),
                 List.Forall
                   (fun strs : StringT * StringT => fst strs ++ snd strs =s str)
                   (fallback_split it its str)).

    Let data' : @parser_computational_types_dataT _ String
      := {| BaseTypes.predata := @rdp_list_predata _ G;
            BaseTypes.split_stateT str0 valid g := split_stateT |}.

    Global Instance first_char_premethods : @parser_computational_dataT' _ _ data'
      := { split_string_for_production str0 valid := first_char_split;
           split_string_for_production_correct str0 valid it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

    Global Instance first_char_data : @boolean_parser_dataT _ _
      := { predata := @rdp_list_predata _ G;
           split_stateT := split_stateT;
           split_string_for_production := first_char_split;
           split_string_for_production_correct it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

    Context (fallback_valid_prod : production CharType -> bool).

    Fixpoint first_char_valid_prod
             (first_char_valid : string -> bool)
             (p : production CharType)
    : bool
      := match p with
           | nil => true
           | (Terminal _)::p' => first_char_valid_prod first_char_valid p'
           | (NonTerminal nt)::p' => ((first_char_valid_prod first_char_valid p')
                                        && first_char_valid nt
                                        && (has_only_terminals p' || fallback_valid_prod p))%bool
         end.

    Definition first_char_valid : bool
      := split_valid (G := G) first_char_valid_prod.

    Lemma first_char_valid_prod_cons {fcv x xs}
    : first_char_valid_prod fcv (x::xs)
      = match x with
          | Terminal _ => first_char_valid_prod fcv xs
          | NonTerminal nt => ((first_char_valid_prod fcv xs)
                                 && fcv nt
                                 && (has_only_terminals xs || fallback_valid_prod (x::xs)))%bool
        end.
    Proof.
      reflexivity.
    Qed.

    Lemma valid_if_has_only_terminals {fcv p}
          (H : has_only_terminals p = true)
    : first_char_valid_prod fcv p = true.
    Proof.
      induction p; t_equality.
    Qed.

    Lemma has_only_terminals_min_parse_length
          {str0 valid strs its}
          (H : has_only_terminals its = true)
          (p : minimal_parse_of_production String G initial_nonterminal_data

 has_only_terminals its = true
  strs : String
  X2 : minimal_parse_of_production String G (Valid_nonterminals G)
         rdp_list_is_valid_nonterminal rdp_list_remove_nonterminal str0 valid
         strs its
  H8 : [[c]] ++ strs ≤s str0
  pf : s1 ++ [[c]] ++ strs ≤s str0
  st : split_stateT (s1 ++ [[c]] ++ strs)
  ============================
   SplitAtT (Length (s1 ++ [[c]] ++ strs) - S (Datatypes.length its))

    Context (fallback_split_ind : forall x xs, fallback_valid_prod (x::xs) -> fallback_valid_prod xs).

    Lemma first_char_split_complete
          (H : first_char_valid = true)
    : forall str0 valid str pf nt,
        is_valid_nonterminal initial_nonterminals_data nt ->
        ForallT
          (Forall_tails
             (fun prod =>
                match prod with
                  | [] => True
                  | it :: its =>
                    @split_list_completeT _ String G first_char_data str0 valid str pf
                                          (@first_char_split it its str) it its
                end)) (Lookup G nt).
    Proof.
      apply (split_complete_simple first_char_valid_prod).
      { intros ? ? ? p.
        induction p; t_equality. }
      { intros f x xs; revert x.
        induction xs; t_equality. }
      { intros.
        cut ({st1st2 : _ |
              In
                ({| string_val := fst (SplitAt (Length s1) (s1 ++ s2)); state_val := fst st1st2 |},
                 {| string_val := snd (SplitAt (Length s1) (s1 ++ s2)); state_val := snd st1st2 |})
                (first_char_split it its {| string_val := s1 ++ s2; state_val := st |})}).
        { rewrite SplitAt_concat_correct; simpl; trivial. }
        { exists (split_state_at (Length s1) st).
          unfold first_char_split.
          t_equality.

          Focus 2.
          revert st.

          rewrite <- Associativity.
          {
unfold SplitAtT; simpl.
unfold eq_rect.
            match goal with
              | [ |- context[match ?e with eq_refl => _ end] ]
                => subst;
                  match type of e with
                    | ?a = ?b
                      => generalize e;
                        first [ generalize dependent b; generalize dependent a; intros; progress subst
                              | generalize dependent a; generalize dependent b; intros; progress subst ]
                  end
            end.
            reflexivity. }
          { unfold eq_rect; simpl.
            do 3 match goal with
                   | [ |- context[match ?e with eq_refl => _ end] ]
                     => subst;
                       let T := type of e in
                       match eval simpl in T with
                         | ?a = ?b
                           => generalize e;
                             first [ generalize dependent b; generalize dependent a; intros; progress subst
                                   | generalize dependent a; generalize dependent b; intros; progress subst ]
                       end
                   | _ => progress simpl
                 end.
            reflexivity. }
          { unfold eq_rect; simpl.
            match goal with
                   | [ |- context[match ?e with eq_refl => _ end] ]
                     => subst;
                       let T := type of e in
                       match eval simpl in T with
                         | ?a = ?b
                           => generalize e; simpl;
                             first [ generalize dependent b; intros; progress subst
                                   | generalize dependent a; generalize dependent b; intros; progress subst
                                   | generalize b; intros; progress subst
                                   | generalize a; generalize dependent b; intros; progress subst
                                   | generalize dependent a; generalize b; intros; progress subst
                                   | generalize a; generalize b; intros; progress subst ]
                       end
                   | _ => progress simpl
                 end.
            reflexivity. }
          {
unfold SplitAtT; simpl.
          generalize
                                                        e

          generalize (RightId String [[ c ]]).
          general

 }
      { exact H. }
    Qed.

    Global Instance first_char_cdata' H : @boolean_parser_completeness_dataT' _ _ G first_char_data
      := { remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
           remove_nonterminal_2 := rdp_list_remove_nonterminal_2;
           split_string_for_production_complete := @first_char_split_complete H }.

    Global Instance first_char_cdata H : @boolean_parser_correctness_dataT _ _ G
      := { data := first_char_data;
           cdata' := first_char_cdata' H }.
  End first_char_splitter.
End StringT.

Section on_ab_star.
  Definition ab_star_linear_split := first_char_split (String := string_stringlike) (fun _ _ _ => nil).
  Definition ab_star_linear_split_correct_seq {it its str} : List.Forall _ _
    := @first_char_split_correct_seq _ string_stringlike (fun _ _ _ => nil) it its str (Forall_nil _).

  Global Instance ab_star_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ ab_star_grammar)
    := first_char_premethods (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _).
  Global Instance ab_star_data : @boolean_parser_dataT _ string_stringlike
    := first_char_data (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _).

  Global Instance ab_star_cdata' : @boolean_parser_completeness_dataT' _ _ ab_star_grammar ab_star_data
    := first_char_cdata' (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _) eq_refl.

  Global Instance ab_star_cdata : @boolean_parser_correctness_dataT _ _ ab_star_grammar
    := first_char_cdata (String := string_stringlike) (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _) eq_refl.
End on_ab_star.

Section on_ab_star'.
  Definition ab_star'_linear_split := first_char_split (String := string_stringlike) (fun _ _ _ => nil).
  Definition ab_star'_linear_split_correct_seq {it its str} : List.Forall _ _
    := @first_char_split_correct_seq _ string_stringlike (fun _ _ _ => nil) it its str (Forall_nil _).

  Global Instance ab_star'_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ ab_star_grammar')
    := first_char_premethods (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _).
  Global Instance ab_star'_data : @boolean_parser_dataT _ string_stringlike
    := first_char_data (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _).

  Global Instance ab_star'_cdata' : @boolean_parser_completeness_dataT' _ _ ab_star_grammar' ab_star'_data
    := first_char_cdata' (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _) eq_refl.

  Global Instance ab_star'_cdata : @boolean_parser_correctness_dataT _ _ ab_star_grammar'
    := first_char_cdata (String := string_stringlike) (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _) eq_refl.
End on_ab_star'.
