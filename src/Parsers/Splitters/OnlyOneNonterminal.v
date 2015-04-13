(** * Splitter for any part of any grammar with at most one nonterminal in a rule *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.CorrectnessBaseTypes.
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

Create HintDb equality_t_db discriminated.
Create HintDb equality_t_end_db discriminated.

Section StringT.
  Context {CharType} {String : string_like CharType} (split_stateT : String -> Type).

  Let String' : Type := String.
  Let StringT := (StringWithSplitState String split_stateT).

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

  Hint Rewrite RightId LeftId @substring_correct3' Bool.orb_true_r : equality_t_db.
  Hint Rewrite Singleton_Length : equality_t_end_db.
  Hint Rewrite <- Length_correct : equality_t_end_db.

  Local Ltac t_equality :=
    repeat match goal with
             | _ => intro
             | _ => reflexivity
             | [ H : is_true false |- _ ] => hnf in H; exfalso; clear -H; abstract discriminate
             | [ H : false = true |- _ ] => exfalso; clear -H; abstract discriminate
             | [ H : ?x = true, H' : ?x = false |- _ ]
               => symmetry in H';
                 assert (false = true) by (etransitivity; [ exact H' | exact H ]);
                 clear H H'
             | _ => progress simpl in *
             | _ => progress subst
             | _ => progress destruct_head sigT
             | _ => progress destruct_head prod
             | _ => progress destruct_head and
             | _ => progress destruct_head @StringWithSplitState
             | [ |- _ = _ :> (_ * _)%type ] => apply f_equal2
             | [ |- _ \/ False ] => left
             | _ => progress autorewrite with equality_t_db
             | [ H : context[string_dec ?str ?x] |- _ ] => atomic x; destruct (string_dec str x)
             | [ |- context[match ?s with _ => _ end] ] => atomic s; destruct s
             | [ H : context[match ?s with _ => _ end] |- _ ] => atomic s; destruct s
             | [ |- context[match ?f ?x with true => _ | false => _ end] ] => atomic f; atomic x; case_eq (f x)
             | [ |- context[SplitAt ?n (?s1 ++ ?s2)] ]
               => replace n with (Length s1) by (rewrite Singleton_Length; trivial);
                 rewrite SplitAt_concat_correct
             | [ H : (_ || _ = true)%bool |- _ ] => apply Bool.orb_true_iff in H
             | [ H : (_ || _ = false)%bool |- _ ] => apply Bool.orb_false_iff in H
             | [ H : (_ && _ = true)%bool |- _ ] => apply Bool.andb_true_iff in H
             | [ H : (_ && _ = false)%bool |- _ ] => apply Bool.andb_false_iff in H
             | [ H : _ |- _ ] => rewrite Bool.orb_true_r in H
             | [ H : _ |- _ ] => rewrite H
             | _ => progress destruct_head or
             | [ H : minimal_parse_of_item _ _ _ (Terminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_item _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ (_::_) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ nil |- _ ] => inversion H; clear H
             | _ => progress autorewrite with equality_t_end_db
             | _ => progress unfold eq_rect
             | [ |- In _ (@map nat _ _ _) ]
               => apply in_map_iff; eexists; split; [ reflexivity | ]
             | [ |- context[match ?e with eq_refl => _ end] ] => destruct_matched_equality e
             | _ => solve [ eauto ]
           end.

  Section only_one_nt_splitter.
    Context (fallback_split
             : forall (it : item CharType)
                      (its : production CharType)
                      (str : StringT),
                 list nat).

    Fixpoint has_only_terminals (its : production CharType)
    : bool
      := match its with
           | nil => true
           | (Terminal _)::xs => has_only_terminals xs
           | (NonTerminal _)::_ => false
         end.

    Definition only_one_nt_split
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
                else map (fun n => SplitAtT n str) (fallback_split it its str)
         end.

    Lemma only_one_nt_split_correct_seq {it its} {str : StringT}
          (f := fun strs : StringT * StringT => fst strs ++ snd strs =s str)
    : List.Forall f (only_one_nt_split it its str).
    Proof.
      unfold only_one_nt_split; subst f.
      repeat match goal with
               | _ => reflexivity
               | _ => assumption
               | _ => intro
               | _ => progress simpl in *
               | [ |- context[match ?l with _ => _ end] ]
                 => atomic l; destruct l
               | [ |- is_true (_ =s _)%string_like ] => apply bool_eq_correct
               | _ => progress rewrite ?LeftId, ?RightId
               | _ => apply SplitAt_correct
               | [ |- List.Forall _ [] ] => constructor
               | [ |- List.Forall _ (_::_) ] => constructor
               | [ |- List.Forall _ (map _ _) ] => apply Forall_map; unfold compose
               | [ |- @List.Forall nat _ _ ] => apply Forall_forall
               | [ |- context[match ?l with _ => _ end] ]
                 => destruct l
             end.
    Qed.

    Context (G : grammar CharType).

    Let data' : @parser_computational_types_dataT _ String
      := {| BaseTypes.predata := @rdp_list_predata _ G;
            BaseTypes.split_stateT str0 valid g := split_stateT |}.

    Global Instance only_one_nt_premethods : @parser_computational_dataT' _ _ data'
      := { split_string_for_production str0 valid := only_one_nt_split;
           split_string_for_production_correct str0 valid it its str := only_one_nt_split_correct_seq }.

    Global Instance only_one_nt_data : @boolean_parser_dataT _ _
      := { predata := @rdp_list_predata _ G;
           split_stateT := split_stateT;
           split_string_for_production := only_one_nt_split;
           split_string_for_production_correct it its str := only_one_nt_split_correct_seq }.

    Context (fallback_valid_prod : production CharType -> bool).

    Fixpoint only_one_nt_valid_prod
             (only_one_nt_valid : string -> bool)
             (p : production CharType)
    : bool
      := match p with
           | nil => true
           | (Terminal _)::p' => only_one_nt_valid_prod only_one_nt_valid p'
           | (NonTerminal nt)::p' => ((only_one_nt_valid_prod only_one_nt_valid p')
                                        && only_one_nt_valid nt
                                        && (has_only_terminals p' || fallback_valid_prod p))%bool
         end.

    Definition only_one_nt_valid : bool
      := split_valid (G := G) only_one_nt_valid_prod.

    Lemma only_one_nt_valid_prod_cons {fcv x xs}
    : only_one_nt_valid_prod fcv (x::xs)
      = match x with
          | Terminal _ => only_one_nt_valid_prod fcv xs
          | NonTerminal nt => ((only_one_nt_valid_prod fcv xs)
                                 && fcv nt
                                 && (has_only_terminals xs || fallback_valid_prod (x::xs)))%bool
        end.
    Proof.
      reflexivity.
    Qed.

    Lemma valid_if_has_only_terminals {fcv p}
          (H : has_only_terminals p = true)
    : only_one_nt_valid_prod fcv p = true.
    Proof.
      induction p; t_equality.
    Qed.

    Lemma has_only_terminals_min_parse_length
          {str0 valid strs its}
          (H : has_only_terminals its = true)
          (p : minimal_parse_of_production (String := String) (G := G) str0 valid strs its)
    : List.length its = Length strs.
    Proof.
      generalize dependent strs.
      induction its; simpl in *.
      { intros strs p.
        inversion p; subst.
        rewrite Length_Empty; reflexivity. }
      { destruct_head item.
        { intros strs p.
          inversion p; subst.
          inversion_head @minimal_parse_of_item.
          rewrite <- Length_correct, Singleton_Length, <- IHits by assumption.
          reflexivity. }
        { exfalso; discriminate. } }
    Qed.

    Context (fallback_split_ind : forall x xs, fallback_valid_prod (x::xs) -> fallback_valid_prod xs).
    Context (fallback_split_prod_each
             : forall nt_it its str0 valid s1 s2 (pf : s1 ++ s2 ≤s str0) st,
                 has_only_terminals its = false
                 -> MinimalParse.minimal_parse_of_item (G := G) str0 valid s1 (NonTerminal CharType nt_it)
                 -> MinimalParse.minimal_parse_of_production (G := G) str0 valid s2 its
                 -> fallback_valid_prod ((NonTerminal _ nt_it)::its) = true
                 -> In
                      (Length s1)
                      (fallback_split (NonTerminal _ nt_it) its {| string_val := s1 ++ s2; state_val := st |})).

    Hint Rewrite NPeano.Nat.add_sub : equality_t_db.
    Hint Rewrite @has_only_terminals_min_parse_length using eassumption : equality_t_end_db.

    Lemma only_one_nt_split_complete
          (H : only_one_nt_valid = true)
    : forall str0 valid (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) nt,
        is_valid_nonterminal initial_nonterminals_data nt ->
        ForallT
          (Forall_tails
             (fun prod =>
                match prod with
                  | [] => True
                  | it :: its =>
                    @split_list_completeT _ String G only_one_nt_data str0 valid it its str pf
                                          (@only_one_nt_split it its str)
                end)) (Lookup G nt).
    Proof.
      apply (split_complete_simple only_one_nt_valid_prod).
      { intros ? ? ? p.
        induction p; t_equality. }
      { intros f x xs; revert x.
        induction xs; t_equality. }
      { intros.
        cut ({st1st2 : _ |
              In
                ({| string_val := fst (SplitAt (Length s1) (s1 ++ s2)); state_val := fst st1st2 |},
                 {| string_val := snd (SplitAt (Length s1) (s1 ++ s2)); state_val := snd st1st2 |})
                (only_one_nt_split it its {| string_val := s1 ++ s2; state_val := st |})}).
        { rewrite SplitAt_concat_correct; simpl; trivial. }
        { exists (split_state_at (Length s1) st).
          unfold only_one_nt_split.
          t_equality;
            try solve [ rewrite has_only_terminals_min_parse_length by eassumption;
                        rewrite NPeano.Nat.add_sub;
                        reflexivity
                      | eapply fallback_split_prod_each;
                        repeat first [ eassumption
                                     | constructor ] ]. } }
      { exact H. }
    Qed.

    Global Instance only_one_nt_cdata' H : @boolean_parser_completeness_dataT' _ _ G only_one_nt_data
      := { split_string_for_production_complete := @only_one_nt_split_complete H }.

    Global Instance only_one_nt_cdata H : @boolean_parser_correctness_dataT _ _ G
      := { data := only_one_nt_data;
           rdata' := rdp_list_rdata';
           cdata' := only_one_nt_cdata' H }.
  End only_one_nt_splitter.
End StringT.
