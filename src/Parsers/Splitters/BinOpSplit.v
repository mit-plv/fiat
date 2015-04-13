(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String NPeano.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.BaseTypes Parsers.CorrectnessBaseTypes.
Require Import Parsers.Splitters.RDPList.
Require Import Common.
Require Import Common.List.Operations Common.List.ListFacts Common.Equality.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Common.Wf.

Require Import Parsers.Splitters.Reflective.
Require Import Parsers.Splitters.OnlyOneNonterminal.

Require Import Parsers.MinimalParse.
Require Import Parsers.ContextFreeGrammarNotations.
Require Import Parsers.Grammars.ExpressionNumPlus.

Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.
Section StringT.
  Context {CharType} {String : string_like CharType}
          (is_bin_op : CharType -> bool).

  Definition next_bin_op (s : String) : option nat
    := Fold
         String
         (fun _ => option nat)
         None
         (fun ch _ cur_next
          => if is_bin_op ch
             then Some 0
             else option_map S cur_next)
         s.

  Let String' : Type := String.
  Let StringT := (StringWithSplitState String (fun _ => True)).

  Local Coercion StringT_of_string (s : String') : StringT :=
    {| string_val := s ; state_val := I |}.

  Lemma StringT_eq {x y : StringT} (H : string_val x = string_val y)
  : x = y.
  Proof.
    destruct x as [? [] ], y as [? [] ]; simpl in *; subst; reflexivity.
  Qed.

  Definition bin_op_split_nat
             (it : item CharType)
             (its : production CharType)
             (str : StringT)
  : list nat
    := match next_bin_op str with
         | Some n => [n]
         | None => nil
       end.

  Definition bin_op_split
             (it : item CharType)
             (its : production CharType)
             (str : StringT)
  : list (StringT * StringT)
    := only_one_nt_split
         I (fun _ _ _ => (I, I)) bin_op_split_nat
         it its str.

  Context (fallback_valid_prod : production CharType -> bool).

  Check only_one_nt_split_complete.



  Definition first_char_split
             (it : item CharType)
             (its : production CharType)
             (str : StringT)
  : list (StringT * StringT).
  Proof.




End StringT.


  Local Coercion StringT_of_string (s : String') : StringT :=
    {| string_val := s ; state_val := I |}.

  Lemma StringT_eq {x y : StringT} (H : string_val x = string_val y)
  : x = y.
  Proof.
    destruct x as [? [] ], y as [? [] ]; simpl in *; subst; reflexivity.
  Qed.

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
             | _ => progress destruct_head @StringWithSplitState
             | [ |- _ = _ :> (_ * _)%type ] => apply f_equal2
             | [ |- _ = _ :> StringT ] => apply StringT_eq
             | [ |- _ \/ False ] => left
             | _ => rewrite RightId
             | _ => rewrite LeftId
             | [ H : context[string_dec ?str ?x] |- _ ] => atomic x; destruct (string_dec str x)
             | [ |- context[match ?s with _ => _ end] ] => atomic s; destruct s
             | [ H : context[match ?s with _ => _ end] |- _ ] => atomic s; destruct s
             | _ => rewrite substring_correct3'
             | [ |- context[SplitAt _ ?n (?s1 ++ ?s2)] ]
               => replace n with (Length s1) by (rewrite Singleton_Length; trivial);
                 rewrite SplitAt_concat_correct
             | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ nil |- _ ] => inversion H; clear H
             | _ => solve [ eauto ]
           end.

  Section first_char_splitter.
    Context (fallback_split
             : forall (it : item CharType)
                      (its : production CharType)
                      (str : StringT),
                 list (StringT * StringT)).

    Definition first_char_split
               (it : item CharType)
               (its : production CharType)
               (str : StringT)
    : list (StringT * StringT)
      := match its with
           | nil => [(str, (Empty _ : String') : StringT)]
           | _::_ => match it with
                       | Terminal _
                         => [(((fst (SplitAt _ 1 str) : String') : StringT),
                              ((snd (SplitAt _ 1 str) : String') : StringT))]
                       | NonTerminal _
                         => fallback_split it its str
                     end
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
             end.
    Qed.

    Context (G : grammar CharType).
    Context (fallback_split_correct_eq
             : forall it its (str : StringT),
                 List.Forall
                   (fun strs : StringT * StringT => fst strs ++ snd strs =s str)
                   (fallback_split it its str)).

    Global Instance first_char_premethods : @parser_computational_dataT' _ _ (@rdp_list_data' _ _ G)
      := { split_string_for_production str0 valid := first_char_split;
           split_string_for_production_correct str0 valid it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

    Global Instance first_char_data : @boolean_parser_dataT _ _
      := { predata := @rdp_list_predata _ G;
           split_stateT str := True;
           split_string_for_production := first_char_split;
           split_string_for_production_correct it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

    Fixpoint first_char_valid_prod
             (first_char_valid : string -> bool)
             (p : production CharType)
    : bool
      := match p with
           | nil => true
           | (NonTerminal nt)::nil => first_char_valid nt
           | (Terminal _)::p' => first_char_valid_prod first_char_valid p'
           | (NonTerminal _)::_::_ => false
         end.

    Definition first_char_valid : bool
      := split_valid (G := G) first_char_valid_prod.

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
      { t_equality. }
      { intros.
        exists (I, I).
        unfold first_char_split.
        t_equality. }
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
