(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.BaseTypes Parsers.BooleanBaseTypes.
Require Import Parsers.Splitters.RDPList.
Require Import Common.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Common.Wf.

Require Import Parsers.MinimalParse.
Require Import Parsers.ContextFreeGrammarNotations.
Require Import Parsers.Grammars.ABStar.

Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.
Local Notation StringT := (StringWithSplitState string_stringlike (fun _ => True)).

Local Coercion StringT_of_string (s : string) : StringT :=
  {| string_val := s : string_stringlike ; state_val := I |}.

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
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress destruct_head sigT
           | _ => progress destruct_head prod
           | _ => progress destruct_head @StringWithSplitState
           | [ |- _ = _ :> (_ * _)%type ] => apply f_equal2
           | [ |- _ = _ :> StringT ] => apply StringT_eq
           | [ |- _ \/ False ] => left
           | [ H : context[(_ ++ "")%string] |- _ ] => generalize dependent H; simpl rewrite (RightId string_stringlike)
           | [ H : context[string_dec ?str ?x] |- _ ] => atomic x; destruct (string_dec str x)
           | [ |- context[match ?s with _ => _ end] ] => atomic s; destruct s
           | _ => rewrite substring_correct3'
           | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion H; clear H
           | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
           | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H
           | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ nil |- _ ] => inversion H; clear H
         end.


Section first_char_splitter.
  Context (fallback_split
           : forall (it : item Ascii.ascii)
                    (its : production Ascii.ascii)
                    (str : StringT),
               list (StringT * StringT)).

  Definition first_char_split
             (*str0 : string*)
             (*valid : nonterminals_listT*)
             (it : item Ascii.ascii)
             (its : production Ascii.ascii)
             (str : StringT)
  : list (StringT * StringT)
    := match its with
         | nil => [(str, "" : StringT)]
         | _::_ => match it with
                     | Terminal _
                       => [((match String.get 0 (string_val str) return string with
                               | Some ch => String.String ch ""
                               | None => ""
                             end : StringT),
                            (substring 1 (length (string_val str)) (string_val str) : StringT))]
                     | NonTerminal _
                       => fallback_split it its str
                   end
       end.

  Local Opaque string_dec.

  Lemma first_char_split_correct_seq {it its} {str : StringT}
        (f := fun strs : StringT * StringT => fst strs ++ snd strs =s str)
        (fallback_split_correct_eq : List.Forall f (fallback_split it its str))
  : List.Forall f (first_char_split it its str).
  Proof.
    unfold first_char_split; subst f.
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
             | _ => assumption
             | [ |- context[match ?l with _ => _ end] ]
               => atomic l; destruct l
             | [ |- context[match string_val ?s with _ => _ end] ]
               => atomic s; destruct s
             | [ |- context[(_ ++ "")%string] ]
               => simpl rewrite (RightId string_stringlike)
             | _ => rewrite substring_correct3'
             | [ |- context[string_dec ?x ?x] ] => rewrite string_dec_refl
             | [ |- context[String.get 0 ?s] ] => atomic s; destruct s
             | [ |- context[String.get 0 (string_val ?s)] ] => atomic s; destruct s
             | [ |- List.Forall _ [] ] => constructor
             | [ |- List.Forall _ (_::_) ] => constructor
           end.
  Qed.

  Context (G : grammar Ascii.ascii).
  Context (fallback_split_correct_eq
           : forall it its (str : StringT),
               List.Forall
                 (fun strs : StringT * StringT => fst strs ++ snd strs =s str)
                 (fallback_split it its str)).

  Global Instance first_char_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ G)
    := { split_string_for_production str0 valid := first_char_split;
         split_string_for_production_correct str0 valid it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

  Global Instance first_char_data : @boolean_parser_dataT _ string_stringlike
    := { predata := @rdp_list_predata _ G;
         split_stateT str := True;
         split_string_for_production := first_char_split;
         split_string_for_production_correct it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

  Fixpoint first_char_valid_prod
             (first_char_valid : string -> bool)
             (p : production Ascii.ascii)
  : bool
    := match p with
         | nil => true
         | (NonTerminal nt)::nil => first_char_valid nt
         | (Terminal _)::p' => first_char_valid_prod first_char_valid p'
         | (NonTerminal _)::_::_ => false
       end.

  Definition first_char_valid_step
             (nt_valid : nonterminals_listT)
             (first_char_valid : forall nt_valid', nonterminals_listT_R nt_valid' nt_valid -> string -> bool)
             (nt : string)
  : bool.
  Proof.
    refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal nt_valid nt)
            then
              let first_char_valid' := first_char_valid (remove_nonterminal nt_valid nt) (remove_nonterminal_dec _ _ _)
              in fold_right
                   andb
                   true
                   (map (first_char_valid_prod first_char_valid') (Lookup G nt))
            else
              is_valid_nonterminal initial_nonterminals_data nt);
    try assumption.
  Defined.

  Lemma first_char_valid_step_ext (valid : nonterminals_listT)
        f g
        (H : forall (valid' : nonterminals_listT)
                    (pf : nonterminals_listT_R valid' valid)
                    nt,
               f valid' pf nt = g valid' pf nt)
        nt
  : first_char_valid_step f nt = first_char_valid_step g nt.
  Proof.
    unfold first_char_valid_step.
    edestruct dec;
    f_equal.
    apply map_ext; intro x.
    induction x as [|x xs IHx]; trivial; simpl.
    destruct x; simpl; trivial.
    destruct xs; simpl; trivial.
  Qed.

  Definition first_char_valid : bool
    := fold_right
         andb
         true
         (map
            (Fix1 _ ntl_wf _ first_char_valid_step (Valid_nonterminals G))
            (Valid_nonterminals G)).

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
                  @split_list_completeT _ string_stringlike G first_char_data str0 valid str pf
                                        (@first_char_split it its str) it its
              end)) (Lookup G nt).
  Proof.
    intros str0 valid str pf nt H'.
    revert str0 valid str pf.
    unfold first_char_valid in *.
    pose proof H' as H''.
    hnf in H'.
    simpl in H''.
    unfold rdp_list_is_valid_nonterminal in H''.
    edestruct in_dec as [H'''|H''']; try discriminate; [].
    apply (fun H => fold_right_andb_map_in H _ H''') in H.
    simpl in H.
    rewrite Fix1_eq in H by apply first_char_valid_step_ext.
    unfold first_char_valid_step in H at 1.
    rewrite H' in H.
    edestruct dec; try (simpl in *; congruence).
    clear -H.
    { induction (Lookup G nt); simpl in *; trivial.
      intros; split;
      repeat match goal with
               | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | _ => solve [ eauto ]
             end.
      clear IHp.
      clear -H.
      let a := match goal with a : production _ |- _ => constr:a end in
      induction a; simpl in *; trivial.
      { intros; split;
        repeat match goal with
                 | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : context[match ?a with _ => _ end] |- _ ] => atomic a; destruct a
                 | _ => solve [ eauto ]
                 | _ => progress simpl in *
                 | _ => congruence
               end;
        clear; repeat intro;
        match goal with
          | [ p : sigT ?P' |- sigT ?P ]
            => refine (existT
                         P
                         ({| string_val := fst (projT1 p) ; state_val := I |},
                          {| string_val := snd (projT1 p) ; state_val := I |})
                         (_, snd (fst (projT2 p)), snd (projT2 p)))
        end;
        unfold first_char_split;
        t_equality. } }
  Qed.

  Global Instance first_char_cdata' H : @boolean_parser_completeness_dataT' _ _ G first_char_data
    := { remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2;
         split_string_for_production_complete := @first_char_split_complete H }.

  Global Instance first_char_cdata H : @boolean_parser_correctness_dataT _ _ G
    := { data := first_char_data;
         cdata' := first_char_cdata' H }.
End first_char_splitter.

Local Opaque string_dec.

Local Ltac unroll_valid_nonterminals :=
  intros;
  let H := match goal with H : is_true (is_valid_nonterminal _ _) |- _ => constr:H end in
  simpl in H;
    unfold rdp_list_is_valid_nonterminal in H; simpl in H;
    repeat match type of H with
             | context[string_dec ?str ?nt] => atomic nt; destruct (string_dec str nt); subst
             | is_true false => hnf in H; clear -H; exfalso; abstract discriminate
           end.

Local Ltac split_productions_cases :=
  repeat match goal with
           | _ => progress simpl in *
           | [ |- context[string_dec ?x ?x] ] => rewrite string_dec_refl
           | [ H : context[string_dec ?x ?x] |- _ ] => rewrite string_dec_refl in H
           | [ |- (_ * _)%type ] => split
           | _ => solve [ constructor ]
           | [ p : sigT ?P' |- sigT ?P ]
             => refine (existT
                          P
                          ({| string_val := fst (projT1 p) ; state_val := I |},
                           {| string_val := snd (projT1 p) ; state_val := I |})
                          (_, snd (fst (projT2 p)), snd (projT2 p)))
           | _ => intro
           | [ |- _ \/ False ] => left
           | [ |- _ = _ :> (_ * _)%type ] => apply f_equal2
           | [ |- _ = _ :> StringT ] => apply StringT_eq
         end.


Section on_ab_star.
  Definition ab_star_linear_split := first_char_split (fun _ _ _ => nil).
  Definition ab_star_linear_split_correct_seq {it its str} : List.Forall _ _
    := @first_char_split_correct_seq (fun _ _ _ => nil) it its str (Forall_nil _).

  Global Instance ab_star_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ ab_star_grammar)
    := first_char_premethods (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _).
  Global Instance ab_star_data : @boolean_parser_dataT _ string_stringlike
    := first_char_data (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _).

  Global Instance ab_star_cdata' : @boolean_parser_completeness_dataT' _ _ ab_star_grammar ab_star_data
    := first_char_cdata' (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _) eq_refl.

  Global Instance ab_star_cdata : @boolean_parser_correctness_dataT _ _ ab_star_grammar
    := first_char_cdata (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _) eq_refl.
End on_ab_star.

Section on_ab_star'.
  Definition ab_star'_linear_split := first_char_split (fun _ _ _ => nil).
  Definition ab_star'_linear_split_correct_seq {it its str} : List.Forall _ _
    := @first_char_split_correct_seq (fun _ _ _ => nil) it its str (Forall_nil _).

  Global Instance ab_star'_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ ab_star_grammar')
    := first_char_premethods (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _).
  Global Instance ab_star'_data : @boolean_parser_dataT _ string_stringlike
    := first_char_data (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _).

  Global Instance ab_star'_cdata' : @boolean_parser_completeness_dataT' _ _ ab_star_grammar' ab_star'_data
    := first_char_cdata' (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _) eq_refl.

  Global Instance ab_star'_cdata : @boolean_parser_correctness_dataT _ _ ab_star_grammar'
    := first_char_cdata (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _) eq_refl.
End on_ab_star'.
