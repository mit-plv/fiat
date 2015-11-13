(** * Definition of the part of boolean-returning CFG parser-recognizer that instantiates things to lists *)
Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser_list.
  Context {Char} {HSL : StringLike Char} {HLSP : StringLikeProperties Char} {G : grammar Char}.
  Definition rdp_list_nonterminals_listT : Type := list String.string.
  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> String.string -> bool
    := fun ls nt => list_bin string_beq nt ls.
  Definition rdp_list_initial_nonterminals_correct
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal (Valid_nonterminals G) nt) <-> List.In nt (Valid_nonterminals G)
    := fun nt => conj (list_in_bl (@string_bl)) (list_in_lb (@string_lb)).

  Definition filter_out_eq (nt : String.string) (ls : list String.string)
    := Eval unfold filter_out in filter_out (string_beq nt) ls.

  Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> String.string -> rdp_list_nonterminals_listT
    := fun ls nt =>
         filter_out_eq nt ls.

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
    intros ls prods H.
    unfold rdp_list_is_valid_nonterminal, rdp_list_nonterminals_listT_R, rdp_list_remove_nonterminal, ltof in *.
    apply list_in_bl in H; [ | solve [ intros; apply string_bl; trivial ] ].
    change filter_out_eq with (fun nt ls => filter_out (string_beq nt) ls); cbv beta.
    rewrite filter_out_filter.
    match goal with
      | [ H : In ?prods ?ls |- context[filter ?f ?ls] ]
        => assert (~In prods (filter f ls))
    end.
    { intro H'.
      apply filter_In in H'.
      destruct H' as [? H'].
      rewrite (fun x => string_lb (eq_refl x)) in *; simpl in *; congruence. }
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
    change filter_out_eq with (fun nt ls => filter_out (string_beq nt) ls); cbv beta.
    setoid_rewrite filter_out_filter.
    repeat match goal with
             | _ => exfalso; congruence
             | _ => reflexivity
             | _ => assumption
             | [ |- appcontext[if ?E then _ else _] ] => destruct E
             | _ => intro
             | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
             | [ H : list_bin _ _ _ = true |- _ ] => apply list_in_bl in H; [ | solve [ intros; apply string_bl; trivial ] ]
             | [ |- list_bin _ _ _ = true ] => apply list_in_lb; [ solve [ intros; apply string_lb; trivial ] | ]
           end.
  Qed.

  Lemma rdp_list_remove_nonterminal_2
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = false
      <-> rdp_list_is_valid_nonterminal ls ps' = false \/ ps = ps'.
  Proof.
    unfold rdp_list_is_valid_nonterminal, rdp_list_remove_nonterminal.
    change filter_out_eq with (fun nt ls => filter_out (string_beq nt) ls); cbv beta.
    setoid_rewrite filter_out_filter.
    repeat match goal with
             | _ => exfalso; congruence
             | _ => reflexivity
             | _ => progress subst
             | _ => intro
             | [ H : @eq bool ?x ?y -> False |- _ ] => apply Bool.eq_true_not_negb in H
             | [ H : context[In _ (filter _ _)] |- _ ] => rewrite filter_In in H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
             | [ |- true = false \/ _ ] => right
             | [ |- ?x = ?x \/ _ ] => left; reflexivity
             | [ H : ~(_ /\ ?x = ?x) |- _ ] => specialize (fun y => H (conj y eq_refl))
             | [ H : ~(?T /\ _), H' : ?T |- _ ] => specialize (fun y => H (conj H' y))
             | [ H : (?T /\ _) -> False, H' : ?T |- _ ] => specialize (fun y => H (conj H' y))
             | [ H : _ \/ _ |- _ ] => destruct H
             | [ |- _ <-> _ ] => split
             | [ H : appcontext[match ?E with left _ => _ | right _ => _ end] |- _ ] => destruct E
             | [ |- appcontext[match ?E with left _ => _ | right _ => _ end] ] => destruct E
             | [ H : _ |- _ ] => rewrite Bool.negb_involutive in H
             | [ H : string_beq _ _ = true |- _ ] => apply string_bl in H
             | [ H : context[string_beq ?x ?x] |- _ ] => rewrite (string_lb (eq_refl x)) in H
             | _ => progress simpl in *
             | [ H : list_bin _ _ _ = true |- _ ] => apply list_in_bl in H; [ | solve [ intros; apply string_bl; trivial ] ]
             | [ |- list_bin _ _ _ = true ] => apply list_in_lb; [ solve [ intros; apply string_lb; trivial ] | ]
             | [ |- context[list_bin ?x ?y ?z = false] ] => case_eq (list_bin x y z)
             | [ H : list_bin _ _ _ = false |- _ ] => apply Bool.not_true_iff_false in H
             | [ H : list_bin _ _ _ <> true |- _ ] => specialize (fun H' => H (list_in_lb (@string_lb) H'))
           end.
  Qed.

  Lemma rdp_list_remove_nonterminal_noninc (ls : rdp_list_nonterminals_listT) (nonterminal : string)
  : ~ rdp_list_nonterminals_listT_R ls (rdp_list_remove_nonterminal ls nonterminal).
  Proof.
    simpl. unfold ltof, rdp_list_remove_nonterminal.
    change filter_out_eq with (fun nt ls => filter_out (string_beq nt) ls); cbv beta.
    setoid_rewrite filter_out_filter.
    intro H.
    cut (Datatypes.length ls < Datatypes.length ls); try omega.
    eapply Lt.lt_le_trans; [ eassumption | ].
    apply filter_list_dec.
  Qed.

  Global Instance rdp_list_predata : parser_computational_predataT
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := Valid_nonterminals G;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_length := @List.length _
         (*nonterminals_listT_R := rdp_list_nonterminals_listT_R;*)
         (*remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;*)
         (*ntl_wf := rdp_list_ntl_wf*) }.

  Global Instance rdp_list_rdata' : @parser_removal_dataT' _ G rdp_list_predata
    := { remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         remove_nonterminal_noninc := rdp_list_remove_nonterminal_noninc;
         initial_nonterminals_correct := rdp_list_initial_nonterminals_correct;
         remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2 }.
End recursive_descent_parser_list.
