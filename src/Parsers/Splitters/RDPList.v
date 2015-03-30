(** * Definition of the part of boolean-returning CFG parser-recognizer that instantiates things to lists *)
Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Wf_nat.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser_list.
  Context {string} {HSL : StringLike string} {HLSP : StringLikeProperties string} {G : grammar string}.
  Definition rdp_list_nonterminals_listT : Type := list String.string.
  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> String.string -> bool
    := fun ls nt => if in_dec string_dec nt ls then true else false.
  Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> String.string -> rdp_list_nonterminals_listT
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

  Global Instance rdp_list_rdata' : @parser_removal_dataT' rdp_list_predata
    := { remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2 }.
End recursive_descent_parser_list.
