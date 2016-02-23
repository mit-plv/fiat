Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common Fiat.Common.Wf.
Require Fiat.Parsers.BooleanRecognizer.
Require Fiat.Parsers.SimpleRecognizer.
Require Fiat.Parsers.BooleanRecognizerExt.

Coercion bool_of_option {A} (x : option A) : bool :=
  match x with
    | Some _ => true
    | None => false
  end.

Section eq.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.
  Context (str : String).

  Local Notation simple_parse_of := (@simple_parse_of Char) (only parsing).
  Local Notation simple_parse_of_production := (@simple_parse_of_production Char) (only parsing).

  Section simple.

    Local Ltac pre_t :=
      idtac;
      match goal with
        | [ |- ?x = bool_of_option ?y ]
          => let x' := head x in
             let y' := head y in
             unfold x' at 1, y' at 1
      end.
    Local Ltac t lem :=
      try pre_t;
      repeat match goal with
               | _ => progress subst
               | [ |- _ = _ ] => reflexivity
               | _ => rewrite !lem
               | _ => rewrite !map_map
               | [ H : ?x <= ?y, H' : ?x <= ?y |- _ ]
                 => assert (H = H') by apply Le.le_proof_irrelevance;
                   subst
               | [ |- context[?E] ]
                 => not is_var E;
                   match type of E with
                     | _ <= _
                       => generalize E; intro
                   end
               | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:?
               | _ => progress unfold option_map
               | [ |- map _ _ = map _ _ ]
                 => apply (_ : Proper (pointwise_relation _ _ ==> eq ==> eq) (@map _ _));
                   [ intro | reflexivity ]
               | _ => progress simpl in *
               | _ => congruence
             end.

    Lemma parse_item'_eq
          (str_matches_nonterminal : nonterminal_carrierT -> bool)
          (str_matches_nonterminal' : nonterminal_carrierT -> option simple_parse_of)
          (str_matches_nonterminal_eq : forall nt,
                                          str_matches_nonterminal nt = str_matches_nonterminal' nt)
          (offset : nat) (len : nat)
          (it : item Char)
    : BooleanRecognizer.parse_item' str str_matches_nonterminal offset len it = SimpleRecognizer.parse_item' str str_matches_nonterminal' offset len it.
    Proof.
      t str_matches_nonterminal_eq.
    Qed.

    Section production.
      Context {len0}
              (parse_nonterminal
               : forall (offset : nat) (len : nat),
                   len <= len0
                   -> nonterminal_carrierT
                   -> bool)
              (parse_nonterminal'
               : forall (offset : nat) (len : nat),
                   len <= len0
                   -> nonterminal_carrierT
                   -> option simple_parse_of)
              (parse_nonterminal_eq
               : forall offset len pf nt, parse_nonterminal offset len pf nt = parse_nonterminal' offset len pf nt).

      Lemma fold_left_option_orb_eq {A} b b' ls ls'
            (Hb : b = @bool_of_option A b')
            (Heq : ls = List.map bool_of_option ls')
      : fold_left orb ls b
        = fold_left SimpleRecognizer.option_orb ls' b'.
      Proof.
        subst.
        revert b'.
        induction ls' as [|?? IHls']; simpl; [ reflexivity | intro ].
        rewrite <- IHls'; destruct b', a; simpl; reflexivity.
      Qed.

      Lemma parse_production'_for_eq
            (splits : production_carrierT -> String -> nat -> nat -> list nat)
            (offset : nat)
            (len : nat)
            (pf : len <= len0)
            (prod_idx : production_carrierT)
      : BooleanRecognizer.parse_production'_for str parse_nonterminal splits offset pf prod_idx
        = SimpleRecognizer.parse_production'_for str parse_nonterminal' splits offset pf prod_idx.
      Proof.
        pre_t.
        repeat match goal with
                 | [ |- appcontext[list_rect ?P ?N ?C] ]
                   => not is_var C;
                     let P' := fresh "P'" in
                     let N' := fresh "N'" in
                     let C' := fresh "C'" in

                     set (P' := P);
                       set (N' := N);
                       set (C' := C)
               end.
        generalize (to_production prod_idx); intro ps.
        revert prod_idx offset len pf.
        induction ps as [|p ps IHps].
        { simpl; intros; t I. }
        { simpl; intros.
          pre_t.
          apply fold_left_option_orb_eq; [ reflexivity | ].
          t I.
          erewrite parse_item'_eq by (intros; eapply parse_nonterminal_eq).
          rewrite IHps; clear IHps.
          t I. }
      Qed.

      Lemma parse_production'_eq
            (offset : nat)
            (len : nat)
            (pf : len <= len0)
            (prod_idx : production_carrierT)
      : BooleanRecognizer.parse_production' str parse_nonterminal offset pf prod_idx
        = SimpleRecognizer.parse_production' str parse_nonterminal' offset pf prod_idx.
      Proof.
        pre_t.
        apply parse_production'_for_eq.
      Qed.
    End production.

    Section productions.
      Context {len0}
              (parse_nonterminal
               : forall (offset : nat)
                        (len : nat)
                        (pf : len <= len0),
                   nonterminal_carrierT -> bool)
              (parse_nonterminal'
               : forall (offset : nat)
                        (len : nat)
                        (pf : len <= len0),
                   nonterminal_carrierT -> option simple_parse_of)
              (parse_nonterminal_eq
               : forall offset len pf nt,
                   parse_nonterminal offset len pf nt
                   = parse_nonterminal' offset len pf nt).

      Lemma fold_right_option_simple_parse_of_orb_eq b b' ls ls'
            (Hb : b = bool_of_option b')
            (Heq : ls = List.map bool_of_option ls')
      : fold_right orb b ls
        = fold_right (@SimpleRecognizer.option_simple_parse_of_orb Char) b' ls'.
      Proof.
        subst.
        revert b'.
        induction ls' as [|?? IHls']; simpl; [ reflexivity | intro ].
        rewrite IHls'; destruct b', a; simpl; try reflexivity;
        t I.
      Qed.

      Lemma parse_productions'_eq
            (offset : nat)
            (len : nat)
            (pf : len <= len0)
            (prods : list production_carrierT)
      : BooleanRecognizer.parse_productions' str parse_nonterminal offset pf prods
        = SimpleRecognizer.parse_productions' str parse_nonterminal' offset pf prods.
      Proof.
        pre_t.
        apply fold_right_option_simple_parse_of_orb_eq; [ reflexivity | ].
        t I.
        erewrite parse_production'_eq; [ reflexivity | ].
        intros; rewrite parse_nonterminal_eq; reflexivity.
      Qed.
    End productions.

    Section nonterminals.
      Section step.
        Context {len0 valid_len}
                (parse_nonterminal
                 : forall (p : nat * nat),
                     prod_relation lt lt p (len0, valid_len)
                     -> forall (valid : nonterminals_listT)
                               (offset : nat) (len : nat),
                          len <= fst p -> nonterminal_carrierT -> bool)
                (parse_nonterminal'
                 : forall (p : nat * nat),
                     prod_relation lt lt p (len0, valid_len)
                     -> forall (valid : nonterminals_listT)
                               (offset : nat) (len : nat),
                          len <= fst p -> nonterminal_carrierT -> option simple_parse_of)
                (parse_nonterminal_eq
                 : forall (p : nat * nat)
                          (pf : prod_relation lt lt p (len0, valid_len))
                          (valid : nonterminals_listT)
                          (offset : nat) (len : nat)
                          (pf' : len <= fst p)
                          (nt : nonterminal_carrierT),
                     parse_nonterminal p pf valid offset len pf' nt
                     = parse_nonterminal' p pf valid offset len pf' nt).

        Lemma parse_nonterminal_step_eq
              (valid : nonterminals_listT)
              (offset : nat)
              (len : nat)
              (pf : len <= len0)
              (nt : nonterminal_carrierT)
        : BooleanRecognizer.parse_nonterminal_step str parse_nonterminal valid offset pf nt
          = SimpleRecognizer.parse_nonterminal_step str parse_nonterminal' valid offset pf nt.
        Proof.
          pre_t.
          edestruct dec; simpl; edestruct lt_dec; simpl; try reflexivity;
          (erewrite parse_productions'_eq; [ reflexivity | ]);
          intros; rewrite <- parse_nonterminal_eq; try reflexivity.
          repeat (f_equal; []); intros.
          apply Le.le_proof_irrelevance.
        Qed.
      End step.

      Section wf.
        Lemma parse_nonterminal_or_abort_eq
        : forall (p : nat * nat)
                 (valid : nonterminals_listT)
                 (offset : nat) (len : nat)
                 (pf : len <= fst p)
                 (nt : nonterminal_carrierT),
            BooleanRecognizer.parse_nonterminal_or_abort str p valid offset pf nt
            = SimpleRecognizer.parse_nonterminal_or_abort str p valid offset pf nt.
        Proof.
          intros.
                 :
            -> option simple_parse_of
          := @Fix
               (nat * nat)
               _
               (well_founded_prod_relation lt_wf lt_wf)
               _
               (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

        Definition parse_nonterminal'
                   (nt : nonterminal_carrierT)
        : option simple_parse_of
          := @parse_nonterminal_or_abort
               (length str, nonterminals_length initial_nonterminals_data)
               initial_nonterminals_data
               0 (length str)
               (le_n _) nt.

        Definition parse_nonterminal
                   (nt : String.string)
        : option simple_parse_of
          := parse_nonterminal' (of_nonterminal nt).
      End wf.
    End nonterminals.

    Definition parse_item
               (it : item Char)
    : option simple_parse_of_item
      := parse_item' parse_nonterminal' 0 (length str) it.

    Definition parse_production
               (pat : production_carrierT)
    : option simple_parse_of_production
      := parse_production' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) 0 (reflexivity _) pat.

    Definition parse_productions
               (pats : list production_carrierT)
    : option simple_parse_of
      := parse_productions' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) 0 (reflexivity _) pats.
  End parts.
End simple.
End recursive_descent_parser.
