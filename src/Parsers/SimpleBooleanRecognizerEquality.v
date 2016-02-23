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
               | [ |- context[match ?x with _ => _ end] ] => destruct x eqn:?
               | _ => progress unfold option_map
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
          rewrite map_map; simpl.
          apply (_ : Proper (pointwise_relation _ _ ==> eq ==> eq) (@map _ _));
            [ intro | reflexivity ].
          erewrite parse_item'_eq by (intros; eapply parse_nonterminal_eq).
          rewrite IHps; clear IHps.
          repeat match goal with
                   | [ H : ?x <= ?y, H' : ?x <= ?y |- _ ]
                     => assert (H = H') by apply Le.le_proof_irrelevance;
                       subst
                   | [ |- context[?E] ]
                     => not is_var E;
                       match type of E with
                         | _ <= _
                           => generalize E; intro
                       end
                 end.
          repeat match goal with
                   | _ => reflexivity
                   | [ |- context[bool_of_option ?x] ]
                     => destruct x eqn:?; simpl
                 end. }
      Qed.

      Definition parse_production'
                 (offset : nat)
                 (len : nat)
                 (pf : len <= len0)
                 (prod_idx : production_carrierT)
      : option simple_parse_of_production
        := parse_production'_for split_string_for_production offset pf prod_idx.
      End production.

      Section productions.
        Context {len0}
                (parse_nonterminal
                 : forall (offset : nat)
                          (len : nat)
                          (pf : len <= len0),
                     nonterminal_carrierT -> option simple_parse_of).

        Definition option_simple_parse_of_orb
                   (x : option simple_parse_of_production)
                   (xs : option simple_parse_of)
        : option simple_parse_of
          := match x, xs with
               | Some x', _ => Some (SimpleParseHead x')
               | None, Some xs' => Some (SimpleParseTail xs')
               | None, None => None
             end.

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions'
                   (offset : nat)
                   (len : nat)
                   (pf : len <= len0)
                   (prods : list production_carrierT)
        : option simple_parse_of
          := fold_right option_simple_parse_of_orb
                        None
                        (map (parse_production' parse_nonterminal offset pf)
                             prods).
      End productions.


      Section nonterminals.
        Section step.
          Context {len0 valid_len}
                  (parse_nonterminal
                   : forall (p : nat * nat),
                       prod_relation lt lt p (len0, valid_len)
                       -> forall (valid : nonterminals_listT)
                                 (offset : nat) (len : nat),
                            len <= fst p -> nonterminal_carrierT -> option simple_parse_of).

          Definition parse_nonterminal_step
                     (valid : nonterminals_listT)
                     (offset : nat)
                     (len : nat)
                     (pf : len <= len0)
                     (nt : nonterminal_carrierT)
          : option simple_parse_of.
          Proof.
            refine
              (option_rect
                 (fun _ => option simple_parse_of)
                 (fun parse_nonterminal
                  => parse_productions'
                       parse_nonterminal
                       offset
                       (len := len)
                       (sumbool_rect
                          (fun b => len <= (if b then len else len0))
                          (fun _ => le_n _)
                          (fun _ => _)
                          (lt_dec len len0))
                       (nonterminal_to_production nt))
                 None
                 (sumbool_rect
                    (fun b => option (forall (offset' : nat) (len' : nat), len' <= (if b then len else len0) -> nonterminal_carrierT -> option simple_parse_of))
                    (fun _ => (** [str] got smaller, so we reset the valid nonterminals list *)
                       Some (@parse_nonterminal
                               (len, nonterminals_length initial_nonterminals_data)
                               (or_introl _)
                               initial_nonterminals_data))
                    (fun _ => (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                       sumbool_rect
                         (fun _ => option (forall (offset' : nat) (len' : nat), len' <= len0 -> nonterminal_carrierT -> option simple_parse_of))
                         (fun is_valid => (** It was valid, so we can remove it *)
                            Some (@parse_nonterminal
                                    (len0, pred valid_len)
                                    (or_intror (conj eq_refl _))
                                    (remove_nonterminal valid nt)))

                         (fun _ => (** oops, we already saw this nonterminal in the past.  ABORT! *)
                            None)
                         (Sumbool.sumbool_of_bool (negb (EqNat.beq_nat valid_len 0) && is_valid_nonterminal valid nt)))
                    (lt_dec len len0)));
            first [ assumption
                  | simpl;
                    generalize (proj1 (proj1 (Bool.andb_true_iff _ _) is_valid));
                    clear; intro;
                    abstract (
                        destruct valid_len; try apply Lt.lt_n_Sn; [];
                        exfalso; simpl in *; congruence
                  ) ].
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_or_abort
          : forall (p : nat * nat)
                   (valid : nonterminals_listT)
                   (offset : nat) (len : nat),
              len <= fst p
              -> nonterminal_carrierT
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
