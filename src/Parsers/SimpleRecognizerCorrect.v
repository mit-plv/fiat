(** * Proof that SimpleRecognizer outputs correct parse trees *)
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.SimpleRecognizer Fiat.Parsers.SimpleRecognizerExt.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectnessMorphisms.
Require Import Fiat.Common Fiat.Common.Wf.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          (*{cdata : @boolean_parser_completeness_dataT' Char _ _ G _}*)
          {rdata : @parser_removal_dataT' _ G _}
          (*(gvalid : grammar_valid G)*).
  (** XXX TODO: remove the above commented out variables if they end up not being necessary. *)

  (** To prove the following, look in SimpleRecognizer, SimpleBooleanRecognizerEquality, SimpleRecognizerExt, BooleanRecognizerCorrect, in that order *)
  Context (str : String).

  Local Ltac t'_safe :=
    idtac;
    match goal with
    | _ => assumption
    | _ => progress destruct_head False
    | _ => progress simpl in *
    | _ => progress simpl_simple_parse_of_correct
    | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
    | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
    | _ => intro
    | _ => congruence
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
    | [ H : SimpleParseProductionCons _ _ = SimpleParseProductionCons _ _ |- _ ] => inversion H; clear H
    | _ => progress subst
    | [ H : context[List.map to_production (nonterminal_to_production (of_nonterminal _))] |- _ ]
      => rewrite nonterminal_to_production_correct in H
    | _ => erewrite unsafe_get_correct by eassumption
    | [ |- is_true (andb _ _) ] => apply Bool.andb_true_iff
    | [ H : context[substring 0 (length ?str) ?str] |- _ ]
      => rewrite Properties.substring_correct3' in H
    | _ => progress unfold option_map in *
    | [ |- context[length (substring _ 0 _)] ]
      => rewrite Properties.substring_length
    | _ => progress rewrite ?Minus.minus_diag, ?Min.min_0_r, ?Min.min_idempotent
    | [ H : _ |- _ ] => progress rewrite ?Minus.minus_diag, ?Min.min_0_r in H
    | [ |- context[min ?x ?y - ?y] ] => rewrite <- (NPeano.Nat.sub_min_distr_r x y y)
    | [ H : EqNat.beq_nat ?x 0 = true |- _ ]
      => is_var x; apply EqNat.beq_nat_true in H
    | [ |- cons _ _ = nil ] => exfalso
    | [ |- _ /\ cons _ _ = nil ] => exfalso
    | _ => progress specialize_by ltac:(exact eq_refl)
    | _ => progress specialize_by omega
    | [ |- ?x = ?x \/ _ ] => left; reflexivity
    | [ H : context[to_production (production_tl _)] |- _ ]
      => rewrite production_tl_correct in H
    | [ H : ?x = cons _ _, H' : appcontext[List.tl ?x] |- _ ]
      => rewrite H in H'
    | [ H : cons _ _ = ?x, H' : appcontext[List.tl ?x] |- _ ]
      => rewrite <- H in H'
    | [ H : ?x + ?y <= ?z |- _ \/ ?x + min ?a ?y <= ?z ]
      => right; clear -H; apply Min.min_case_strong; omega
    | [ H : ?T |- _ \/ ?T ] => right; assumption
    | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
    end.

  Local Ltac t'_unsafe :=
    idtac;
    match goal with
    | _ => progress destruct_head or
    | [ H : andb (EqNat.beq_nat _ 1) (char_at_matches _ _ _) = true |- _ ]
      => apply Properties.char_at_matches_is_char_no_ex in H; [ | reflexivity || assumption ]
    | [ H : ?parse_nonterminal (of_nonterminal _) = Some _,
            IH : forall nt p, ?parse_nonterminal (of_nonterminal nt) = Some p -> _ |- _ ]
      => specialize (IH _ _ H)
    | [ |- ?x = ?x /\ _ ] => split; [ reflexivity | ]
    | [ |- _ /\ ?x = ?x ] => split; [ | reflexivity ]
    end.

  Local Ltac t' := first [ t'_safe | t'_unsafe ].

  Local Ltac t := repeat t'.

  Section parts.
    Lemma parse_item'_correct
          (offset : nat) (len : nat)
          (Hlen : len = 0 \/ offset + len <= length str)
          (parse_nonterminal : nonterminal_carrierT -> option simple_parse_of)
          (parse_nonterminal_correct
           : forall nt p,
              parse_nonterminal (of_nonterminal nt) = Some p
              -> simple_parse_of_item_correct G (substring offset len str) (NonTerminal nt) (SimpleParseNonTerminal nt p))
          (it : item Char) p
    : parse_item' str parse_nonterminal offset len it = Some p
      -> simple_parse_of_item_correct G (substring offset len str) it p.
    Proof. destruct it, p; t. Qed.

    Section production.
      Context {len0}
              (parse_nonterminal
               : forall (offset : nat) (len : nat),
                  len <= len0
                  -> nonterminal_carrierT
                  -> option simple_parse_of)
              (parse_nonterminal_correct
               : forall offset len (Hlen : len = 0 \/ offset + len <= length str) pf nt p,
                  parse_nonterminal offset len pf (of_nonterminal nt) = Some p
                  -> simple_parse_of_item_correct G (substring offset len str) (NonTerminal nt) (SimpleParseNonTerminal nt p)).

      Lemma parse_production'_for_correct
            (splits : production_carrierT -> String -> nat -> nat -> list nat)
            (offset : nat) (len : nat)
            (Hlen : len = 0 \/ offset + len <= length str)
            (pf : len <= len0)
            (prod_idx : production_carrierT) p
        : parse_production'_for str parse_nonterminal splits offset pf prod_idx = Some p
          -> simple_parse_of_production_correct G (substring offset len str) (to_production prod_idx) p.
      Proof.
        unfold parse_production'_for.
        match goal with
        | [ |- appcontext G[list_rect ?P' ?N' ?C' ?ls'] ]
          => set (P := P');
               set (N := N');
               set (C := C');
               remember ls' as ls eqn:Hls
        end;
          revert offset len Hlen pf.
        revert prod_idx Hls p.
        induction ls as [|l ls].
        { simpl; subst P N C; t. }
        { destruct p; simpl; unfold C at 1; t;
          match goal with
          | [ H : context[List.fold_left _ _ _] |- _ ]
            => rewrite <- List.fold_left_rev_right, <- List.map_rev in H
          end;
          match goal with
          | [ H : List.fold_right
                    _ None
                    (List.map
                       (fun n => option_SimpleParseProductionCons
                                   _
                                   _)
                       ?ls)
                  = Some _ |- _ ]
            => generalize dependent ls; simpl in *;
               let ls' := fresh in
               intro ls'; induction ls'
          end;
          unfold option_orb, option_SimpleParseProductionCons in *;
          repeat t'_safe;
          try solve [ t ];
          repeat match goal with
                 | [ H : parse_item' _ _ _ _ _ = Some _ |- _ ]
                   => apply parse_item'_correct in H;
                      [
                      | solve [ t ]..
                      | intros; eapply parse_nonterminal_correct; [ | eassumption ]; solve [ t ] ]
                 | [ IH : forall prod_idx pf p offset len Hlen pf',
                       list_rect ?P ?N ?C ?ls prod_idx offset len pf' = Some p -> _,
                       H : list_rect ?P ?N ?C ?ls _ _ _ _ = Some _ |- _ ]
                   => specialize (fun Hlen pf => IH _ pf _ _ _ Hlen _ H)
                 end;
          specialize_by ltac:(solve [ t ]);
          repeat t'_safe.
          { setoid_rewrite take_take.
            setoid_rewrite drop_take.
            setoid_rewrite drop_drop.
            setoid_rewrite (Plus.plus_comm _ offset).
            eexists; t; split; eassumption. }
          { setoid_rewrite take_take.
            setoid_rewrite drop_take.
            setoid_rewrite drop_drop.
            setoid_rewrite (Plus.plus_comm _ offset).
            eexists; split; [ eassumption | t ]. } }
      Qed.

      Lemma parse_production'_correct
            (offset : nat) (len : nat)
            (Hlen : len = 0 \/ offset + len <= length str)
            (pf : len <= len0)
            (prod_idx : production_carrierT) p
        : parse_production' str parse_nonterminal offset pf prod_idx = Some p
          -> simple_parse_of_production_correct G (substring offset len str) (to_production prod_idx) p.
      Proof.
        apply parse_production'_for_correct; assumption.
      Qed.
    End production.

    Section productions.
      Context {len0}
              (parse_nonterminal
               : forall (offset : nat)
                        (len : nat)
                        (pf : len <= len0),
                  nonterminal_carrierT -> option simple_parse_of)
              (parse_nonterminal_correct
               : forall offset len (Hlen : len = 0 \/ offset + len <= length str) pf nt p,
                  parse_nonterminal offset len pf (of_nonterminal nt) = Some p
                  -> simple_parse_of_item_correct G (substring offset len str) (NonTerminal nt) (SimpleParseNonTerminal nt p)).

      Definition parse_productions'_correct
                 (offset : nat) (len : nat)
                 (Hlen : len = 0 \/ offset + len <= length str)
                 (pf : len <= len0)
                 (prods : list production_carrierT)
                 p
        : parse_productions' str parse_nonterminal offset pf prods = Some p
          -> simple_parse_of_correct G (substring offset len str) (List.map to_production prods) p.
      Proof.
        unfold parse_productions'.
        revert p; induction prods as [|x xs IHxs]; intros; destruct p; unfold option_simple_parse_of_orb in *;
          t.
        { eapply parse_production'_correct; [ eassumption | t.. | eassumption ]. }
        { eapply parse_production'_correct; [ eassumption | t.. | eassumption ]. }
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
                      len <= fst p -> nonterminal_carrierT -> option simple_parse_of)
                (parse_nonterminal_correct
                 : forall p0 wf valid offset len (Hlen : len = 0 \/ offset + len <= length str) pf nt p,
                    parse_nonterminal p0 wf valid offset len pf (of_nonterminal nt) = Some p
                    -> simple_parse_of_item_correct G (substring offset len str) (NonTerminal nt) (SimpleParseNonTerminal nt p)).

        Lemma parse_nonterminal_step_correct
                   (valid : nonterminals_listT)
                   (offset : nat) (len : nat)
                   (Hlen : len = 0 \/ offset + len <= length str)
                   (pf : len <= len0)
                   nt
                   p
          : parse_nonterminal_step str parse_nonterminal valid offset pf (of_nonterminal nt) = Some p
            -> simple_parse_of_correct G (substring offset len str) (List.map to_production (nonterminal_to_production (of_nonterminal nt))) p.
        Proof.
          specialize (fun p00 p01 wf valid => @parse_nonterminal_correct (p00, p01) wf valid).
          unfold parse_nonterminal_step, option_rect; t;
            unfold sumbool_rect in *; t;
              let H := match goal with H : parse_productions' _ _ _ _ _ = Some _ |- _ => H end in
              (eapply parse_productions'_correct in H;
               [ assumption | .. ]);
                eauto with nocore;
                omega.
        Qed.
      End step.

      Section wf.
        Lemma parse_nonterminal_or_abort_correct
        : forall (p : nat * nat)
                 (valid : nonterminals_listT)
                 (offset : nat) (len : nat)
                 (Hlen : len = 0 \/ offset + len <= length str)
                 (pf : len <= fst p)
                 nt
                 pt,
          parse_nonterminal_or_abort str p valid offset pf (of_nonterminal nt) = Some pt
          -> simple_parse_of_correct G (substring offset len str) (List.map to_production (nonterminal_to_production (of_nonterminal nt))) pt.
        Proof.
          unfold parse_nonterminal_or_abort.
          intro p.
          let Rwf := match goal with |- appcontext[Fix ?Rwf] => Rwf end in
          induction (Rwf p) as [?? IH].
          intros ??????? HF.
          rewrite Fix5_eq in HF
                          by (intros; apply parse_nonterminal_step_ext; assumption).
          eapply parse_nonterminal_step_correct; [ | assumption | eassumption ].
          simpl; intros; simpl_simple_parse_of_correct.
        Admitted.
        (*
        Lemma parse_nonterminal'_correct
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
            := parse_nonterminal' (of_nonterminal nt).*)
      End wf.
    End nonterminals.
(*
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
      := parse_productions' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) 0 (reflexivity _) pats. *)
  End parts.
End correctness.
