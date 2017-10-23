Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.GenericBoolCorrectnessBaseTypes.
Require Import Fiat.Parsers.GenericRecognizer.
Require Import Fiat.Parsers.GenericRecognizerExt.
Require Import Fiat.Common.
Require Import Fiat.Common.Wf1.

Section eq.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {rdata : @parser_removal_dataT' _ G _}.
  Context {gendata gendata' : @generic_parser_dataT Char}.
  Context {genddata genddata'}
          {gendcdata : @generic_parser_decidable_correctness_data Char gendata genddata}
          {gendcdata' : @generic_parser_decidable_correctness_data Char gendata' genddata'}.
  Context (str : String).

  Local Ltac expand_once :=
    idtac;
    match goal with
    | [ |- ?f ?x = ?g ?y ]
      => let x' := head x in
         let y' := head y in
         unfold x', y'
    end.

  Local Ltac t' :=
    idtac;
    match goal with
    | [ |- ?R ?x ?x ] => reflexivity
    | _ => assumption
    | [ |- ?f match ?x with _ => _ end = ?g match ?x with _ => _ end ]
      => destruct x eqn:?
    | _ => progress subst
    | _ => progress autorewrite with generic_parser_decidable_correctness
    | _ => progress simpl in *
    | _ => solve [ auto with nocore ]
    | _ => intro
    | _ => rewrite List.map_map
    | [ |- andb _ _ = andb _ _ ] => apply (f_equal2 andb)
    | [ |- List.fold_right orb false _ = List.fold_right orb false _ ]
      => apply (f_equal (List.fold_right orb false))
    | [ |- List.map ?f ?ls = List.map ?g ?ls ] => apply List.map_ext
    | [ |- ?f (option_rect _ _ _ (sumbool_rect _ _ _ ?x))
           = ?g (option_rect _ _ _ (sumbool_rect _ _ _ ?x)) ]
      => destruct x eqn:?
    end.

  Local Ltac t tac := intros; expand_once; repeat first [ progress t' | progress tac ].

  Lemma parse_item'_eq
        str_matches_nonterminal str_matches_nonterminal'
        (str_matches_nonterminal_eq : forall nt,
            parse_nt_T_to_bool (gendata := gendata) (str_matches_nonterminal nt)
            = parse_nt_T_to_bool (gendata := gendata') (str_matches_nonterminal' nt))
        (offset : nat) (len : nat)
        (it : item Char)
    : parse_item_T_to_bool (parse_item' (gendata := gendata) str str_matches_nonterminal offset len it)
      = parse_item_T_to_bool (parse_item' (gendata := gendata') str str_matches_nonterminal' offset len it).
  Proof. t I. Qed.

  Section production.
    Context {len0 : nat}
            (parse_nonterminal
             : forall (offset : nat) (len0_minus_len : nat),
                nonterminal_carrierT
                -> _)
            (parse_nonterminal'
             : forall (offset : nat) (len0_minus_len : nat),
                nonterminal_carrierT
                -> _)
            (parse_nonterminal_eq
             : forall offset len0_minus_len nt,
                parse_nt_T_to_bool (gendata := gendata) (parse_nonterminal offset len0_minus_len nt)
                = parse_nt_T_to_bool (gendata := gendata') (parse_nonterminal' offset len0_minus_len nt)).

    Lemma parse_production'_for_eq
          (splits : production_carrierT -> String -> nat -> nat -> list nat)
          (offset : nat)
          (len0_minus_len : nat)
          (prod_idx : production_carrierT)
      : parse_production_T_to_bool (parse_production'_for (len0 := len0) str parse_nonterminal splits offset len0_minus_len prod_idx)
        = parse_production_T_to_bool (parse_production'_for (len0 := len0) str parse_nonterminal' splits offset len0_minus_len prod_idx).
    Proof.
      t I.
      repeat match goal with
             | [ |- context[list_rect ?P ?N ?C] ]
               => not is_var C;
                    let P' := fresh "P'" in
                    let N' := fresh "N'" in
                    let C' := fresh "C'" in
                    set (P' := P);
                      set (N' := N);
                      set (C' := C)
             end.
      generalize (to_production prod_idx); intro ps.
      revert prod_idx offset len0_minus_len.
      induction ps as [|p ps IHps].
      { simpl; t I. }
      { simpl; t ltac:(apply parse_item'_eq). }
    Qed.

    Lemma parse_production'_eq
          (offset : nat)
          (len0_minus_len : nat)
          (prod_idx : production_carrierT)
      : parse_production_T_to_bool (parse_production' (len0 := len0) str parse_nonterminal offset len0_minus_len prod_idx)
        = parse_production_T_to_bool (parse_production' (len0 := len0) str parse_nonterminal' offset len0_minus_len prod_idx).
    Proof. t ltac:(apply parse_production'_for_eq). Qed.
  End production.

  Section productions.
    Context {len0 : nat}
            (parse_nonterminal
             : forall (offset : nat)
                      (len0_minus_len : nat),
                nonterminal_carrierT -> _)
            (parse_nonterminal'
             : forall (offset : nat)
                      (len0_minus_len : nat),
                nonterminal_carrierT -> _)
            (parse_nonterminal_eq
             : forall offset len0_minus_len nt,
                parse_nt_T_to_bool (gendata := gendata) (parse_nonterminal offset len0_minus_len nt)
                = parse_nt_T_to_bool (gendata := gendata') (parse_nonterminal' offset len0_minus_len nt)).

    Lemma parse_productions'_eq
          (offset : nat)
          (len0_minus_len : nat)
          (prods : list production_carrierT)
      : parse_productions_T_to_bool (parse_productions' (len0 := len0) str parse_nonterminal offset len0_minus_len prods)
        = parse_productions_T_to_bool (parse_productions' (len0 := len0) str parse_nonterminal' offset len0_minus_len prods).
    Proof. t ltac:(apply parse_production'_eq). Qed.
  End productions.

  Section nonterminals.
    Section step.
      Context {len0 valid_len}
              (parse_nonterminal
               : forall (p : nat * nat),
                  Wf.prod_relation lt lt p (len0, valid_len)
                  -> forall (valid : nonterminals_listT)
                            (offset : nat) (len : nat),
                    len <= fst p -> nonterminal_carrierT -> _)
              (parse_nonterminal'
               : forall (p : nat * nat),
                  Wf.prod_relation lt lt p (len0, valid_len)
                  -> forall (valid : nonterminals_listT)
                            (offset : nat) (len : nat),
                    len <= fst p -> nonterminal_carrierT -> _)
              (parse_nonterminal_eq
               : forall (p : nat * nat)
                        (pf : Wf.prod_relation lt lt p (len0, valid_len))
                        (valid : nonterminals_listT)
                        (offset : nat) (len : nat)
                        (pf' : len <= fst p)
                        (nt : nonterminal_carrierT),
                  parse_nt_T_to_bool (gendata := gendata) (parse_nonterminal p pf valid offset len pf' nt)
                  = parse_nt_T_to_bool (gendata := gendata') (parse_nonterminal' p pf valid offset len pf' nt)).
      Local Unset Keyed Unification.
      Lemma parse_nonterminal_step_eq
            (valid : nonterminals_listT)
            (offset : nat)
            (len : nat)
            (pf : len <= len0)
            (nt : nonterminal_carrierT)
        : parse_nt_T_to_bool (parse_nonterminal_step str parse_nonterminal valid offset pf nt)
          = parse_nt_T_to_bool (parse_nonterminal_step str parse_nonterminal' valid offset pf nt).
      Proof. t ltac:(apply parse_productions'_eq). Qed.
    End step.

    Section wf.
      Lemma parse_nonterminal_or_abort_eq
      : forall (p : nat * nat)
               (valid : nonterminals_listT)
               (offset : nat) (len : nat)
               (pf : len <= fst p)
               (nt : nonterminal_carrierT),
        parse_nt_T_to_bool (parse_nonterminal_or_abort (gendata := gendata) str p valid offset pf nt)
        = parse_nt_T_to_bool (parse_nonterminal_or_abort (gendata := gendata') str p valid offset pf nt).
      Proof.
        t I.
        lazymatch goal with
        | [ |- ?f0 (Fix ?rwf ?P ?F ?x ?a ?b ?c ?d ?e)
               = ?f1 (Fix ?rwf ?Q ?G ?x ?a ?b ?c ?d ?e) ]
          => revert a b c d e;
               induction (rwf x);
               intros;
               rewrite !Wf1.Fix5_eq
                 by (intros; apply parse_nonterminal_step_ext; trivial)
        end.
        apply parse_nonterminal_step_eq.
        auto with nocore.
      Qed.

      Lemma parse_nonterminal_or_abort_minus_eq
      : forall (p : nat * nat)
               (valid : nonterminals_listT)
               (offset : nat) (len0_minus_len : nat)
               (nt : nonterminal_carrierT),
        parse_nt_T_to_bool (parse_nonterminal_or_abort_minus (gendata := gendata) str p valid offset len0_minus_len nt)
        = parse_nt_T_to_bool (parse_nonterminal_or_abort_minus (gendata := gendata') str p valid offset len0_minus_len nt).
      Proof.
        intros; apply parse_nonterminal_or_abort_eq.
      Qed.

      Definition parse_nonterminal'_eq
                 (nt : nonterminal_carrierT)
        : parse_nt_T_to_bool (parse_nonterminal' (gendata := gendata) str nt)
          = parse_nt_T_to_bool (parse_nonterminal' (gendata := gendata') str nt).
      Proof. t ltac:(apply parse_nonterminal_or_abort_eq). Qed.

      Definition parse_nonterminal_eq
                 (nt : String.string)
        : parse_nt_T_to_bool (parse_nonterminal (gendata := gendata) str nt)
          = parse_nt_T_to_bool (parse_nonterminal (gendata := gendata') str nt).
      Proof. t ltac:(apply parse_nonterminal'_eq). Qed.
    End wf.
  End nonterminals.

  Definition parse_item_eq
             (it : item Char)
    : parse_item_T_to_bool (parse_item (gendata := gendata) str it)
      = parse_item_T_to_bool (parse_item (gendata := gendata') str it)
    := parse_item'_eq _ _ parse_nonterminal'_eq _ _ _.

  Definition parse_production_eq
             (pat : production_carrierT)
    : parse_production_T_to_bool (parse_production (gendata := gendata) str pat)
      = parse_production_T_to_bool (parse_production (gendata := gendata') str pat)
    := parse_production'_eq _ _ (parse_nonterminal_or_abort_minus_eq _ _) _ _ _.

  Definition parse_productions_eq
             (pats : list production_carrierT)
    : parse_productions_T_to_bool (parse_productions (gendata := gendata) str pats)
      = parse_productions_T_to_bool (parse_productions (gendata := gendata') str pats)
    := parse_productions'_eq _ _ (parse_nonterminal_or_abort_minus_eq _ _) _ _ _.
End eq.
