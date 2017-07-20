(** * A general [fold] over grammars *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Common.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.OptionFacts.

Set Implicit Arguments.

Section general_fold.
  Context {Char : Type} {T : Type}.

  Class fold_grammar_data :=
    { on_terminal : (Char -> bool) -> T;
      on_redundant_nonterminal : String.string -> T;
      on_nonterminal : String.string -> T -> T;
      on_nil_production : T;
      combine_production : T -> T -> T;
      on_nil_productions : T;
      combine_productions : T -> T -> T }.
  Context `{fold_grammar_data} (G : pregrammar' Char).

  Global Instance compile_item_data_of_fold_grammar_data : opt.compile_item_data Char T
    := {| opt.on_terminal := on_terminal;
          opt.nonterminal_names := pregrammar_nonterminals G;
          opt.invalid_nonterminal := Gensym.gensym (pregrammar_nonterminals G) |}.

  Section with_compiled_productions.
    Context (compiled_productions : list (opt.productions T))
            (Hcompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions).

    Definition opt_Lookup_idx (n : nat) : opt.productions T
      := List.nth n compiled_productions nil.
    Lemma eq_opt_Lookup_idx n
      : opt_Lookup_idx n = opt.compile_productions (Lookup_idx G n).
    Proof.
      unfold opt_Lookup_idx, Lookup_idx; subst compiled_productions.
      change nil with (opt.compile_productions nil) at 1.
      rewrite map_nth.
      reflexivity.
    Qed.

    Definition fold_production' (fold_nt : String.string -> default_nonterminal_carrierT -> T)
               (its : opt.production T)
      := fold_right
           combine_production
           on_nil_production
           (map
              (fun it =>
                 match it with
                 | opt.Terminal ch => ch
                 | opt.NonTerminal nt nt_idx => on_nonterminal nt (fold_nt nt nt_idx)
                 end)
              its).

    Lemma fold_production'_ext {f g} (ext : forall b b', f b b' = g b b') b
      : fold_production' f b = fold_production' g b.
    Proof.
      unfold fold_production'.
      induction b as [ | x ]; try reflexivity; simpl.
      destruct x; rewrite ?IHb, ?ext; reflexivity.
    Qed.

    Definition fold_productions' (fold_nt : String.string -> default_nonterminal_carrierT -> T)
               (its : opt.productions T)
      := fold_right
           combine_productions
           on_nil_productions
           (map
              (fold_production' fold_nt)
              its).

    Lemma fold_productions'_ext {f g} (ext : forall b b', f b b' = g b b') b
      : fold_productions' f b = fold_productions' g b.
    Proof.
      unfold fold_productions'.
      induction b as [ | x ]; try reflexivity; simpl.
      rewrite IHb, (fold_production'_ext ext); reflexivity.
    Qed.

    Definition fold_nt_step
               (predata := @rdp_list_predata _ G)
               (valid0_len : nat)
               (fold_nt : forall valid_len : nat,
                   nonterminals_listT
                   -> String.string -> default_nonterminal_carrierT -> T)
               (valid0 : nonterminals_listT)
               (nt : String.string)
               (nt_idx : default_nonterminal_carrierT)
      : T.
    Proof.
      refine match valid0_len with
             | 0 => on_redundant_nonterminal nt
             | S valid0_len'
               => if is_valid_nonterminal valid0 nt_idx
                  then fold_productions'
                         (@fold_nt valid0_len' (remove_nonterminal valid0 nt_idx))
                         (opt_Lookup_idx nt_idx)
                  else on_redundant_nonterminal nt
             end.
    Defined.

    Lemma fold_nt_step_ext
          {x0 x0' f g}
          (ext : forall y p b b', f y p b b' = g y p b b')
          b b'
      : @fold_nt_step x0 f x0' b b' = @fold_nt_step x0 g x0' b b'.
    Proof.
      unfold fold_nt_step.
      repeat match goal with
             | [ |- context[match ?x with _ => _ end] ]
               => destruct x eqn:?
             | _ => reflexivity
             end.
      apply fold_productions'_ext; eauto.
    Qed.

    Fixpoint fold_cnt' initial : nonterminals_listT -> String.string -> default_nonterminal_carrierT -> T
      := @fold_nt_step initial (@fold_cnt').

    Lemma unfold_fold_cnt' initial
      : @fold_cnt' initial = @fold_nt_step initial (@fold_cnt').
    Proof. destruct initial; reflexivity. Qed.

    Definition fold_cnt : String.string -> default_nonterminal_carrierT -> T
      := let predata := @rdp_list_predata _ G in
         @fold_cnt' (nonterminals_length initial_nonterminals_data) initial_nonterminals_data.
    Definition fold_nt' initial (valid0 : nonterminals_listT) (nt : String.string) : T
      := @fold_cnt' initial valid0 nt (opt.compile_nonterminal nt).

    Definition fold_nt : String.string -> T
      := let predata := @rdp_list_predata _ G in
         @fold_nt' (nonterminals_length initial_nonterminals_data) initial_nonterminals_data.

    Definition fold_production (pat : production Char) : T
      := @fold_production' (@fold_cnt) (opt.compile_production pat).

    Definition fold_productions (pats : productions Char) : T
      := @fold_productions' (@fold_cnt) (opt.compile_productions pats).
  End with_compiled_productions.

  Definition compiled_productions : list (opt.productions T)
    := List.map opt.compile_productions (List.map snd (pregrammar_productions G)).
End general_fold.
Global Hint Immediate compile_item_data_of_fold_grammar_data : typeclass_instances.

Global Arguments fold_grammar_data : clear implicits.

Section fold_correctness.
  Context {Char : Type} {T : Type}.
  Context {FGD : fold_grammar_data Char T}
          (G : pregrammar' Char).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Class fold_grammar_correctness_computational_data :=
    { Pnt : nonterminals_listT -> String.string -> T -> Type;
      Ppat : nonterminals_listT -> production Char -> T -> Type;
      Ppats : nonterminals_listT -> productions Char -> T -> Type }.
  Class fold_grammar_correctness_data :=
    { fgccd :> fold_grammar_correctness_computational_data;
      Pnt_lift : forall valid0 nt value,
                   sub_nonterminals_listT valid0 initial_nonterminals_data
                   -> is_valid_nonterminal valid0 (of_nonterminal nt)
                   -> Ppats (remove_nonterminal valid0 (of_nonterminal nt)) (G nt) value
                   -> Pnt valid0 nt value;
      Pnt_redundant : forall valid0 nt,
                        sub_nonterminals_listT valid0 initial_nonterminals_data
                        -> is_valid_nonterminal valid0 (of_nonterminal nt) = false
                        -> Pnt valid0 nt (on_redundant_nonterminal nt);
      Ppat_nil : forall valid0, Ppat valid0 nil on_nil_production;
      Ppat_cons_nt : forall valid0 nt xs p ps,
                       sub_nonterminals_listT valid0 initial_nonterminals_data
                       -> Pnt valid0 nt p
                       -> Ppat valid0 xs ps
                       -> Ppat valid0
                               (NonTerminal nt::xs)
                               (combine_production (on_nonterminal nt p) ps);
      Ppat_cons_t : forall valid0 ch xs ps,
                      sub_nonterminals_listT valid0 initial_nonterminals_data
                      -> Ppat valid0 xs ps
                      -> Ppat valid0
                              (Terminal ch::xs)
                              (combine_production (on_terminal ch) ps);
      Ppats_nil : forall valid0, Ppats valid0 nil on_nil_productions;
      Ppats_cons : forall valid0 x xs p ps,
                     sub_nonterminals_listT valid0 initial_nonterminals_data
                     -> Ppat valid0 x p
                     -> Ppats valid0 xs ps
                     -> Ppats valid0 (x::xs) (combine_productions p ps) }.
  Context {FGCD : fold_grammar_correctness_data}.

  Lemma fold_production'_correct
        valid0
        f
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
        (IHf : forall nt nt_idx, of_nonterminal nt = nt_idx -> Pnt valid0 nt (f nt nt_idx))
        pat
  : Ppat valid0 pat (fold_production' f (opt.compile_production pat)).
  Proof.
    unfold fold_production'.
    induction pat; simpl.
    { apply Ppat_nil. }
    { edestruct (_ : item _).
      { apply Ppat_cons_t; trivial. }
      { apply Ppat_cons_nt; eauto. } }
  Qed.

  Lemma fold_productions'_correct
        valid0
        f
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
        (IHf : forall nt nt_idx, of_nonterminal nt = nt_idx -> Pnt valid0 nt (f nt nt_idx))
        pats
  : Ppats valid0 pats (fold_productions' f (opt.compile_productions pats)).
  Proof.
    unfold fold_productions'.
    induction pats as [ | x xs IHxs ]; intros.
    { simpl; apply Ppats_nil. }
    { simpl; apply Ppats_cons; trivial; [].
      { apply fold_production'_correct; trivial. } }
  Qed.

  Section step.
    Context (fold_nt : forall valid_len : nat,
                         nonterminals_listT
                         -> String.string -> default_nonterminal_carrierT -> T).

    Lemma fold_nt_step_correct0
          (valid0 : nonterminals_listT)
          (Hlen : nonterminals_length valid0 <= 0)
          (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
      : forall nt nt_idx,
        of_nonterminal nt = nt_idx
        -> Pnt valid0 nt (fold_nt_step (compiled_productions G) 0 fold_nt valid0 nt nt_idx).
    Proof.
      assert (Hlen' : nonterminals_length valid0 = 0) by omega; clear Hlen.
      simpl; intros nt nt_idx Hnt.
      apply Pnt_redundant; [ assumption | ].
      destruct (is_valid_nonterminal valid0 (of_nonterminal nt)) eqn:Hvalid; trivial.
      assert (nonterminals_length (remove_nonterminal valid0 (of_nonterminal nt)) < nonterminals_length valid0)
        by (apply remove_nonterminal_dec; assumption).
      omega.
    Qed.
  End step.

  Local Opaque rdp_list_predata.

  Lemma fold_cnt'_correct
        (valid0 : nonterminals_listT)
        (valid0_len : nat)
        (Hlen : nonterminals_length valid0 <= valid0_len)
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
    : forall nt nt_idx,
      of_nonterminal nt = nt_idx
      -> Pnt valid0 nt (fold_cnt' (compiled_productions G) valid0_len valid0 nt nt_idx).
  Proof.
    revert valid0 Hsub Hlen.
    induction valid0_len as [|valid0_len IH].
    { intros; apply fold_nt_step_correct0; assumption. }
    { simpl.
      intros valid0 Hsub Hlen nt nt_idx Hnt.
      match goal with
        | [ |- context[if ?e then _ else _] ] => destruct e eqn:Hvalid
      end.
      { apply Pnt_lift; [ subst; assumption.. | ].
        rewrite (eq_opt_Lookup_idx G), <- list_to_productions_to_nonterminal by reflexivity.
        change (Lookup_string G) with (Lookup G); subst.
        change default_to_nonterminal with to_nonterminal.
        rewrite to_of_nonterminal
          by (apply initial_nonterminals_correct, Hsub; assumption).
        apply fold_productions'_correct.
        { apply sub_nonterminals_listT_remove_2; assumption. }
        { apply IH.
          { apply sub_nonterminals_listT_remove_2; assumption. }
          { apply Le.le_S_n.
            etransitivity; [ | exact Hlen ].
            apply (remove_nonterminal_dec valid0 (of_nonterminal nt) Hvalid). } } }
      { apply Pnt_redundant; subst; assumption. } }
  Qed.

  Lemma fold_cnt_correct
        nt nt_idx
        (Hnt : of_nonterminal nt = nt_idx)
  : Pnt initial_nonterminals_data nt (fold_cnt G (compiled_productions G) nt nt_idx).
  Proof.
    unfold fold_cnt.
    apply fold_cnt'_correct; subst; reflexivity.
  Qed.

  Lemma fold_nt'_correct
        (valid0 : nonterminals_listT)
        (valid0_len : nat)
        (Hlen : nonterminals_length valid0 <= valid0_len)
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
    : forall nt, Pnt valid0 nt (fold_nt' (compiled_productions G) valid0_len valid0 nt).
  Proof.
    intro nt; apply fold_cnt'_correct; auto.
  Qed.

  Lemma fold_nt_correct
        nt
  : Pnt initial_nonterminals_data nt (fold_nt G (compiled_productions G) nt).
  Proof.
    unfold fold_nt.
    apply fold_nt'_correct;
    reflexivity.
  Qed.

  Lemma fold_production_correct
        pat
  : Ppat initial_nonterminals_data pat (fold_production G (compiled_productions G) pat).
  Proof.
    unfold fold_production.
    apply fold_production'_correct, fold_cnt_correct.
    reflexivity.
  Qed.

  Lemma fold_productions_correct
        pats
  : Ppats initial_nonterminals_data pats (fold_productions G (compiled_productions G) pats).
  Proof.
    unfold fold_productions.
    apply fold_productions'_correct, fold_cnt_correct.
    reflexivity.
  Qed.
End fold_correctness.

Module compile.
  Section semantics.
    Context {Char : Type} {T : Type}.
    Context `{@fold_grammar_data Char T} (G : pregrammar' Char).

    Local Notation productions_def precompiled_productions
      := (List.map (fun nt_idx_nt => fold_cnt G precompiled_productions (snd nt_idx_nt) (fst nt_idx_nt)) (enumerate (List.map fst (pregrammar_productions G)) 0)).

    Definition productions : list T
      := productions_def (compiled_productions G).

    Section with_compiled_productions.
      Context (precompiled_productions : list (opt.productions T))
              (Hprecompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = precompiled_productions).
      Context (compiled_productions : list T)
              (Hcompiled_productions : productions_def precompiled_productions = compiled_productions).

      Definition fold_cnt : String.string -> default_nonterminal_carrierT -> T
        := fun nt nt_idx => List.nth nt_idx compiled_productions (on_redundant_nonterminal nt).
      Definition fold_nt : String.string -> T
        := fun nt => fold_cnt nt (opt.compile_nonterminal nt).
      Definition fold_production (pat : Core.production Char) : T
        := fold_production' fold_cnt (opt.compile_production pat).
      Definition fold_productions (pats : Core.productions Char) : T
        := fold_productions' fold_cnt (opt.compile_productions pats).
    End with_compiled_productions.

  End semantics.

  Section fold_correctness.
    Context {Char : Type} {T : Type}.
    Context {FGD : fold_grammar_data Char T}
            (G : pregrammar' Char)
            {FGCD : fold_grammar_correctness_data G}.

    Let predata := @rdp_list_predata _ G.
    Local Existing Instance predata.

    Lemma fold_cnt_correct
          nt nt_idx
          (Hnt : of_nonterminal nt = nt_idx)
      : Pnt initial_nonterminals_data nt (fold_cnt (productions G) nt nt_idx).
    Proof.
      unfold fold_cnt, productions.
      repeat match goal with
             | _ => progress subst
             | _ => rewrite ListFacts.nth_error_nth
             | _ => progress unfold option_map in *
             | _ => progress break_innermost_match_step
             | _ => progress break_innermost_match_hyps_step
             | _ => progress inversion_option
             | _ => progress destruct_head' sig
             | _ => progress destruct_head' and
             | _ => progress cbn [fst snd plus] in *
             | [ H : nth_error (map _ _) _ = Some _ |- _ ] => apply ListFacts.nth_error_map'_strong in H
             | [ H : nth_error (enumerate _ _) _ = _ |- _ ]
               => rewrite ListFacts.nth_error_enumerate in H
             | [ H : nth_error (map ?f ?ls) ?idx = None |- _ ]
               => let H' := fresh in
                  destruct (nth_error ls idx) eqn:H';
                    [ eapply map_nth_error in H'; rewrite H in H'; congruence
                    | clear H ]
             end.
      { match goal with
        | [ H : nth_error _ (of_nonterminal ?nt) = Some ?x |- _ ]
          => assert (fst x = nt);
               [ pose proof H as H'; rewrite nth_error_default_to_nonterminal in H'
               | subst nt ]
        end.
        { break_innermost_match_hyps; try congruence; inversion_option; subst.
          cbn [fst].
          change default_to_nonterminal with (rdp_list_to_nonterminal (G:=G)).
          unfold of_nonterminal, predata, rdp_list_predata.
          rewrite rdp_list_to_of_nonterminal; [ reflexivity | ].
          apply initial_nonterminals_correct, rdp_list_is_valid_nonterminal_nth_error.
          congruence. }
        { apply fold_cnt_correct; reflexivity. } }
      { apply Pnt_redundant; [ reflexivity | ].
        match goal with |- ?x = false => destruct x eqn:Hb end;
          [ | reflexivity ].
        exfalso.
        eapply rdp_list_is_valid_nonterminal_nth_error; try eassumption; assumption. }
    Qed.

    Lemma fold_nt_correct nt
      : Pnt initial_nonterminals_data nt (fold_nt G (productions G) nt).
    Proof. unfold fold_nt; apply fold_cnt_correct; reflexivity. Qed.

    Lemma fold_production_correct pat
      : Ppat initial_nonterminals_data pat (fold_production G (productions G) pat).
    Proof.
      unfold fold_production.
      apply fold_production'_correct; [ reflexivity | apply fold_cnt_correct ].
    Qed.

    Lemma fold_productions_correct pats
      : Ppats initial_nonterminals_data pats (fold_productions G (productions G) pats).
    Proof.
      unfold fold_productions.
      apply fold_productions'_correct; [ reflexivity | apply fold_cnt_correct ].
    Qed.
  End fold_correctness.
End compile.
