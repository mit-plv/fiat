(** * A general [fold] over grammars *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.

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

  Definition fold_production' (fold_nt : String.string -> T)
             (its : production Char)
    := fold_right
         combine_production
         on_nil_production
         (map
            (fun it =>
               match it with
                 | Terminal ch => on_terminal ch
                 | NonTerminal nt => on_nonterminal nt (fold_nt nt)
               end)
            its).

  Lemma fold_production'_ext {f g} (ext : forall b, f b = g b) b
  : fold_production' f b = fold_production' g b.
  Proof.
    unfold fold_production'.
    induction b as [ | x ]; try reflexivity; simpl.
    destruct x; rewrite ?IHb, ?ext; reflexivity.
  Qed.

  Definition fold_productions' (fold_nt : String.string -> T)
             (its : productions Char)
    := fold_right
         combine_productions
         on_nil_productions
         (map
            (fold_production' fold_nt)
            its).

  Lemma fold_productions'_ext {f g} (ext : forall b, f b = g b) b
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
                          -> String.string -> T)
             (valid0 : nonterminals_listT)
             (nt : String.string)
  : T.
  Proof.
    refine match valid0_len with
             | 0 => on_redundant_nonterminal nt
             | S valid0_len'
               => if is_valid_nonterminal valid0 (of_nonterminal nt)
                  then fold_productions'
                         (@fold_nt valid0_len' (remove_nonterminal valid0 (of_nonterminal nt)))
                         (Lookup G nt)
                  else on_redundant_nonterminal nt
           end.
  Defined.

  Lemma fold_nt_step_ext
        {x0 x0' f g}
        (ext : forall y p b, f y p b = g y p b)
        b
  : @fold_nt_step x0 f x0' b = @fold_nt_step x0 g x0' b.
  Proof.
    unfold fold_nt_step.
    repeat match goal with
             | [ |- context[match ?x with _ => _ end] ]
               => destruct x eqn:?
             | _ => reflexivity
           end.
    apply fold_productions'_ext; eauto.
  Qed.

  Fixpoint fold_nt' initial : nonterminals_listT -> String.string -> T
    := @fold_nt_step initial (@fold_nt').

  Definition fold_nt : String.string -> T
    := let predata := @rdp_list_predata _ G in
       @fold_nt' (nonterminals_length initial_nonterminals_data) initial_nonterminals_data.

  Definition fold_production := @fold_production' (@fold_nt).

  Definition fold_productions := @fold_productions' (@fold_nt).
End general_fold.

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
        (IHf : forall nt, Pnt valid0 nt (f nt))
        pat
  : Ppat valid0 pat (fold_production' f pat).
  Proof.
    unfold fold_production'.
    induction pat; simpl.
    { apply Ppat_nil. }
    { edestruct (_ : item _).
      { apply Ppat_cons_t; trivial. }
      { apply Ppat_cons_nt; trivial. } }
  Qed.

  Lemma fold_productions'_correct
        valid0
        f
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
        (IHf : forall nt, Pnt valid0 nt (f nt))
        pats
  : Ppats valid0 pats (fold_productions' f pats).
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
                         -> String.string -> T).

    Lemma fold_nt_step_correct0
          (valid0 : nonterminals_listT)
          (Hlen : nonterminals_length valid0 <= 0)
          (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
    : forall nt,
        Pnt valid0 nt (fold_nt_step 0 fold_nt valid0 nt).
    Proof.
      assert (Hlen' : nonterminals_length valid0 = 0) by omega; clear Hlen.
      simpl; intro nt.
      apply Pnt_redundant; [ assumption | ].
      destruct (is_valid_nonterminal valid0 (of_nonterminal nt)) eqn:Hvalid; trivial.
      assert (nonterminals_length (remove_nonterminal valid0 (of_nonterminal nt)) < nonterminals_length valid0)
        by (apply remove_nonterminal_dec; assumption).
      omega.
    Qed.
  End step.

  Local Opaque rdp_list_predata.

  Lemma fold_nt'_correct
        (valid0 : nonterminals_listT)
        (valid0_len : nat)
        (Hlen : nonterminals_length valid0 <= valid0_len)
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
  : forall nt,
      Pnt valid0 nt (fold_nt' valid0_len valid0 nt).
  Proof.
    revert valid0 Hsub Hlen.
    induction valid0_len as [|valid0_len IH].
    { intros; apply fold_nt_step_correct0; assumption. }
    { simpl.
      intros valid0 Hsub Hlen nt.
      match goal with
        | [ |- context[if ?e then _ else _] ] => destruct e eqn:Hvalid
      end.
      { apply Pnt_lift; [ assumption.. | ].
        apply fold_productions'_correct.
        { apply sub_nonterminals_listT_remove_2; assumption. }
        { apply IH.
          { apply sub_nonterminals_listT_remove_2; assumption. }
          { apply Le.le_S_n.
            etransitivity; [ | exact Hlen ].
            apply (remove_nonterminal_dec valid0 (of_nonterminal nt) Hvalid). } } }
      { apply Pnt_redundant; assumption. } }
  Qed.

  Lemma fold_nt_correct
        nt
  : Pnt initial_nonterminals_data nt (fold_nt G nt).
  Proof.
    unfold fold_nt, fold_nt'.
    apply fold_nt'_correct;
    reflexivity.
  Qed.

  Lemma fold_production_correct
        pat
  : Ppat initial_nonterminals_data pat (fold_production G pat).
  Proof.
    unfold fold_production.
    apply fold_production'_correct, fold_nt_correct.
    reflexivity.
  Qed.

  Lemma fold_productions_correct
        pats
  : Ppats initial_nonterminals_data pats (fold_productions G pats).
  Proof.
    unfold fold_productions.
    apply fold_productions'_correct, fold_nt_correct.
    reflexivity.
  Qed.
End fold_correctness.
