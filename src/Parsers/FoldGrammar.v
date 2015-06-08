(** * A general [fold] over grammars *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.

Set Implicit Arguments.

Section general_fold.
  Context {Char : Type} {T : Type}.

  Class fold_grammar_data :=
    { on_terminal : Char -> T;
      on_redundant_nonterminal : String.string -> T;
      on_nonterminal : String.string -> T -> T;
      on_nil_production : T;
      combine_production : T -> T -> T;
      on_nil_productions : T;
      combine_productions : T -> T -> T }.
  Context `{fold_grammar_data} (G : grammar Char).

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
             (valid0 : nonterminals_listT)
             (fold_nt : forall valid, nonterminals_listT_R valid valid0
                                      -> String.string -> T)
             (nt : String.string)
  : T.
  Proof.
    refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal valid0 nt)
            then fold_productions'
                   (@fold_nt (remove_nonterminal valid0 nt) (remove_nonterminal_dec _ _ _))
                   (Lookup G nt)
            else on_redundant_nonterminal nt);
    assumption.
  Defined.

  Lemma fold_nt_step_ext
        {x0 f g}
        (ext : forall y p b, f y p b = g y p b)
        b
  : @fold_nt_step x0 f b = fold_nt_step g b.
  Proof.
    unfold fold_nt_step.
    edestruct Sumbool.sumbool_of_bool; trivial.
    apply fold_productions'_ext; eauto.
  Qed.

  Definition fold_nt' initial : String.string -> T
    := let predata := @rdp_list_predata _ G in
       @Fix _ _ ntl_wf _
            (@fold_nt_step)
            initial.

  Definition fold_nt : String.string -> T
    := @fold_nt' initial_nonterminals_data.

  Definition fold_production := @fold_production' (@fold_nt).

  Definition fold_productions := @fold_productions' (@fold_nt).
End general_fold.

Global Arguments fold_grammar_data : clear implicits.

Section fold_correctness.
  Context {Char : Type} {T : Type}.
  Context {FGD : fold_grammar_data Char T}
          (G : grammar Char).

  Class fold_grammar_correctness_computational_data :=
    { Pnt : @nonterminals_listT (@rdp_list_predata _ G) -> String.string -> T -> Type;
      Ppat : @nonterminals_listT (@rdp_list_predata _ G) -> production Char -> T -> Type;
      Ppats : @nonterminals_listT (@rdp_list_predata _ G) -> productions Char -> T -> Type }.
  Class fold_grammar_correctness_data :=
    { fgccd :> fold_grammar_correctness_computational_data;
      Pnt_lift : forall valid0 nt value,
                   sub_nonterminals_listT valid0 initial_nonterminals_data
                   -> is_valid_nonterminal valid0 nt
                   -> Ppats (remove_nonterminal valid0 nt) (G nt) value
                   -> Pnt valid0 nt value;
      Pnt_redundant : forall valid0 nt,
                        sub_nonterminals_listT valid0 initial_nonterminals_data
                        -> is_valid_nonterminal valid0 nt = false
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

  Lemma Fix_fold_nt_step_correct
        (valid0 : nonterminals_listT)
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
  : forall nt,
      Pnt valid0 nt (Fix ntl_wf _ (fold_nt_step (G:=G)) valid0 nt).
  Proof.
    induction (ntl_wf valid0) as [ ? ? IH ]; intros.
    rewrite Fix1_eq; [ | solve [ apply fold_nt_step_ext ] ].
    unfold fold_nt_step at 1; cbv beta zeta.
    match goal with
      | [ |- context[dec ?x] ] => destruct x eqn:?
    end;
      simpl;
      [ | apply Pnt_redundant; assumption ].
    let H := match goal with H : is_valid_nonterminal ?x ?nt = true |- _ => constr:H end in
    specialize (IH _ (remove_nonterminal_dec _ _ H)).
    apply Pnt_lift; trivial.
    specialize_by ltac:(rewrite sub_nonterminals_listT_remove; assumption).
    apply fold_productions'_correct; eauto.
    rewrite sub_nonterminals_listT_remove; assumption.
  Qed.

  Lemma fold_nt_correct
        nt
  : Pnt initial_nonterminals_data nt (fold_nt G nt).
  Proof.
    unfold fold_nt, fold_nt'.
    apply Fix_fold_nt_step_correct.
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
