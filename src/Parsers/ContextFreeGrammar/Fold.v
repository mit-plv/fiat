(** * A general [fold] over grammars *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Module preopt.
  Section syntax.
    Context {Char : Type}.

    Inductive item :=
    | Terminal (_ : Char -> bool)
    | NonTerminal (nt : String.string) (_ : nat).

    Definition production := list item.
    Definition productions := list production.

    Record pregrammar' :=
      { pregrammar_productions : list (String.string * productions);
        pregrammar_nonterminals := map fst pregrammar_productions;
        pregrammar_compiled_productions := map snd pregrammar_productions;
        invalid_nonterminal := Gensym.gensym pregrammar_nonterminals;
        Lookup_idx := fun n : nat => nth n (map snd pregrammar_productions) [];
        Lookup_string := list_to_productions [] pregrammar_productions;
        nonterminals_unique : NoDupR string_beq pregrammar_nonterminals }.
  End syntax.

  Global Arguments item : clear implicits.
  Global Arguments production : clear implicits.
  Global Arguments productions : clear implicits.
  Global Arguments pregrammar' : clear implicits.

  Section semantics.
    Context {Char : Type}.

    Class compile_item_data :=
      { ononterminal_names : list String.string;
        oinvalid_nonterminal : String.string }.

    Section with_cidata.
      Context {cidata : compile_item_data}.
      Definition compile_nonterminal nt
        := List.first_index_default (string_beq nt) (List.length ononterminal_names) ononterminal_names.
      Definition compile_item (expr : Core.item Char) : item Char
        := match expr with
           | Core.Terminal ch => Terminal ch
           | Core.NonTerminal nt => NonTerminal nt (compile_nonterminal nt)
           end.

      Definition compile_production (expr : Core.production Char) : production Char
        := List.map compile_item expr.

      Definition compile_productions (expr : Core.productions Char) : productions Char
        := List.map compile_production expr.
    End with_cidata.

    Section with_pregrammar.
      Context (G : PreNotations.pregrammar' Char).

      Local Instance cidata_of_pregrammar' : compile_item_data
        := { ononterminal_names := PreNotations.pregrammar_nonterminals G;
             oinvalid_nonterminal := PreNotations.invalid_nonterminal G }.

      Definition compile_pregrammar' : pregrammar' Char.
      Proof.
        refine {| pregrammar_productions := List.map (fun xy => (fst xy, @compile_productions cidata_of_pregrammar' (snd xy)))
                                                     (PreNotations.pregrammar_productions G) |}.
        abstract (rewrite map_map; exact (PreNotations.nonterminals_unique G)).
      Defined.
    End with_pregrammar.
  End semantics.

  Global Arguments compile_item_data : clear implicits.
End preopt.

Global Hint Immediate preopt.cidata_of_pregrammar' : typeclass_instances.

Module opt.
  Section syntax.
    Context {T : Type}.

    Inductive item :=
    | Terminal (_ : T)
    | NonTerminal (nt : String.string) (_ : nat).

    Definition production := list item.
    Definition productions := list production.
  End syntax.

  Global Arguments item : clear implicits.
  Global Arguments production : clear implicits.
  Global Arguments productions : clear implicits.

  Section semantics.
    Context {Char : Type} {T : Type}.

    Class compile_item_data :=
      { on_terminal : (Char -> bool) -> T }.

    Context {cidata : compile_item_data}.
    Definition compile_item (expr : preopt.item Char) : opt.item T
      := match expr with
         | preopt.Terminal ch => Terminal (on_terminal ch)
         | preopt.NonTerminal nt nt_idx => NonTerminal nt nt_idx
         end.

    Definition compile_production (expr : preopt.production Char) : opt.production T
      := List.map compile_item expr.

    Definition compile_productions (expr : preopt.productions Char) : opt.productions T
      := List.map compile_production expr.
  End semantics.

  Global Arguments compile_item_data : clear implicits.
End opt.

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
  Context `{fold_grammar_data}
          (G_orig : pregrammar' Char)
          (G : preopt.pregrammar' Char)
          (HG : preopt.compile_pregrammar' G_orig = G).

  Global Instance compile_item_data_of_fold_grammar_data : opt.compile_item_data Char T
    := {| opt.on_terminal := on_terminal |}.

  Section with_compiled_productions.
    Context (compiled_productions : list (opt.productions T))
            (Hcompiled_productions : List.map opt.compile_productions (preopt.pregrammar_compiled_productions G)
                                     = compiled_productions).

    Definition opt_Lookup_idx (n : nat) : opt.productions T
      := List.nth n compiled_productions nil.
    Lemma eq_opt_Lookup_idx n
      : opt_Lookup_idx n = opt.compile_productions (preopt.compile_productions (Lookup_idx G_orig n)).
    Proof.
      unfold opt_Lookup_idx, Lookup_idx, preopt.pregrammar_compiled_productions, preopt.pregrammar_productions, preopt.compile_pregrammar' in *; subst compiled_productions G.
      rewrite (map_map _ snd); simpl @snd; rewrite <- (map_map snd).
      change nil with (opt.compile_productions (preopt.compile_productions nil)) at 1.
      rewrite !map_nth.
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
               (predata := @rdp_list_predata _ G_orig)
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
  End with_compiled_productions.

  Definition compiled_productions : list (opt.productions T)
    := List.map opt.compile_productions (preopt.pregrammar_compiled_productions G).

  Definition fold_cnt : String.string -> default_nonterminal_carrierT -> T
    := let predata := @rdp_list_predata _ G_orig in
       @fold_cnt' compiled_productions (nonterminals_length initial_nonterminals_data) initial_nonterminals_data.
  Definition fold_nt' initial (valid0 : nonterminals_listT) (nt : String.string) : T
    := @fold_cnt' compiled_productions initial valid0 nt (preopt.compile_nonterminal nt).

  Definition fold_nt : String.string -> T
    := let predata := @rdp_list_predata _ G_orig in
       @fold_nt' (nonterminals_length initial_nonterminals_data) initial_nonterminals_data.

  Definition fold_production (pat : production Char) : T
    := @fold_production' (@fold_cnt) (opt.compile_production (preopt.compile_production pat)).

  Definition fold_productions (pats : productions Char) : T
    := @fold_productions' (@fold_cnt) (opt.compile_productions (preopt.compile_productions pats)).
End general_fold.
Global Hint Immediate compile_item_data_of_fold_grammar_data : typeclass_instances.

Global Arguments fold_grammar_data : clear implicits.

Section fold_correctness.
  Context {Char : Type} {T : Type}.
  Context {FGD : fold_grammar_data Char T}
          (G_orig : pregrammar' Char)
          (G : preopt.pregrammar' Char)
          (HG : preopt.compile_pregrammar' G_orig = G).

  Let predata := @rdp_list_predata _ G_orig.
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
                   -> Ppats (remove_nonterminal valid0 (of_nonterminal nt)) (G_orig nt) value
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
  : Ppat valid0 pat (fold_production' f (opt.compile_production (preopt.compile_production pat))).
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
  : Ppats valid0 pats (fold_productions' f (opt.compile_productions (preopt.compile_productions pats))).
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
        rewrite (eq_opt_Lookup_idx HG), <- list_to_productions_to_nonterminal by reflexivity.
        change (Lookup_string G_orig) with (Lookup G_orig); subst.
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
  : Pnt initial_nonterminals_data nt (fold_cnt G_orig G nt nt_idx).
  Proof.
    unfold fold_cnt.
    apply fold_cnt'_correct; subst; reflexivity.
  Qed.

  Lemma fold_nt'_correct
        (valid0 : nonterminals_listT)
        (valid0_len : nat)
        (Hlen : nonterminals_length valid0 <= valid0_len)
        (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
    : forall nt, Pnt valid0 nt (fold_nt' G valid0_len valid0 nt).
  Proof.
    intro nt; apply fold_cnt'_correct; auto.
  Qed.

  Lemma fold_nt_correct
        nt
  : Pnt initial_nonterminals_data nt (fold_nt G_orig G nt).
  Proof.
    unfold fold_nt.
    apply fold_nt'_correct;
    reflexivity.
  Qed.

  Lemma fold_production_correct
        pat
  : Ppat initial_nonterminals_data pat (fold_production G_orig G pat).
  Proof.
    unfold fold_production.
    apply fold_production'_correct, fold_cnt_correct.
    reflexivity.
  Qed.

  Lemma fold_productions_correct
        pats
  : Ppats initial_nonterminals_data pats (fold_productions G_orig G pats).
  Proof.
    unfold fold_productions.
    apply fold_productions'_correct, fold_cnt_correct.
    reflexivity.
  Qed.
End fold_correctness.
