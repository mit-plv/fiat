(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalanced.MinimalOfCore.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          {predata : parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}.

  Fixpoint paren_balanced_pb_parse_of_production_empty
           {valid0 pat level}
           (str : String) (Hlen : length str = 0) (p : parse_of_production G str pat)
           (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p)
           (Hp : pb'_production G valid0 level pat)
           {struct p}
  : level = 0 /\ paren_balanced' str level = true.
  Proof.
    destruct p as [ | ??? p0 p1 ]; simpl in *.
    { rewrite paren_balanced'_nil by assumption.
      inversion Hp; subst; simpl.
      repeat constructor. }
    { specialize (fun Hlen level => paren_balanced_pb_parse_of_production_empty valid0 _ level _ Hlen p1 (snd Hforall)).
      specialize_by ltac:(rewrite drop_length; omega).
      dependent destruction p0;
        inversion Hp; subst; clear Hp.
      { exfalso.
        match goal with
          | [ H : is_true (take _ _ ~= [ _ ]) |- _ ]
            => generalize (length_singleton _ _ H)
        end.
        rewrite take_length, Hlen.
        apply Min.min_case_strong; intros; omega. }
      { assert (H' : drop n str =s str) by (apply drop_empty; assumption).
        rewrite <- H'.
        apply paren_balanced_pb_parse_of_production_empty; assumption. } }
  Qed.

  Fixpoint paren_balanced_pb_parse_of_productions
             {valid0 pats}
             (str : String) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p)
             (Hp : pb'_productions G valid0 pats)
             {struct Hp}
  : paren_balanced' str 0 = true
  with paren_balanced_pb_parse_of_production
         {valid0 pat level}
         (str : String) (p : parse_of_production G str pat)
         (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p)
         (Hp : pb'_production G valid0 level pat)
         {struct Hp}
       : paren_balanced' str level = true.
  Proof.
    { destruct Hp as [|??? Hp0 Hp1].
      { inversion p. }
      { specialize (fun str p H => paren_balanced_pb_parse_of_production _ _ _ str p H Hp0).
        specialize (fun str p H => paren_balanced_pb_parse_of_productions _ _ str p H Hp1).
        dependent destruction p; eauto with nocore. } }
    { destruct Hp as [|???? Hp0 Hp1|Hp].
      { inversion p.
        rewrite paren_balanced'_nil by assumption.
        reflexivity. }
      { dependent destruction p.
        let p1 := match goal with p1 : parse_of_production _ _ _ |- _ => constr:p1 end in
        specialize (fun level => paren_balanced_pb_parse_of_production _ _ level _ p1 (snd Hforall)).
        let p0 := match goal with p0 : parse_of_item _ _ _ |- _ => constr:p0 end in
        let p := fresh in
        rename p0 into p;
          dependent destruction p.
        let p0 := match goal with p0 : parse_of _ _ _ |- _ => constr:p0 end in
        specialize (paren_balanced_pb_parse_of_productions _ _ _ p0 (snd (fst Hforall))).
        evar (lv : nat).
        specialize (paren_balanced_pb_parse_of_production lv); subst lv.
        specialize_by eassumption.
        admit. }
      {
clear paren_balanced_pb_parse_of_productions.
        dependent destruction p.

        match goal with
          | [ H : is_true (take _ _ ~= [ _ ]) |- _ ]
            => generalize (length_singleton _ _ H);
              pose proof (take_n_1_singleton _ _ _ H)
        end.
          rewrite paren_balanced'_recr.
          erewrite (proj1 (get_0 _ _)) by eassumption.
          rewrite take_length.
          unfold paren_balanced'_step, pb_check_level, pb_new_level in *.
          apply Min.min_case_strong;
            repeat match goal with
                     | _ => progress subst
                     | _ => progress intros
                     | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                     | [ H : is_true ?x |- context[?x] ] => rewrite H
                     | _ => progress simpl in *
                     | _ => solve [ eauto with nocore ]
                     | [ n : nat, str : _ |- _ ]
                       => let H' := fresh in
                          assert (H' : drop 1 str =s drop n str)
                            by (apply bool_eq_empty; rewrite drop_length; omega);
                            rewrite H';
                            solve [ eauto with nocore ]
                   end. }
        {

          replace (drop 1 str) with (drop n str).
          Focus 2.
          rewrite <- (drop_empty (str := drop 1 str) (n := n)).


                     | _ => rewrite paren_balanced'_nil by (rewrite drop_length; omega)
                   end.

            .
              erewrite paren_balanced_pb_parse_of_production by assumption;
              rewrite ?Bool.andb_true_r;
              trivial. }
          { rewriteg
            reflexivity.
            reflexivity.
            SearchAbout (_ && true)%bool.

              3:assumption.
              2:exact (snd Hforall).
            Focus 3.
            3:assumption.

          end.

        { admit; apply (fun k => @paren_balanced_pb_parse_of_item' paren_balanced_pb_parse_of_productions valid0 _ _ k _ (fst Hforall));
          rewrite take_length, Hlen, Min.min_0_r; reflexivity. }
        { pose proof (@paren_balanced_pb_parse_of_production valid0).
; [ | eassumption ]. x y k). _ (snd Hforall)).
          rewrite drop_length, Hlen; reflexivity. } } }
  Defined.



  Definition paren_balanced_pb_parse_of_item'
             (paren_balanced_pb_parse_of_productions
              : forall valid0 pats
                       (str : String) (Hlen : length str = 0) (p : parse_of G str pats)
                       (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p),
                  pb_productions G valid0 pats)
             {valid0 it}
             (str : String) (Hlen : length str = 0) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p)
  : pb_item G valid0 it.
  Proof.
    destruct p as [ | nt p ].
    { exfalso.
      erewrite length_singleton in Hlen by eassumption; omega. }
    { specialize (paren_balanced_pb_parse_of_productions valid0 (G nt) str Hlen p (snd Hforall)).
      constructor; simpl in *; [ exact (fst Hforall) | assumption ]. }
  Defined.

  Fixpoint paren_balanced_pb_parse_of_productions
             {valid0 pats}
             (str : String) (Hlen : length str = 0) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p)
             {struct p}
  : pb_productions G valid0 pats
  with paren_balanced_pb_parse_of_production
         {valid0 pat}
         (str : String) (Hlen : length str = 0) (p : parse_of_production G str pat)
         (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p)
         {struct p}
       : pb_production G valid0 pat.
  Proof.
    { destruct p as [ ?? p | ?? p ]; simpl in *.
      { pose proof (paren_balanced_pb_parse_of_production valid0 _ _ Hlen p Hforall).
        left; assumption. }
      { pose proof (paren_balanced_pb_parse_of_productions valid0 _ _ Hlen p Hforall).
        right; assumption. } }
    { destruct p as [ | ?? p ]; simpl in *.
      { constructor. }
      { constructor.
        { apply (fun k => @paren_balanced_pb_parse_of_item' paren_balanced_pb_parse_of_productions valid0 _ _ k _ (fst Hforall)).
          rewrite take_length, Hlen, Min.min_0_r; reflexivity. }
        { apply (fun k => @paren_balanced_pb_parse_of_production valid0 _ _ k _ (snd Hforall)).
          rewrite drop_length, Hlen; reflexivity. } } }
  Defined.

  Definition paren_balanced_pb_parse_of_item
             {valid0 it}
             (str : String) (Hlen : length str = 0) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p)
  : pb_item G valid0 it
    := @paren_balanced_pb_parse_of_item' (@paren_balanced_pb_parse_of_productions) valid0 it str Hlen p Hforall.

  Definition paren_balanced_minimal_pb_parse_of_item
             {valid0 it}
             (str : String) (Hlen : length str = 0) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p)
  : minimal_pb_item (G := G) valid0 it.
  Proof.
    eapply minimal_pb_item__of__pb_item.
    eapply paren_balanced_pb_parse_of_item; eassumption.
  Qed.

  Definition paren_balanced_minimal_pb_parse_of_production
             {valid0 pat}
             (str : String) (Hlen : length str = 0) (p : parse_of_production G str pat)
             (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p)
  : minimal_pb_production (G := G) valid0 pat.
  Proof.
    eapply minimal_pb_production__of__pb_production.
    eapply paren_balanced_pb_parse_of_production; eassumption.
  Qed.

  Definition paren_balanced_minimal_pb_parse_of_productions
             {valid0 pats}
             (str : String) (Hlen : length str = 0) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p)
  : minimal_pb_productions (G := G) valid0 pats.
  Proof.
    eapply minimal_pb_productions__of__pb_productions.
    eapply paren_balanced_pb_parse_of_productions; eassumption.
  Qed.*)

  Fixpoint parse_hiding_from_pb_parse_of_productions
             {valid0 pats}
             (str : String) (Hlen : length str = 0)
             (p : pb_productions G valid0 pats)
             {struct p}
  : { p : parse_of G str pats
          & Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p }
  with paren_balanced_from_pb_parse_of_production
         {valid0 pat}
         (str : String) (Hlen : length str = 0)
         (p: pb_production G valid0 pat)
         {struct p}
       : { p : parse_of_production G str pat
               & Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p }.
  Proof.
    { destruct p as [ ?? p | ?? p ]; simpl in *.
      { pose proof (paren_balanced_from_pb_parse_of_production valid0 _ _ Hlen p) as p'.
        eexists (ParseHead _ (projT1 p')).
        exact (projT2 p'). }
      { pose proof (paren_balanced_from_pb_parse_of_productions valid0 _ _ Hlen p) as p'.
        eexists (ParseTail _ (projT1 p')).
        exact (projT2 p'). } }
    { destruct p as [ | ?? p0 p1 ]; simpl in *.
      { exists (ParseProductionNil G _ Hlen). constructor. }
      { eapply (@paren_balanced_from_pb_parse_of_item' paren_balanced_from_pb_parse_of_productions) in p0.
        eapply (@paren_balanced_from_pb_parse_of_production) in p1.
        { eexists (ParseProductionCons _ 0 (projT1 p0) (projT1 p1)).
          exact (projT2 p0, projT2 p1). }
        { rewrite ?take_length, ?drop_length, Hlen; reflexivity. }
        { rewrite ?take_length, ?drop_length, Hlen, Min.min_0_r; reflexivity. } } }
  Defined.

  Definition paren_balanced_from_pb_parse_of_item'
             (paren_balanced_from_pb_parse_of_productions
              : forall valid0 pats
                       (str : String) (Hlen : length str = 0),
                  pb_productions G valid0 pats
                  -> { p : parse_of G str pats
                           & Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p })
             {valid0 it}
             (str : String) (Hlen : length str = 0)
             (p : pb_item G valid0 it)
  : { p : parse_of_item G str it
          & Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p }.
  Proof.
    destruct p as [ nt H p ].
    eapply paren_balanced_from_pb_parse_of_productions in p; [ | eassumption.. ].
    exists (ParseNonTerminal _ (projT1 p)).
    exact (H, projT2 p).
  Defined.

  Definition paren_balanced_from_pb_parse_of_item
             {valid0 it}
             (str : String) (Hlen : length str = 0)
             (p : pb_item G valid0 it)
  : { p : parse_of_item G str it
          & Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p }
    := @paren_balanced_from_pb_parse_of_item' (@paren_balanced_from_pb_parse_of_productions) valid0 it str Hlen p.

  Definition paren_balanced_from_minimal_pb_parse_of_item
             {valid0 it}
             (str : String) (Hlen : length str = 0)
             (p : minimal_pb_item (G := G) valid0 it)
  : { p : parse_of_item G str it
          & Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p }.
  Proof.
    eapply paren_balanced_from_pb_parse_of_item; trivial.
    eapply pb_item__of__minimal_pb_item; try eassumption; reflexivity.
  Qed.

  Definition paren_balanced_from_minimal_pb_parse_of_production
             {valid0 pat}
             (str : String) (Hlen : length str = 0)
             (p : minimal_pb_production (G := G) valid0 pat)
  : { p : parse_of_production G str pat
          & Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p }.
  Proof.
    eapply paren_balanced_from_pb_parse_of_production; trivial.
    eapply pb_production__of__minimal_pb_production; try eassumption; reflexivity.
  Qed.

  Definition paren_balanced_from_minimal_pb_parse_of_productions
             {valid0 pats}
             (str : String) (Hlen : length str = 0)
             (p : minimal_pb_productions (G := G) valid0 pats)
  : { p : parse_of G str pats
          & Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p }.
  Proof.
    eapply paren_balanced_from_pb_parse_of_productions; trivial.
    eapply pb_productions__of__minimal_pb_productions; try eassumption; reflexivity.
  Qed.
End cfg.
