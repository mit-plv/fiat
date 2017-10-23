(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalanced.MinimalOfCore.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.WellFounded.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}
          {pdata : paren_balanced_hiding_dataT Char}.

  Local Arguments pbh'_production / _ _ _ _ _ _ _ _.
  Local Arguments minimal_pbh'_production / _ _ _ _ _ _ _ _.
  Local Arguments pbh'_productions / _ _ _ _ _ _ _.
  Local Arguments minimal_pbh'_productions / _ _ _ _ _ _ _.
  Local Arguments eq_rect_r / _ _ _ _ _ _.
  Local Arguments eq_rect / _ _ _ _ _ _.

  Section expand.
    Context (transform1 transform2 : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT).
    Context (transform12 : ((sub_nonterminals_listT ==> eq ==> sub_nonterminals_listT)%signature)
                             transform1
                             transform2).

    Fixpoint expand_generic_pbh'_productions
             {valid0 valid0'}
             {valid'}
             {valid pats}
             (Hsub0 : sub_nonterminals_listT valid0 valid0')
             (Hsub : sub_nonterminals_listT valid valid')
             (H : generic_pbh'_productions G transform1 valid0 valid pats)
    : generic_pbh'_productions G transform2 valid0' valid' pats
    with expand_generic_pbh'_production
           {valid0 valid0'}
           {valid' n'}
           {valid n pat}
           (Hsub0 : sub_nonterminals_listT valid0 valid0')
           (Hsub : sub_nonterminals_listT valid valid')
           (Hle : n = n')
           (H : generic_pbh'_production G transform1 valid0 valid n pat)
         : generic_pbh'_production G transform2 valid0' valid' n' pat.
    Proof.
      { simpl in *; destruct H; [ left | right ]; eauto. }
      { simpl in *; subst; destruct H; [ constructor 1 | constructor 2 | constructor 3 | econstructor 4 ]; eauto.
        { eapply expand_generic_pbh'_productions; [ .. | eassumption ]; try apply transform12; trivial. }
        { eapply expand_generic_pb'_production; [ | eassumption | reflexivity | eassumption ].
          unfold respectful; trivial. } }
    Defined.

    Fixpoint expand_size_of_pbh'_productions
             {valid0 valid0'}
             {valid'}
             {valid pats}
             (Hsub0 : sub_nonterminals_listT valid0 valid0')
             (Hsub : sub_nonterminals_listT valid valid')
             (H : generic_pbh'_productions G transform1 valid0 valid pats)
    : size_of_pbh'_productions (expand_generic_pbh'_productions Hsub0 Hsub H) = size_of_pbh'_productions H
    with expand_size_of_pbh'_production
           {valid0 valid0'}
           {valid' n'}
           {valid n pat}
           (Hsub0 : sub_nonterminals_listT valid0 valid0')
           (Hsub : sub_nonterminals_listT valid valid')
           (Hle : n = n')
           (H : generic_pbh'_production G transform1 valid0 valid n pat)
    : size_of_pbh'_production (expand_generic_pbh'_production Hsub0 Hsub Hle H) = size_of_pbh'_production H.
    Proof.
      { simpl in *; destruct H; simpl_size_of; trivial; eauto;
        apply f_equal; eauto. }
      { simpl in *; destruct H; subst; simpl_size_of; eauto using f_equal, f_equal2, eq_refl with nocore. }
    Defined.
  End expand.

  Local Ltac t0 :=
    repeat first [ solve [ trivial ]
                 | progress subst
                 | reflexivity
                 | progress setoid_subst_rel sub_nonterminals_listT
                 | apply sub_nonterminals_listT_remove_2
                 | intro
                 | progress destruct_head bool ].

  Definition pbh'_productions__of__minimal_pbh'_productions
             {valid0 valid0'}
             valid valid' pats
             (Hsub0 : sub_nonterminals_listT valid0 valid0')
             (Hsub : sub_nonterminals_listT valid valid')
  : minimal_pbh'_productions G valid0 valid pats -> pbh'_productions G valid0' valid' pats.
  Proof. apply expand_generic_pbh'_productions; t0. Defined.

  Definition pbh'_production__of__minimal_pbh'_production
             {valid0 valid0'}
             valid valid' n pat
             (Hsub0 : sub_nonterminals_listT valid0 valid0')
             (Hsub : sub_nonterminals_listT valid valid')
  : minimal_pbh'_production G valid0 valid n pat -> pbh'_production G valid0' valid' n pat.
  Proof. apply expand_generic_pbh'_production; t0. Defined.

  Section minimize.
    Context {valid00 : nonterminals_listT}.
    Section alt_option.
      Context (valid0 : nonterminals_listT).

      Definition alt_option h valid
        := { nt : _ & (is_valid_nonterminal valid (of_nonterminal nt) = false /\ is_valid_nonterminal valid0 (of_nonterminal nt))
                      * { p : pbh'_productions G valid00 valid0 (Lookup G nt)
                              & (size_of_pbh'_productions p < h) } }%type.

      Lemma not_alt_all {h} (ps : alt_option h valid0)
      : False.
      Proof.
        destruct ps as [ ? [ H' _ ] ].
        revert H'; clear; intros [? ?].
        congruence.
      Qed.

      Definition alt_all_elim {h T} (ps : T + alt_option h valid0)
      : T.
      Proof.
        destruct ps as [|ps]; [ assumption | exfalso ].
        eapply not_alt_all; eassumption.
      Defined.

      Definition expand_alt_option' {h h' valid valid'}
                 (H : h <= h') (H' : sub_nonterminals_listT valid' valid)
      : alt_option h valid -> alt_option h' valid'.
      Proof.
        hnf in H'; unfold alt_option.
        repeat match goal with
                 | [ |- sigT _ -> _ ] => intros_destruct
                 | [ |- sig _ -> _ ] => intros_destruct
                 | [ |- prod _ _ -> _ ] => intros_destruct
                 | [ |- and _ _ -> _ ] => intros_destruct
                 | _ => intro
                 | _ => progress subst
                 | [ H : size_of_pbh'_productions ?x < _ |- _ ] => is_var x; erewrite <- expand_size_of_pbh'_productions in H
                 | [ |- prod _ _ ] => split
                 | [ |- and _ _ ] => split
                 | [ |- sigT _ ] => esplit
                 | [ |- sig _ ] => esplit
                 | [ H : _ = false |- _ = false ]
                   => apply Bool.not_true_iff_false in H;
                     apply Bool.not_true_iff_false;
                     intro; apply H
                 | _ => eapply H'; eassumption
                 | _ => assumption
                 | _ => eassumption
                 | [ |- _ < _ ] => eapply Lt.lt_trans; eassumption
                 | [ |- _ < _ ] => eapply Lt.lt_le_trans; eassumption
               end.
        Grab Existential Variables.
        reflexivity.
        reflexivity.
        unfold respectful; intros; subst; assumption.
      Defined.

      Definition expand_alt_option {h h' valid valid'}
                 (H : h < h') (H' : sub_nonterminals_listT valid' valid)
      : alt_option h valid -> alt_option h' valid'.
      Proof.
        apply expand_alt_option'; try assumption.
        apply Lt.lt_le_weak; assumption.
      Defined.
    End alt_option.

    Context {valid0 : nonterminals_listT}
            (Hsub0 : sub_nonterminals_listT valid0 initial_nonterminals_data).

    Section wf_parts.
      Let of_item_T' h
          (valid : nonterminals_listT) {nt : string}
          (p : pbh'_productions G valid00 valid0 (Lookup G nt))
        := forall (p_small : size_of_pbh'_productions p < h)
                  (pf : sub_nonterminals_listT (remove_nonterminal valid (of_nonterminal nt)) valid0),
             ({ p' : minimal_pbh'_productions G valid00 (remove_nonterminal valid (of_nonterminal nt)) (Lookup G nt)
                     & (size_of_pbh'_productions (pbh'_productions__of__minimal_pbh'_productions (reflexivity _) pf p')) <= size_of_pbh'_productions p })%type
             + alt_option valid0 (size_of_pbh'_productions p) valid.

      Let of_item_T h
        := forall valid it p, @of_item_T' h valid it p.

      Let of_production_T' h
          (valid : nonterminals_listT) (n : nat) {pat : production Char}
          (p : pbh'_production G valid00 valid0 n pat)
        := forall (p_small : size_of_pbh'_production p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_pbh'_production G valid00 valid n pat
                     & (size_of_pbh'_production (pbh'_production__of__minimal_pbh'_production (reflexivity _) pf p') <= size_of_pbh'_production p) })%type
                + alt_option valid0 (size_of_pbh'_production p) valid.

      Let of_production_T h
        := forall valid n pat p, @of_production_T' h valid n pat p.

      Let of_productions_T' h
          (valid : nonterminals_listT) {pats : productions Char}
          (p : pbh'_productions G valid00 valid0 pats)
        := forall (p_small : size_of_pbh'_productions p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_pbh'_productions G valid00 valid pats
                     & (size_of_pbh'_productions (pbh'_productions__of__minimal_pbh'_productions (reflexivity _) pf p') <= size_of_pbh'_productions p) })%type
             + alt_option valid0 (size_of_pbh'_productions p) valid.

      Let of_productions_T h
        := forall valid pats p, @of_productions_T' h valid pats p.

      Section production.
        Lemma lt_helper_1 {x y z} (H : S (x + y) < S z) : x < z.
        Proof. omega. Qed.

        Lemma lt_helper_2 {x y z} (H : S (x + y) < S z) : y < z.
        Proof. omega. Qed.

        Lemma lt_helper_1' {x y} : x < S (x + y).
        Proof. omega. Qed.

        Lemma lt_helper_2' {x y} : y < S (x + y).
        Proof. omega. Qed.

        Fixpoint minimal_pbh'_production__of__pbh'_production'
                 h
                 (minimal_pbh'_item__of__pbh'_item'
                  : forall h' (pf : h' < h), @of_item_T h')
                 {struct h}
        : of_production_T h.
        Proof.
          intros valid' n pat p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          specialize (minimal_pbh'_production__of__pbh'_production' h' (fun h'' pf => minimal_pbh'_item__of__pbh'_item' _ (le_S _ _ pf))).
          specialize (minimal_pbh'_item__of__pbh'_item' h' (Lt.lt_n_Sn _)).
          destruct p as [ | ? nt' ?? p0' p1' | ?? nt' ? p0' p' | ??????? p' ]; simpl_size_of.
          { left; eexists (PBHProductionNil _ _ _ _); reflexivity. }
          { assert (size_of_pbh'_productions p0' < h') by exact (lt_helper_1 H_h).
            assert (size_of_pbh'_production p1' < h') by exact (lt_helper_2 H_h).
            assert (pf : sub_nonterminals_listT (remove_nonterminal valid' (of_nonterminal nt')) valid)
              by (rewrite Hinit'; apply sub_nonterminals_listT_remove_2; reflexivity).
            destruct (is_valid_nonterminal valid' (of_nonterminal nt')) eqn:Hnt'.
            { assert (pf' : sub_nonterminals_listT (remove_nonterminal valid' (of_nonterminal nt')) valid)
                by (rewrite Hinit'; apply sub_nonterminals_listT_remove_2; reflexivity).
              destruct (fun k => minimal_pbh'_item__of__pbh'_item' _ _ p0' k pf')
                as [ [p0'' H0''] | p0'' ];
                [ assumption
                | destruct (fun k => minimal_pbh'_production__of__pbh'_production' valid' _ _ p1' k Hinit')
                  as [ [p1'' H1''] | p1'' ];
                  [ assumption
                  | left | right ]
                | right ];
                unfold pbh'_production__of__minimal_pbh'_production, pbh'_productions__of__minimal_pbh'_productions in *; simpl;
                rewrite ?expand_size_of_pbh'_production, ?expand_size_of_pbh'_productions in *.
              { eexists (PBHProductionConsNonTerminal0 _ Hnt' p0'' p1'').
                rewrite ?expand_size_of_pbh'_production, ?expand_size_of_pbh'_productions in *.
                simpl_size_of.
                apply Le.le_n_S, Plus.plus_le_compat; assumption. }
              { eapply expand_alt_option'; [ .. | eassumption ];
                try solve [ apply Lt.lt_n_Sn
                          | apply lt_helper_1'
                          | apply lt_helper_2'
                          | reflexivity
                          | omega ]. }
              { eapply expand_alt_option'; [ .. | eassumption ];
                try solve [ apply Lt.lt_n_Sn
                          | apply lt_helper_1'
                          | apply lt_helper_2'
                          | reflexivity
                          | destruct start_level; reflexivity
                          | abstract omega ]. } }
            { right.
              exists nt'.
              split; [ split; assumption | ].
              exists p0'.
              abstract omega. } }
          { assert (size_of_pbh'_production p' < h') by omega.
            assert (pf : sub_nonterminals_listT (remove_nonterminal valid' (of_nonterminal nt')) valid)
              by (rewrite Hinit'; apply sub_nonterminals_listT_remove_2; reflexivity).
            assert (pf' : sub_nonterminals_listT (remove_nonterminal valid' (of_nonterminal nt')) valid)
              by (rewrite Hinit'; apply sub_nonterminals_listT_remove_2; reflexivity).
            destruct (fun k => minimal_pbh'_production__of__pbh'_production' valid' _ _ p' k Hinit')
              as [ [p1'' H1''] | p1'' ];
              [ assumption
              | left | right ];
              unfold pbh'_production__of__minimal_pbh'_production, pbh'_productions__of__minimal_pbh'_productions in *; simpl;
              rewrite ?expand_size_of_pbh'_production, ?expand_size_of_pbh'_productions in *.
            { eexists (PBHProductionConsNonTerminalS p0' p1'').
              rewrite ?expand_size_of_pbh'_production, ?expand_size_of_pbh'_productions in *.
              simpl_size_of.
              apply Le.le_n_S; assumption. }
            { eapply expand_alt_option'; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
                        | apply lt_helper_1'
                        | apply lt_helper_2'
                        | reflexivity
                        | omega ]. } }
          { assert (size_of_pbh'_production p' < h') by omega.
            destruct (fun k => minimal_pbh'_production__of__pbh'_production' _ _ _ p' k Hinit')
              as [ [p0'' H0''] | p0'' ];
              [ assumption
              | left
              | right ];
              unfold pbh'_production__of__minimal_pbh'_production, pbh'_productions__of__minimal_pbh'_productions in *; simpl;
              rewrite ?expand_size_of_pbh'_production, ?expand_size_of_pbh'_productions in *.
            { eexists (PBHProductionConsTerminal _ _ _ _ p0'').
              rewrite ?expand_size_of_pbh'_production, ?expand_size_of_pbh'_productions in *.
              simpl_size_of.
              apply Le.le_n_S; assumption. }
            { unfold pb_new_level in *.
              eapply expand_alt_option'; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
                        | apply lt_helper_1'
                        | apply lt_helper_2'
                        | reflexivity
                        | omega ]. } }
          Grab Existential Variables.
          assumption.
          assumption.
        Defined.
      End production.

      Section productions.
        Fixpoint minimal_pbh'_productions__of__pbh'_productions'
                 h
                 (minimal_pbh'_item__of__pbh'_item
                  : forall h' (pf : h' < h), @of_item_T h')
                 {struct h}
        : of_productions_T h.
        Proof.
          intros valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          specialize (minimal_pbh'_productions__of__pbh'_productions' h' (fun h'' pf => minimal_pbh'_item__of__pbh'_item _ (le_S _ _ pf))).
          pose proof (minimal_pbh'_production__of__pbh'_production' (fun h'' pf => minimal_pbh'_item__of__pbh'_item _ (le_S _ _ pf))) as minimal_pbh'_production__of__pbh'_production''.
          specialize (minimal_pbh'_item__of__pbh'_item h' (Lt.lt_n_Sn _)).
          destruct p as [ | ??? p0' p1' ].
          { left.
            eexists (PBHNil _ _ _ _).
            unfold pbh'_productions__of__minimal_pbh'_productions; simpl.
            rewrite expand_size_of_pbh'_productions.
            simpl_size_of.
            omega. }
          { assert (size_of_pbh'_production p0' < h') by exact (lt_helper_1 H_h).
            assert (size_of_pbh'_productions p1' < h') by exact (lt_helper_2 H_h).
            destruct (fun k => minimal_pbh'_production__of__pbh'_production'' valid' _ _ p0' k Hinit')
              as [ [p0'' H0''] | p0'' ];
              [ solve [ auto with arith ]
              | destruct (fun k => minimal_pbh'_productions__of__pbh'_productions' valid' _ p1' k Hinit')
                as [ [p1'' H1''] | p1'' ]; try assumption;
                [ left
                | right ]
              | right ].
            { exists (PBHCons p0'' p1'').
              simpl in *.
              unfold pbh'_productions__of__minimal_pbh'_productions in *.
              unfold pbh'_production__of__minimal_pbh'_production in *.
              rewrite expand_size_of_pbh'_productions in *.
              rewrite expand_size_of_pbh'_production in *.
              simpl_size_of.
              omega. }
            { eapply expand_alt_option'; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
                        | simpl_size_of; omega
                        | reflexivity ]. }
            { eapply expand_alt_option'; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
                        | simpl_size_of; omega
                        | reflexivity ]. } }
        Defined.
      End productions.

      Section item.
        Definition minimal_pbh'_item__of__pbh'_item_step
                   h
                   (minimal_pbh'_item__of__pbh'_item
                    : forall h' (pf : h' < h), @of_item_T h')
        : of_item_T h.
        Proof.
          intros valid' nt p H_h Hinit'.
          pose proof (minimal_pbh'_productions__of__pbh'_productions' minimal_pbh'_item__of__pbh'_item) as X.
          specialize (X (remove_nonterminal valid' (of_nonterminal nt)) (Lookup G nt) p H_h Hinit').
          destruct X as [p' | [nt' [[H0' H1'] [p' H']]] ];
            [ left
            | ].
          { exact p'. }
          { destruct (is_valid_nonterminal valid' (of_nonterminal nt')) eqn:Hvalid.
            { assert (H'nt : of_nonterminal nt = of_nonterminal nt').
              { apply remove_nonterminal_2 in H0'.
                destruct H0' as [ H0' | ]; [ | assumption ].
                clear -H0' Hvalid; congruence. }
              pose proof (f_equal to_nonterminal H'nt) as H'nt'.
              rewrite !to_of_nonterminal
                in H'nt'
                by (apply initial_nonterminals_correct, Hsub0;
                    first [ assumption
                          | rewrite -> H'nt; assumption
                          | rewrite <- H'nt; assumption ]).
              subst.
              destruct (minimal_pbh'_item__of__pbh'_item _ H_h valid' _ p' H' Hinit')
                as [ [p'' H''] | p''].
              { left; exists p''.
                omega. }
              { right.
                eapply expand_alt_option'; [ .. | eassumption ];
                try solve [ reflexivity
                          | omega ]. } }
            { right.
              exists nt'.
              split; [ split; assumption | ].
              exists p'.
              omega. } }
        Defined.

        Definition minimal_pbh'_item__of__pbh'_item''
        : forall h, of_item_T h.
        Proof.
          apply (Fix Wf_nat.lt_wf).
          exact minimal_pbh'_item__of__pbh'_item_step.
        Defined.
      End item.

      Definition minimal_pbh'_production__of__pbh'_production''
                 h
      : of_production_T h
        := @minimal_pbh'_production__of__pbh'_production' h (fun _ _ => @minimal_pbh'_item__of__pbh'_item'' _).

      Definition minimal_pbh'_productions__of__pbh'_productions''
                 h
      : of_productions_T h
        := @minimal_pbh'_productions__of__pbh'_productions' h (fun _ _ => @minimal_pbh'_item__of__pbh'_item'' _).

      Definition minimal_pbh'_production__of__pbh'_production
                 {n} {pat : production Char}
                 (p : pbh'_production G valid00 valid0 n pat)
      : minimal_pbh'_production G valid00 valid0 n pat.
      Proof.
        pose proof (@minimal_pbh'_production__of__pbh'_production'' _ valid0 _ _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
        apply alt_all_elim in X.
        exact (projT1 X).
      Defined.

      Definition minimal_pbh'_productions__of__pbh'_productions
                 {pats : productions Char}
                 (p : pbh'_productions G valid00 valid0 pats)
      : minimal_pbh'_productions G valid00 valid0 pats.
      Proof.
        pose proof (@minimal_pbh'_productions__of__pbh'_productions'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
        apply alt_all_elim in X.
        exact (projT1 X).
      Defined.


      Definition minimal_pbh'_production__iff__pbh'_production
                 {n} {it : production Char}
      : inhabited (pbh'_production G valid00 valid0 n it)
        <-> inhabited (minimal_pbh'_production G valid00 valid0 n it).
      Proof.
        split; intros [H]; constructor;
        [ apply minimal_pbh'_production__of__pbh'_production
        | eapply pbh'_production__of__minimal_pbh'_production ];
        try (eassumption || reflexivity).
      Qed.

      Definition minimal_pbh'_productions__iff__pbh'_productions
                 {it : productions Char}
      : inhabited (pbh'_productions G valid00 valid0 it)
        <-> inhabited (minimal_pbh'_productions G valid00 valid0 it).
      Proof.
        split; intros [H]; constructor;
        [ apply minimal_pbh'_productions__of__pbh'_productions
        | eapply pbh'_productions__of__minimal_pbh'_productions ];
        try (eassumption || reflexivity).
      Qed.
    End wf_parts.
  End minimize.
End cfg.
