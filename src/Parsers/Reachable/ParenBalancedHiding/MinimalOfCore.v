(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.WellFounded.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}
          {pdata : paren_balanced_hiding_dataT Char}.

  Local Arguments pbh'_production / .
  Local Arguments minimal_pbh'_production / .
  Local Arguments pbh'_productions / .
  Local Arguments minimal_pbh'_productions / .

  Section expand.
    Context (transform1 transform2 : nonterminals_listT -> string -> nonterminals_listT).
    Context (transform12 : ((sub_nonterminals_listT ==> eq ==> sub_nonterminals_listT)%signature)
                             transform1
                             transform2).

    Fixpoint expand_generic_pbh'_productions
             {valid0 n0}
             {valid n pats}
             (Hsub : sub_nonterminals_listT valid valid0)
             (Hle : n <= n0)
             (H : generic_pbh'_productions G transform1 valid n pats)
    : generic_pbh'_productions G transform2 valid0 n0 pats
    with expand_generic_pbh'_production
           {valid0 n0}
           {valid n pat}
           (Hsub : sub_nonterminals_listT valid valid0)
           (Hle : n <= n0)
           (H : generic_pbh'_production G transform1 valid n pat)
         : generic_pbh'_production G transform2 valid0 n0 pat.
    Proof.
      { simpl in *; destruct H; [ left | right ]; eauto. }
      { simpl in *; destruct H; [ constructor 1 | constructor 2 | constructor 3 ]; eauto.
        { eapply expand_generic_pbh'_productions; [ .. | eassumption ]; try apply transform12; trivial. }
        { eapply pbh_check_level_le; eassumption. }
        { eapply expand_generic_pbh'_production; [ .. | eassumption ]; trivial.
          { rewrite <- Hle; reflexivity. } } }
    Defined.

    Fixpoint expand_size_of_pbh'_productions
             {valid0 n0}
             {valid n pats}
             (Hsub : sub_nonterminals_listT valid valid0)
             (Hle : n <= n0)
             (H : generic_pbh'_productions G transform1 valid n pats)
    : size_of_pbh'_productions (expand_generic_pbh'_productions Hsub Hle H) = size_of_pbh'_productions H
    with expand_size_of_pbh'_production
           {valid0 n0}
           {valid n pat}
           (Hsub : sub_nonterminals_listT valid valid0)
           (Hle : n <= n0)
           (H : generic_pbh'_production G transform1 valid n pat)
    : size_of_pbh'_production (expand_generic_pbh'_production Hsub Hle H) = size_of_pbh'_production H.
    Proof.
      { simpl in *; destruct H; simpl_size_of;
        apply f_equal; eauto. }
      { simpl in *; destruct H; simpl_size_of; eauto using f_equal, f_equal2, eq_refl with nocore. }
    Defined.
  End expand.

  Local Ltac t0 :=
    repeat first [ solve [ trivial ]
                 | progress subst
                 | reflexivity
                 | progress setoid_subst_rel sub_nonterminals_listT
                 | apply sub_nonterminals_listT_remove_2
                 | intro ].

  Definition pbh'_productions__of__minimal_pbh'_productions
             {valid0}
             valid n pats
             (Hsub : sub_nonterminals_listT valid valid0)
  : minimal_pbh'_productions G valid n pats -> pbh'_productions G valid0 n pats.
  Proof. apply expand_generic_pbh'_productions; t0. Qed.

  Definition pbh'_production__of__minimal_pbh'_production
             {valid0}
             valid n pat
             (Hsub : sub_nonterminals_listT valid valid0)
  : minimal_pbh'_production G valid n pat -> pbh'_production G valid0 n pat.
  Proof. apply expand_generic_pbh'_production; t0. Qed.

  Section minimize.
    Context {valid0 : nonterminals_listT}.

    Let alt_option start_level h valid
      := { nt : _ & (is_valid_nonterminal valid nt = false /\ is_valid_nonterminal valid0 nt)
                    * { p : pbh'_productions G valid0 start_level (Lookup G nt)
                            & (size_of_pbh'_productions p < h) } }%type.

    Lemma not_alt_all {start_level h} (ps : alt_option h start_level valid0)
    : False.
    Proof.
      destruct ps as [ ? [ H' _ ] ].
      revert H'; clear; intros [? ?].
      congruence.
    Qed.

    Definition alt_all_elim {start_level h T} (ps : T + alt_option h start_level valid0)
    : T.
    Proof.
      destruct ps as [|ps]; [ assumption | exfalso ].
      eapply not_alt_all; eassumption.
    Defined.

    Definition expand_alt_option' {start_level start_level' h h' valid valid'}
               (Hs : start_level <= start_level') (H : h <= h') (H' : sub_nonterminals_listT valid' valid)
    : alt_option start_level h valid -> alt_option start_level' h' valid'.
    Proof.
      hnf in H'; unfold alt_option.
      repeat match goal with
               | [ |- sigT _ -> _ ] => intros []
               | [ |- sig _ -> _ ] => intros []
               | [ |- prod _ _ -> _ ] => intros []
               | [ |- and _ _ -> _ ] => intros []
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
      assumption.
      reflexivity.
      intros ??????; subst; assumption.
    Defined.

    Definition expand_alt_option {start_level start_level' h h' valid valid'}
               (Hs : start_level <= start_level') (H : h < h') (H' : sub_nonterminals_listT valid' valid)
    : alt_option start_level h valid -> alt_option start_level' h' valid'.
    Proof.
      apply expand_alt_option'; try assumption.
      apply Lt.lt_le_weak; assumption.
    Defined.

    Section wf_parts.
      (*Let of_item_T' h
          (valid : nonterminals_listT) {it : item Char}
          (p : pbh'_item G valid0 it)
        := forall (p_small : size_of_pbh'_item p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_pbh'_item G valid it
                     & (size_of_pbh'_item (pbh'_item__of__minimal_pbh'_item pf p')) <= size_of_pbh'_item p })%type
             + alt_option (size_of_pbh'_item p) valid.

      Let of_item_T h
        := forall valid it p, @of_item_T' h valid it p.*)

      Let of_production_T' h
          (valid : nonterminals_listT) (n : nat) {pat : production Char}
          (p : pbh'_production G valid0 n pat)
        := forall (p_small : size_of_pbh'_production p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_pbh'_production G valid n pat
                     & (size_of_pbh'_production (pbh'_production__of__minimal_pbh'_production pf p') <= size_of_pbh'_production p) })%type
                + alt_option (size_of_pbh'_production p) n valid.

      Let of_production_T h
        := forall valid n pat p, @of_production_T' h valid n pat p.

      Let of_productions_T' h
          (valid : nonterminals_listT) (n : nat) {pats : productions Char}
          (p : pbh'_productions G valid0 n pats)
        := forall (p_small : size_of_pbh'_productions p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_pbh'_productions G valid n pats
                     & (size_of_pbh'_productions (pbh'_productions__of__minimal_pbh'_productions pf p') <= size_of_pbh'_productions p) })%type
             + alt_option (size_of_pbh'_productions p) n valid.

      Let of_productions_T h
        := forall valid n pats p, @of_productions_T' h valid n pats p.

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
                 {struct h}
        : of_production_T h
        with minimal_pbh'_productions__of__pbh'_productions'
               h
               {struct h}
             : of_productions_T h.
        Proof.
          { intros valid' n pat p H_h Hinit'.
            destruct h as [|h']; [ exfalso; omega | ].
            specialize (minimal_pbh'_production__of__pbh'_production' h').
            specialize (minimal_pbh'_productions__of__pbh'_productions' h').
            specialize (fun valid pf => minimal_pbh'_production__of__pbh'_production' valid _ _ p (le_S _ _ pf)).
            SearchAbout (S ?x <= S ?y -> S ?x <= ?y).
            unfold of_production_T' in *.
 _ (le_S _ _ pf)).
            specialize (minimal_pbh'_item__of__pbh'_item h' (Le.le_n_Sn _)).
            destruct p as [ | ?? p0' p1' ].
            { left; eexists (MinMaybeEmptyProductionNil _); simpl; reflexivity. }
            { assert (size_of_pbh'_item p0' < h') by exact (lt_helper_1 H_h).
              assert (size_of_pbh'_production p1' < h') by exact (lt_helper_2 H_h).
              destruct (fun k => minimal_pbh'_item__of__pbh'_item valid' _ p0' k Hinit')
                as [ [p0'' H0''] | p0'' ];
                [ assumption
                | destruct (fun k => minimal_pbh'_production__of__pbh'_production' valid' _ p1' k Hinit')
                  as [ [p1'' H1''] | p1'' ];
                  [ assumption
                  | left | right ]
                | right ].
              { eexists (MinMaybeEmptyProductionCons p0'' p1'').
                simpl in *.
                apply Le.le_n_S, Plus.plus_le_compat; assumption. }
              { eapply expand_alt_option; [ .. | eassumption ];
                try solve [ apply Lt.lt_n_Sn
                          | apply lt_helper_1'
                          | apply lt_helper_2'
                          | reflexivity ]. }
              { eapply expand_alt_option; [ .. | eassumption ];
                try solve [ apply Lt.lt_n_Sn
                          | apply lt_helper_1'
                          | apply lt_helper_2'
                          | reflexivity ]. } }
        Defined.
      End production.

      Section productions.
        Fixpoint minimal_pbh'_productions__of__pbh'_productions'
                 h
                 (minimal_pbh'_item__of__pbh'_item
                  : forall h' (pf : h' <= h), @of_item_T h')
                 {struct h}
        : of_productions_T h.
        Proof.
          intros valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          specialize (minimal_pbh'_productions__of__pbh'_productions' h' (fun h'' pf => minimal_pbh'_item__of__pbh'_item _ (le_S _ _ pf))).
          pose proof (minimal_pbh'_production__of__pbh'_production' (fun h'' pf => minimal_pbh'_item__of__pbh'_item _ (le_S _ _ pf))) as minimal_pbh'_production__of__pbh'_production''.
          specialize (minimal_pbh'_item__of__pbh'_item h' (Le.le_n_Sn _)).
          destruct p as [ ? ? p' | ? ? p' ].
          { destruct (fun k => minimal_pbh'_production__of__pbh'_production'' valid' _ p' k Hinit')
              as [ [p'' H''] | p'' ];
            [ solve [ auto with arith ]
            | left | right ].
            { eexists (MinMaybeEmptyHead _ p'').
              simpl in *.
              apply Le.le_n_S; exact H''. }
            { eapply expand_alt_option; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
                        | reflexivity ]. } }
          { destruct (minimal_pbh'_productions__of__pbh'_productions' valid' _ p' (Lt.lt_S_n _ _ H_h) Hinit')
              as [ [p'' H''] | p'' ];
            [ left | right ].
            { eexists (MinMaybeEmptyTail _ p'').
              simpl in *.
              apply Le.le_n_S; exact H''. }
            { eapply expand_alt_option; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
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
          intros valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [nonterminal' H' p'].
          { case_eq (is_valid_nonterminal valid' nonterminal'); intro H'''.
            { edestruct (fun k => @minimal_pbh'_productions__of__pbh'_productions' _ (fun h'' pf => minimal_pbh'_item__of__pbh'_item _ (Le.le_n_S _ _ pf)) (remove_nonterminal valid' nonterminal') _ p' k)
              as [ [ p'' H'' ] | [ nt'' H'' ] ];
            [ solve [ auto with arith ]
            | left | ].
            { eexists (MinMaybeEmptyNonTerminal _ _ H''' p'').
              apply Le.le_n_S; eassumption. }
            { destruct (string_dec nonterminal' nt''); subst.
              { destruct H'' as [ H'' [ p'' H'''' ] ].
                simpl in *.
                destruct (fun k => minimal_pbh'_item__of__pbh'_item _ (@reflexivity _ le _ _) valid' _ (MaybeEmptyNonTerminal _ H' p'') k Hinit')
                  as [ [ p''' H0' ] | p''' ];
                  [ solve [ eauto with arith ]
                  | left | right ].
                { exists p'''; eauto with arith. }
                { eapply expand_alt_option; [ .. | eassumption ];
                  eauto with arith;
                  reflexivity. } }
              { right.
                exists nt''.
                destruct_head prod; destruct_head and; repeat split; trivial.
                { erewrite <- remove_nonterminal_5 by eassumption; assumption. }
                { destruct_head sigT.
                  eexists.
                  apply Lt.lt_S; eassumption. } } } }
            { right.
              exists nonterminal'; repeat split; trivial; [].
              exists p'.
              auto with arith. } }
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

        Definition minimal_pbh'_item__of__pbh'_item
                   {it : item Char}
                   (p : pbh'_item G valid0 it)
        : minimal_pbh'_item G valid0 it.
        Proof.
          pose proof (@minimal_pbh'_item__of__pbh'_item'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
          apply alt_all_elim in X.
          exact (projT1 X).
        Defined.

        Definition minimal_pbh'_production__of__pbh'_production
                   {pat : production Char}
                   (p : pbh'_production G valid0 pat)
        : minimal_pbh'_production G valid0 pat.
        Proof.
          pose proof (@minimal_pbh'_production__of__pbh'_production'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
          apply alt_all_elim in X.
          exact (projT1 X).
        Defined.

        Definition minimal_pbh'_productions__of__pbh'_productions
                   {pats : productions Char}
                   (p : pbh'_productions G valid0 pats)
        : minimal_pbh'_productions G valid0 pats.
        Proof.
          pose proof (@minimal_pbh'_productions__of__pbh'_productions'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
          apply alt_all_elim in X.
          exact (projT1 X).
        Defined.


        Definition minimal_pbh'_item__iff__pbh'_item
                   {it : item Char}
        : inhabited (pbh'_item G valid0 it)
          <-> inhabited (minimal_pbh'_item G valid0 it).
        Proof.
          split; intros [H]; constructor;
          [ apply minimal_pbh'_item__of__pbh'_item
          | eapply pbh'_item__of__minimal_pbh'_item ];
          try (eassumption || reflexivity).
        Qed.

        Definition minimal_pbh'_production__iff__pbh'_production
                   {it : production Char}
        : inhabited (pbh'_production G valid0 it)
          <-> inhabited (minimal_pbh'_production G valid0 it).
        Proof.
          split; intros [H]; constructor;
          [ apply minimal_pbh'_production__of__pbh'_production
          | eapply pbh'_production__of__minimal_pbh'_production ];
          try (eassumption || reflexivity).
        Qed.

        Definition minimal_pbh'_productions__iff__pbh'_productions
                   {it : productions Char}
        : inhabited (pbh'_productions G valid0 it)
          <-> inhabited (minimal_pbh'_productions G valid0 it).
        Proof.
          split; intros [H]; constructor;
          [ apply minimal_pbh'_productions__of__pbh'_productions
          | eapply pbh'_productions__of__minimal_pbh'_productions ];
          try (eassumption || reflexivity).
        Qed.
    End wf_parts.
  End minimize.
End cfg.
