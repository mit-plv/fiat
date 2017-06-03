(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Minimal.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.WellFounded.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Definition maybe_empty_item__of__minimal_maybe_empty_item'
             {valid0}
             (maybe_empty_productions__of__minimal_maybe_empty_productions
              : forall valid prods,
                  sub_nonterminals_listT valid valid0
                  -> minimal_maybe_empty_productions (G := G) valid prods
                  -> maybe_empty_productions G valid0 prods)
             valid it
             (Hsub : sub_nonterminals_listT valid valid0)
             (H : minimal_maybe_empty_item (G := G) valid it)
  : maybe_empty_item G valid0 it.
  Proof.
    destruct H; constructor.
    { clear maybe_empty_productions__of__minimal_maybe_empty_productions; eauto. }
    { eapply maybe_empty_productions__of__minimal_maybe_empty_productions; [ | eassumption ].
      clear -Hsub rdata'.
      eauto using sub_nonterminals_listT_remove_2. }
  Defined.

  Fixpoint maybe_empty_productions__of__minimal_maybe_empty_productions
             {valid0}
             valid pats
             (Hsub : sub_nonterminals_listT valid valid0)
             (H : minimal_maybe_empty_productions (G := G) valid pats)
  : maybe_empty_productions G valid0 pats
  with maybe_empty_production__of__minimal_maybe_empty_production
             {valid0}
             valid pat
             (Hsub : sub_nonterminals_listT valid valid0)
             (H : minimal_maybe_empty_production (G := G) valid pat)
  : maybe_empty_production G valid0 pat.
  Proof.
    { destruct H; [ left | right ]; eauto. }
    { destruct H; [ left | right ]; eauto using maybe_empty_item__of__minimal_maybe_empty_item'. }
  Defined.

  Definition maybe_empty_item__of__minimal_maybe_empty_item
             {valid0}
    := @maybe_empty_item__of__minimal_maybe_empty_item' valid0 maybe_empty_productions__of__minimal_maybe_empty_productions.

  Section expand.
    Definition expand_minimal_maybe_empty_item'
               (expand_minimal_maybe_empty_productions
                : forall valid valid' prods,
                    sub_nonterminals_listT valid valid'
                    -> minimal_maybe_empty_productions (G := G) valid prods
                    -> minimal_maybe_empty_productions (G := G) valid' prods)
               valid valid' it
               (Hsub : sub_nonterminals_listT valid valid')
               (H : minimal_maybe_empty_item (G := G) valid it)
    : minimal_maybe_empty_item (G := G) valid' it.
    Proof.
      destruct H; constructor.
      { clear expand_minimal_maybe_empty_productions; eauto. }
      { eapply expand_minimal_maybe_empty_productions; [ | eassumption ].
        clear -Hsub rdata'.
        eauto using remove_nonterminal_mor. }
    Defined.

    Fixpoint expand_minimal_maybe_empty_productions
             valid valid' pats
             (Hsub : sub_nonterminals_listT valid valid')
             (H : minimal_maybe_empty_productions (G := G) valid pats)
    : minimal_maybe_empty_productions (G := G) valid' pats
    with expand_minimal_maybe_empty_production
           valid valid' pat
           (Hsub : sub_nonterminals_listT valid valid')
           (H : minimal_maybe_empty_production (G := G) valid pat)
         : minimal_maybe_empty_production (G := G) valid' pat.
    Proof.
      { destruct H; [ left | right ]; eauto. }
      { destruct H; [ left | right ]; eauto using expand_minimal_maybe_empty_item'. }
    Defined.

    Definition expand_minimal_maybe_empty_item
      := @expand_minimal_maybe_empty_item' expand_minimal_maybe_empty_productions.
  End expand.

  (*Global Instance minimal_maybe_empty_item_Proper {valid0}
  : Proper (sub_nonterminals_listT ==> eq ==> impl) (minimal_maybe_empty_item (G := G) ch).
  Proof. repeat intro; subst; eapply expand_minimal_maybe_empty_item; eauto. Qed.

  Global Instance minimal_maybe_empty_production_Proper {valid0}
  : Proper (sub_nonterminals_listT ==> eq ==> impl) (minimal_maybe_empty_production (G := G) ch).
  Proof. repeat intro; subst; eapply expand_minimal_maybe_empty_production; eauto. Qed.

  Global Instance minimal_maybe_empty_productions_Proper {valid0}
  : Proper (sub_nonterminals_listT ==> eq ==> impl) (minimal_maybe_empty_productions (G := G) ch).
  Proof. repeat intro; subst; eapply expand_minimal_maybe_empty_productions; eauto. Qed.*)

  Section minimize.
    Context {valid0 : nonterminals_listT}
            (Hsub0 : sub_nonterminals_listT valid0 initial_nonterminals_data).

    Let alt_option h valid
      := { nt : _ & (is_valid_nonterminal valid (of_nonterminal nt) = false /\ is_valid_nonterminal valid0 (of_nonterminal nt))
                    * { p : maybe_empty_productions G valid0 (Lookup G nt)
                            & (size_of_maybe_empty_productions p < h) } }%type.

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
               | [ |- sigT _ ] => esplit
               | [ |- sig _ ] => esplit
               | [ |- prod _ _ ] => split
               | [ |- and _ _ ] => split
               | [ H : _ = false |- _ = false ]
                 => apply Bool.not_true_iff_false in H;
                   apply Bool.not_true_iff_false;
                   intro; apply H
               | _ => eapply H'; eassumption
               | _ => assumption
               | [ |- _ < _ ] => eapply Lt.lt_trans; eassumption
               | [ |- _ < _ ] => eapply Lt.lt_le_trans; eassumption
             end.
    Defined.

    Definition expand_alt_option {h h' valid valid'}
               (H : h < h') (H' : sub_nonterminals_listT valid' valid)
    : alt_option h valid -> alt_option h' valid'.
    Proof.
      apply expand_alt_option'; try assumption.
      apply Lt.lt_le_weak; assumption.
    Defined.

    Section wf_parts.
      Let of_item_T' h
          (valid : nonterminals_listT) {it : item Char}
          (p : maybe_empty_item G valid0 it)
        := forall (p_small : size_of_maybe_empty_item p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_maybe_empty_item (G := G) valid it
                     & (size_of_maybe_empty_item (maybe_empty_item__of__minimal_maybe_empty_item pf p')) <= size_of_maybe_empty_item p })%type
             + alt_option (size_of_maybe_empty_item p) valid.

      Let of_item_T h
        := forall valid it p, @of_item_T' h valid it p.

      Let of_production_T' h
          (valid : nonterminals_listT) {pat : production Char}
          (p : maybe_empty_production G valid0 pat)
        := forall (p_small : size_of_maybe_empty_production p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_maybe_empty_production (G := G) valid pat
                     & (size_of_maybe_empty_production (maybe_empty_production__of__minimal_maybe_empty_production pf p') <= size_of_maybe_empty_production p) })%type
                + alt_option (size_of_maybe_empty_production p) valid.

      Let of_production_T h
        := forall valid pat p, @of_production_T' h valid pat p.

      Let of_productions_T' h
          (valid : nonterminals_listT) {pats : productions Char}
          (p : maybe_empty_productions G valid0 pats)
        := forall (p_small : size_of_maybe_empty_productions p < h)
                  (pf : sub_nonterminals_listT valid valid0),
             ({ p' : minimal_maybe_empty_productions (G := G) valid pats
                     & (size_of_maybe_empty_productions (maybe_empty_productions__of__minimal_maybe_empty_productions pf p') <= size_of_maybe_empty_productions p) })%type
             + alt_option (size_of_maybe_empty_productions p) valid.

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

        Fixpoint minimal_maybe_empty_production__of__maybe_empty_production'
                 h
                 (minimal_maybe_empty_item__of__maybe_empty_item
                  : forall h' (pf : h' <= h), @of_item_T h')
                 {struct h}
        : of_production_T h.
        Proof.
          intros valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          specialize (minimal_maybe_empty_production__of__maybe_empty_production' h' (fun h'' pf => minimal_maybe_empty_item__of__maybe_empty_item _ (le_S _ _ pf))).
          specialize (minimal_maybe_empty_item__of__maybe_empty_item h' (Le.le_n_Sn _)).
          destruct p as [ | ?? p0' p1' ].
          { left; eexists (MinMaybeEmptyProductionNil _); simpl; reflexivity. }
          { assert (size_of_maybe_empty_item p0' < h') by exact (lt_helper_1 H_h).
            assert (size_of_maybe_empty_production p1' < h') by exact (lt_helper_2 H_h).
            destruct (fun k => minimal_maybe_empty_item__of__maybe_empty_item valid' _ p0' k Hinit')
              as [ [p0'' H0''] | p0'' ];
              [ assumption
              | destruct (fun k => minimal_maybe_empty_production__of__maybe_empty_production' valid' _ p1' k Hinit')
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
        Fixpoint minimal_maybe_empty_productions__of__maybe_empty_productions'
                 h
                 (minimal_maybe_empty_item__of__maybe_empty_item
                  : forall h' (pf : h' <= h), @of_item_T h')
                 {struct h}
        : of_productions_T h.
        Proof.
          intros valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          specialize (minimal_maybe_empty_productions__of__maybe_empty_productions' h' (fun h'' pf => minimal_maybe_empty_item__of__maybe_empty_item _ (le_S _ _ pf))).
          pose proof (minimal_maybe_empty_production__of__maybe_empty_production' (fun h'' pf => minimal_maybe_empty_item__of__maybe_empty_item _ (le_S _ _ pf))) as minimal_maybe_empty_production__of__maybe_empty_production''.
          specialize (minimal_maybe_empty_item__of__maybe_empty_item h' (Le.le_n_Sn _)).
          destruct p as [ ? ? p' | ? ? p' ].
          { destruct (fun k => minimal_maybe_empty_production__of__maybe_empty_production'' valid' _ p' k Hinit')
              as [ [p'' H''] | p'' ];
            [ solve [ auto with arith ]
            | left | right ].
            { eexists (MinMaybeEmptyHead _ p'').
              simpl in *.
              apply Le.le_n_S; exact H''. }
            { eapply expand_alt_option; [ .. | eassumption ];
              try solve [ apply Lt.lt_n_Sn
                        | reflexivity ]. } }
          { destruct (minimal_maybe_empty_productions__of__maybe_empty_productions' valid' _ p' (Lt.lt_S_n _ _ H_h) Hinit')
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
        Definition minimal_maybe_empty_item__of__maybe_empty_item_step
                   h
                   (minimal_maybe_empty_item__of__maybe_empty_item
                    : forall h' (pf : h' < h), @of_item_T h')
        : of_item_T h.
        Proof.
          intros valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [nonterminal' H' p'].
          { case_eq (is_valid_nonterminal valid' (of_nonterminal nonterminal')); intro H'''.
            { edestruct (fun k => @minimal_maybe_empty_productions__of__maybe_empty_productions' _ (fun h'' pf => minimal_maybe_empty_item__of__maybe_empty_item _ (Le.le_n_S _ _ pf)) (remove_nonterminal valid' (of_nonterminal nonterminal')) _ p' k)
              as [ [ p'' H'' ] | [ nt'' H'' ] ];
            [ solve [ auto with arith ]
            | left | ].
            { eexists (MinMaybeEmptyNonTerminal _ _ H''' p'').
              apply Le.le_n_S; eassumption. }
            { destruct (string_dec nonterminal' nt''); subst.
              { destruct H'' as [ H'' [ p'' H'''' ] ].
                simpl in *.
                destruct (fun k => minimal_maybe_empty_item__of__maybe_empty_item _ (@reflexivity _ le _ _) valid' _ (MaybeEmptyNonTerminal _ H' p'') k Hinit')
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
                { erewrite <- remove_nonterminal_5
                    by repeat match goal with
                                | _ => eassumption
                                | _ => progress subst
                                | [ H : ?y <> ?x, H' : _ = ?x |- _ ] => destruct (H H')
                                | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
                                | _ => progress destruct_head' and
                                | _ => intro
                                | [ H : ?x <> ?y,
                                        H' : ?e = of_nonterminal ?y |- _ ]
                                  => is_evar e; unify e (of_nonterminal x); revert H'
                                | [ Hsub0 : sub_nonterminals_listT _ _,
                                            H : _ = of_nonterminal _ |- _ ]
                                  => let H' := fresh in
                                     pose proof (f_equal to_nonterminal H) as H';
                                       progress
                                         (rewrite !to_of_nonterminal
                                           in H'
                                           by (apply initial_nonterminals_correct, Hsub0;
                                               first [ assumption
                                                     | rewrite <- H; assumption
                                                     | rewrite -> H; assumption ]));
                                       clear H
                              end.
                  eassumption. }
                { destruct_head sigT.
                  eexists.
                  apply Lt.lt_S; eassumption. } } } }
            { right.
              exists nonterminal'; repeat split; trivial; [].
              exists p'.
              auto with arith. } }
        Defined.

        Definition minimal_maybe_empty_item__of__maybe_empty_item''
        : forall h, of_item_T h.
        Proof.
          apply (Fix Wf_nat.lt_wf).
          exact minimal_maybe_empty_item__of__maybe_empty_item_step.
        Defined.
      End item.

      Definition minimal_maybe_empty_production__of__maybe_empty_production''
                 h
      : of_production_T h
        := @minimal_maybe_empty_production__of__maybe_empty_production' h (fun _ _ => @minimal_maybe_empty_item__of__maybe_empty_item'' _).

      Definition minimal_maybe_empty_productions__of__maybe_empty_productions''
                 h
      : of_productions_T h
        := @minimal_maybe_empty_productions__of__maybe_empty_productions' h (fun _ _ => @minimal_maybe_empty_item__of__maybe_empty_item'' _).

        Definition minimal_maybe_empty_item__of__maybe_empty_item
                   {it : item Char}
                   (p : maybe_empty_item G valid0 it)
        : minimal_maybe_empty_item (G := G) valid0 it.
        Proof.
          pose proof (@minimal_maybe_empty_item__of__maybe_empty_item'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
          apply alt_all_elim in X.
          exact (projT1 X).
        Defined.

        Definition minimal_maybe_empty_production__of__maybe_empty_production
                   {pat : production Char}
                   (p : maybe_empty_production G valid0 pat)
        : minimal_maybe_empty_production (G := G) valid0 pat.
        Proof.
          pose proof (@minimal_maybe_empty_production__of__maybe_empty_production'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
          apply alt_all_elim in X.
          exact (projT1 X).
        Defined.

        Definition minimal_maybe_empty_productions__of__maybe_empty_productions
                   {pats : productions Char}
                   (p : maybe_empty_productions G valid0 pats)
        : minimal_maybe_empty_productions (G := G) valid0 pats.
        Proof.
          pose proof (@minimal_maybe_empty_productions__of__maybe_empty_productions'' _ valid0 _ p (@reflexivity _ le _ _) (reflexivity _)) as X.
          apply alt_all_elim in X.
          exact (projT1 X).
        Defined.


        Definition minimal_maybe_empty_item__iff__maybe_empty_item
                   {it : item Char}
        : inhabited (maybe_empty_item G valid0 it)
          <-> inhabited (minimal_maybe_empty_item (G := G) valid0 it).
        Proof.
          split; intros [H]; constructor;
          [ apply minimal_maybe_empty_item__of__maybe_empty_item
          | eapply maybe_empty_item__of__minimal_maybe_empty_item ];
          try (eassumption || reflexivity).
        Qed.

        Definition minimal_maybe_empty_production__iff__maybe_empty_production
                   {it : production Char}
        : inhabited (maybe_empty_production G valid0 it)
          <-> inhabited (minimal_maybe_empty_production (G := G) valid0 it).
        Proof.
          split; intros [H]; constructor;
          [ apply minimal_maybe_empty_production__of__maybe_empty_production
          | eapply maybe_empty_production__of__minimal_maybe_empty_production ];
          try (eassumption || reflexivity).
        Qed.

        Definition minimal_maybe_empty_productions__iff__maybe_empty_productions
                   {it : productions Char}
        : inhabited (maybe_empty_productions G valid0 it)
          <-> inhabited (minimal_maybe_empty_productions (G := G) valid0 it).
        Proof.
          split; intros [H]; constructor;
          [ apply minimal_maybe_empty_productions__of__maybe_empty_productions
          | eapply maybe_empty_productions__of__minimal_maybe_empty_productions ];
          try (eassumption || reflexivity).
        Qed.
    End wf_parts.
  End minimize.
End cfg.
