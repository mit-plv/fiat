(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.Reachable.AllReachable.
Require Import Fiat.Parsers.Reachable.AllMinimalReachable.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.Reachable.AllReachableWellFounded.
Require Import Fiat.Common.
(*Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Setoids.Setoid Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Wf Coq.Arith.Wf_nat.
Require Import Fiat.Parsers.ContextFreeGrammar Fiat.Parsers.ContextFreeGrammarProperties Fiat.Parsers.WellFoundedParse.
Require Import Fiat.Parsers.CorrectnessBaseTypes Fiat.Parsers.BaseTypes.
Require Export Fiat.Parsers.MinimalParse.
Require Export Fiat.Parsers.WellFoundedParseProperties.
Require Import Fiat.Common Fiat.Common.Le Fiat.Common.Wf.*)

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}.

  Definition reachable_from_item__of__minimal_reachable_from_item'
             {ch}
             (reachable_from_productions__of__minimal_reachable_from_productions
              : forall valid prods,
                  sub_nonterminals_listT valid initial_nonterminals_data
                  -> minimal_reachable_from_productions (G := G) ch valid prods
                  -> reachable_from_productions G ch prods)
             valid it
             (Hsub : sub_nonterminals_listT valid initial_nonterminals_data)
             (H : minimal_reachable_from_item (G := G) ch valid it)
  : reachable_from_item G ch it.
  Proof.
    destruct H; [ left | right ].
    { clear reachable_from_productions__of__minimal_reachable_from_productions; eauto. }
    { eapply reachable_from_productions__of__minimal_reachable_from_productions; [ | eassumption ].
      clear -Hsub rdata'.
      eauto using sub_nonterminals_listT_remove_2. }
  Defined.

  Fixpoint reachable_from_productions__of__minimal_reachable_from_productions
             {ch}
             valid pats
             (Hsub : sub_nonterminals_listT valid initial_nonterminals_data)
             (H : minimal_reachable_from_productions (G := G) ch valid pats)
  : reachable_from_productions G ch pats
  with reachable_from_production__of__minimal_reachable_from_production
             {ch}
             valid pat
             (Hsub : sub_nonterminals_listT valid initial_nonterminals_data)
             (H : minimal_reachable_from_production (G := G) ch valid pat)
  : reachable_from_production G ch pat.
  Proof.
    { destruct H; [ left | right ]; eauto. }
    { destruct H; [ left | right ]; eauto using reachable_from_item__of__minimal_reachable_from_item'. }
  Defined.

  Definition reachable_from_item__of__minimal_reachable_from_item
             {ch}
    := @reachable_from_item__of__minimal_reachable_from_item' ch reachable_from_productions__of__minimal_reachable_from_productions.

  Section expand.
    Definition expand_minimal_reachable_from_item'
               {ch}
               (expand_minimal_reachable_from_productions
                : forall valid valid' prods,
                    sub_nonterminals_listT valid valid'
                    -> minimal_reachable_from_productions (G := G) ch valid prods
                    -> minimal_reachable_from_productions (G := G) ch valid' prods)
               valid valid' it
               (Hsub : sub_nonterminals_listT valid valid')
               (H : minimal_reachable_from_item (G := G) ch valid it)
    : minimal_reachable_from_item (G := G) ch valid' it.
    Proof.
      destruct H; [ left | right ].
      { clear expand_minimal_reachable_from_productions; eauto. }
      { eapply expand_minimal_reachable_from_productions; [ | eassumption ].
        clear -Hsub rdata'.
        eauto using remove_nonterminal_mor. }
    Defined.

    Fixpoint expand_minimal_reachable_from_productions
             {ch}
             valid valid' pats
             (Hsub : sub_nonterminals_listT valid valid')
             (H : minimal_reachable_from_productions (G := G) ch valid pats)
    : minimal_reachable_from_productions (G := G) ch valid' pats
    with expand_minimal_reachable_from_production
           {ch}
           valid valid' pat
           (Hsub : sub_nonterminals_listT valid valid')
           (H : minimal_reachable_from_production (G := G) ch valid pat)
         : minimal_reachable_from_production (G := G) ch valid' pat.
    Proof.
      { destruct H; [ left | right ]; eauto. }
      { destruct H; [ left | right ]; eauto using expand_minimal_reachable_from_item'. }
    Defined.

    Definition expand_minimal_reachable_from_item
               {ch}
      := @expand_minimal_reachable_from_item' ch expand_minimal_reachable_from_productions.
  End expand.

  (*Global Instance minimal_reachable_from_item_Proper {ch}
  : Proper (sub_nonterminals_listT ==> eq ==> impl) (minimal_reachable_from_item (G := G) ch).
  Proof. repeat intro; subst; eapply expand_minimal_reachable_from_item; eauto. Qed.

  Global Instance minimal_reachable_from_production_Proper {ch}
  : Proper (sub_nonterminals_listT ==> eq ==> impl) (minimal_reachable_from_production (G := G) ch).
  Proof. repeat intro; subst; eapply expand_minimal_reachable_from_production; eauto. Qed.

  Global Instance minimal_reachable_from_productions_Proper {ch}
  : Proper (sub_nonterminals_listT ==> eq ==> impl) (minimal_reachable_from_productions (G := G) ch).
  Proof. repeat intro; subst; eapply expand_minimal_reachable_from_productions; eauto. Qed.*)

  Section minimize.
    Context {ch : Char}.

    Let alt_option h valid
      := { nt : _ & (is_valid_nonterminal valid nt = false /\ is_valid_nonterminal initial_nonterminals_data nt)
                    * { p : reachable_from_productions G ch (Lookup G nt)
                            & (size_of_reachable_from_productions p < h) } }%type.

    Lemma not_alt_all {h} (ps : alt_option h initial_nonterminals_data)
    : False.
    Proof.
      destruct ps as [ ? [ H' _ ] ].
      revert H'; clear; intros [? ?].
      congruence.
    Qed.

    Definition alt_all_elim {h T} (ps : T + alt_option h initial_nonterminals_data)
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
               | [ |- sigT _ -> _ ] => intros []
               | [ |- sig _ -> _ ] => intros []
               | [ |- prod _ _ -> _ ] => intros []
               | [ |- and _ _ -> _ ] => intros []
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
          (p : reachable_from_item G ch it)
        := forall (p_small : size_of_reachable_from_item p < h)
                  (pf : sub_nonterminals_listT valid initial_nonterminals_data),
             ({ p' : minimal_reachable_from_item (G := G) ch valid it
                     & (size_of_reachable_from_item (reachable_from_item__of__minimal_reachable_from_item pf p')) <= size_of_reachable_from_item p })%type
             + alt_option (size_of_reachable_from_item p) valid.

      Let of_item_T h
        := forall valid it p, @of_item_T' h valid it p.

      Let of_parse_production_T' h
          (valid : nonterminals_listT) {pat : production Char}
          (p : reachable_from_production G str pat)
        := forall (p_small : size_of_parse_production p < h),
             sub_nonterminals_listT valid initial_nonterminals_data
             -> Forall_reachable_from_production P p
             -> ({ p' : minimal_reachable_from_production (G := G) len0 valid pat
                        & (size_of_parse_production (projT1 (reachable_from_production__of__minimal_reachable_from_production p')) <= size_of_parse_production p)
                          * Forall_reachable_from_production P (projT1 (reachable_from_production__of__minimal_reachable_from_production p')) })%type
                + alt_option (size_of_parse_production p) valid.

      Let of_parse_production_T len0 h
        := forall str pf valid pat p, @of_parse_production_T' h len0 str pf valid pat p.

      Let of_parse_T' h
          {len0} {str : String} (pf : length str <= len0)
          (valid : nonterminals_listT) {pats : productions Char}
          (p : parse_of G str pats)
        := forall (p_small : size_of_parse p < h),
             sub_nonterminals_listT valid initial_nonterminals_data
             -> Forall_parse_of P p
             -> ({ p' : minimal_parse_of (G := G) len0 valid pats
                        & (size_of_parse (projT1 (parse_of__of__minimal_parse_of p')) <= size_of_parse p)
                          * Forall_parse_of P (projT1 (parse_of__of__minimal_parse_of p')) })%type
                + alt_option (size_of_parse p) valid.

      Let of_parse_T len0 h
        := forall str pf valid pats p, @of_parse_T' h len0 str pf valid pats p.

      Let of_parse_nonterminal_T {len0 str valid nonterminal} (p : parse_of G str (Lookup G nonterminal)) h
        := size_of_reachable_from_item (ParseNonTerminal nonterminal p) < h
           -> length str <= len0
           -> sub_nonterminals_listT valid initial_nonterminals_data
           -> Forall_reachable_from_item P (ParseNonTerminal nonterminal p)
           -> ({ p' : minimal_parse_of_nonterminal (G := G) len0 valid nonterminal
                      & (size_of_reachable_from_item (projT1 (reachable_from_item__of__minimal_reachable_from_item (MinParseNonTerminal p'))) <= size_of_reachable_from_item (ParseNonTerminal nonterminal p))
                        * Forall_reachable_from_item P (projT1 (reachable_from_item__of__minimal_reachable_from_item (MinParseNonTerminal p'))) })%type
              + alt_option (size_of_reachable_from_item (ParseNonTerminal nonterminal p)) valid.

      Section item.
        Context {len0 : nat} {str : String} {valid : nonterminals_listT}.

        Definition minimal_reachable_from_item__of__reachable_from_item
                   h
                   (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                    : forall h' (pf : h' < S (S h)) {len0 str valid nonterminal}
                             (p : parse_of G str (Lookup G nonterminal)),
                        @of_parse_nonterminal_T len0 str valid nonterminal p h')
        : of_item_T len0 h.
        Proof.
          intros str' pf valid' pats p H_h Hinit' H_forall.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [ ch pf0 |nonterminal' p'].
          { left.
            eexists (MinimalParse.MinParseTerminal _ _ _ _ pf0);
              split; simpl; constructor. }
          { edestruct (fun pf => @minimal_parse_of_nonterminal__of__parse_of_nonterminal (S h') pf len0 _ valid' _ p') as [ [p'' H''] | p'' ];
            try solve [ repeat (apply Lt.lt_n_Sn || apply Lt.lt_S)
                      | exact Hinit'
                      | exact H_h
                      | exact H_forall
                      | exact pf ];
            [|];
            [ left | right ].
            { exists (MinParseNonTerminal p'').
              simpl in *.
              exact H''. }
            { exact p''. } }
        Defined.
      End item.

      Section production.
        Context {len0 : nat} {str : String} {valid : nonterminals_listT}.

        Local Ltac min_parse_prod_t' :=
          idtac;
          match goal with
            | _ => assumption
            | [ |- ?R ?x ?x ]
              => reflexivity
            | _ => progress destruct_head prod
            | [ H : False |- _ ]
              => solve [ destruct H ]
            | _ => progress simpl
            | _ => progress subst
            | _ => progress rewrite ?parse_of_contract_minimal_reachable_from_item_lt, ?parse_of_contract_minimal_reachable_from_production_lt, ?parse_of_contract_minimal_parse_of_lt
            | [ |- context G[size_of_parse_production (ParseProductionCons ?s ?n ?a ?b)] ]
              => let G' := context G[S (size_of_reachable_from_item a + size_of_parse_production b)] in
                 change G'
            | [ H : alt_option _ initial_nonterminals_data _ |- _ ]
              => apply not_alt_all in H
            | [ p0 : minimal_reachable_from_item ?ns' ?v (take ?n ?s) ?pat,
                     p1 : minimal_reachable_from_production ?ns' ?v (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns'
                |- ({ p' : minimal_reachable_from_production ?ns' ?v ?s (?pat :: ?pats) & _ } + _)%type ]
              => left; exists (MinParseProductionCons _ n H p0 p1)
            | [ p0 : minimal_reachable_from_item ?ns' _ (take ?n ?s) ?pat,
                     p1 : minimal_reachable_from_production ?ns' ?v (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns'
                |- ({ p' : minimal_reachable_from_production ?ns' ?v ?s (?pat :: ?pats) & _ } + _)%type ]
              => let H' := fresh in
                 assert (H' : length (take n s) < ns')
                   by (rewrite <- H, ?take_short_length by omega; omega);
                   left; exists (MinParseProductionCons
                                   _
                                   n
                                   H
                                   (contract_minimal_reachable_from_item_lt (valid' := v) H' p0)
                                   p1)
            | [ p0 : minimal_reachable_from_item ?ns' ?v (take ?n ?s) ?pat,
                     p1 : minimal_reachable_from_production ?ns' _ (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns'
                |- ({ p' : minimal_reachable_from_production ?ns' ?v ?s (?pat :: ?pats) & _ } + _)%type ]
              => let H' := fresh in
                 assert (H' : length (drop n s) < ns')
                   by (rewrite <- H, drop_length; omega);
                   left; exists (MinParseProductionCons
                                   _
                                   n
                                   H
                                   p0
                                   (contract_minimal_reachable_from_production_lt (valid' := v) H' p1))
            | [ p0 : minimal_reachable_from_item ?ns' _ (take ?n ?s) ?pat,
                     p1 : minimal_reachable_from_production ?ns' _ (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns',
                              H' : ?n < length ?s,
                                   H'' : 0 < ?n
                |- ({ p' : minimal_reachable_from_production ?ns' ?v ?s (?pat :: ?pats) & _ } + _)%type ]
              => let H0' := fresh in
                 let H1' := fresh in
                 assert (H1' : length (drop n s) < ns')
                   by (rewrite <- H, drop_length; omega);
                   assert (H0' : length (take n s) < ns')
                   by (rewrite <- H, ?take_short_length by omega; omega);
                   left; eexists (MinParseProductionCons
                                    _
                                    n
                                    H
                                    (contract_minimal_reachable_from_item_lt (valid' := v) H0' p0)
                                    (contract_minimal_reachable_from_production_lt (valid' := v) H1' p1))
            | [ |- (_ * _)%type ]
              => split
            | [ H : _ <= _ |- _ <= _ ] => apply H
            | _ => apply Le.le_n_S
            | _ => apply Plus.plus_le_compat
            | [ H0 : Forall_reachable_from_item _ _,
                     H1 : Forall_reachable_from_production _ _
                |- Forall_reachable_from_production _ _ ]
              => exact (H0, H1)
            | [ H : alt_option _ ?v (drop 0 ?x)
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v (drop ?n ?x), H' : length ?x <= ?n
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v (take ?n ?x), H' : length ?x = ?n
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v (take ?n ?x), H' : length ?x <= ?n
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            (*| [ H : alt_option _ ?v ?x
                |- (_ + alt_option _ ?v (Empty _ ++ ?x))%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]*)
            (*| [ |- _ = _ ]
              => progress rewrite ?LeftId, ?RightId*)
            | [ H : length ?s = 0 |- beq _ ?s ] => apply bool_eq_empty
            | [ H : length ?s = 0 |- beq ?s _ ] => apply bool_eq_empty
            | _ => rewrite take_short_length by assumption
            | _ => rewrite take_long by assumption
            | [ H : context[min _ _] |- _ ] => rewrite min_l in H by assumption
            | [ H : context[min _ _] |- _ ] => rewrite min_r in H by assumption
            | [ H : context[min _ _] |- _ ] => rewrite min_l in H by omega
            | [ H : context[min _ _] |- _ ] => rewrite min_r in H by omega
            | _ => rewrite drop_length
            | _
              => solve [ eauto using le_S, Le.le_trans, Plus.le_plus_l, Plus.le_plus_r, drop_0, take_long, NPeano.Nat.eq_le_incl, bool_eq_empty, drop_length, (fun x y => proj2 (NPeano.Nat.sub_0_le x y)) with nocore ]
          end.
        (*Local Ltac min_parse_prod_pose_t' :=
          idtac;
          match goal with
            | [ H : ?a <> Empty _,
                    H' : ?a ++ _ ≤s _ |- _ ]
              => unique pose proof (strle_to_lt_nonempty_r H H')
            | [ H : ?a <> Empty _,
                    H' : _ ++ ?a ≤s _ |- _ ]
              => unique pose proof (strle_to_lt_nonempty_l H H')
          end.*)
        (*Local Ltac min_parse_prod_pose_t := repeat min_parse_prod_pose_t'.*)
        Local Ltac min_parse_prod_t := repeat min_parse_prod_t'.

        (** This is the proof where we pay the proof for conceptual
            mismatch.  We are, conceptually, simultaneously
            "minimizing parse trees" and "producing parse traces".  It
            is marginally nicer(!!) to contain the ugliness in this
            single proof, rather than have it infect everything.  So
            we must conceptually minimize the passed parse tree while
            in fact building a trace of the parse algorithm.  To do
            this, in the cons case, we need to figure out how we're
            decreasing.  According with conceptual minimization, when
            we have parsed [s0 ++ s1] as a cons of [p0] and [p1],
            having a smaller parse tree for, say [s0], with any other
            pattern, does us no good, unless [s1] is empty (and [s0 =
            s0 ++ s1]), when we can simply pass that smaller parse up
            the function call tree.  So we must eliminate the
            "alternate" option, by expanding the valid list to the
            initial data.  Luckily(?!), in the case where [s1] is
            non-empty, [s0] is strictly smaller than [s0 ++ s1], and
            thus we can rebuild the minimal parse tree to contract it.
            This, finally, allows us to either build a minimal parse
            tree for the thing we are asked about (or to contract the
            "alternate option" parse tree, passing it back up?). *)

        Fixpoint minimal_reachable_from_production__of__reachable_from_production
                 h
                 (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                  : forall h' (pf : h' < S (S h)) {len0 str valid nonterminal}
                           (p : parse_of G str (Lookup G nonterminal)),
                      @of_parse_nonterminal_T len0 str valid nonterminal p h')
                 {struct h}
        : of_parse_production_T len0 h.
        Proof.
          intros str' pf valid' pats p H_h Hinit' H_forall.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [ pf0' | n pat' pats' p0' p1' ].
          { clear minimal_reachable_from_production__of__reachable_from_production.
            left.
            eexists (@MinimalParse.MinParseProductionNil _ _ _ _ _ _ _ pf0');
              repeat (reflexivity || esplit). }
          { specialize (fun h' pf
                        => @minimal_parse_of_nonterminal__of__parse_of_nonterminal
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            change (S ((size_of_reachable_from_item p0')
                       + (size_of_parse_production p1'))
                    < S h') in H_h.
            apply Lt.lt_S_n in H_h.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_l _ _) H_h) as H_h0.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_r _ _) H_h) as H_h1.
            clear H_h.
            assert (pf0' : length (take n str') <= length str')
              by (rewrite take_length; apply Min.min_case_strong; omega).
            assert (pf1' : length (drop n str') <= length str')
              by (rewrite drop_length; omega).
            pose proof (fun valid Hinit => @minimal_reachable_from_item__of__reachable_from_item _ h'  minimal_parse_of_nonterminal__of__parse_of_nonterminal _ (transitivity pf0' pf) valid _ p0' H_h0 Hinit (fst H_forall)) as p_it.
            pose proof (fun valid Hinit => @minimal_reachable_from_production__of__reachable_from_production h' minimal_parse_of_nonterminal__of__parse_of_nonterminal _ (transitivity pf1' pf) valid _ p1' H_h1 Hinit (snd H_forall)) as p_prod.
            clear pf0' pf1'.
            destruct (le_lt_dec (length str') n) as [ Hle | Hle ], (zerop (min n (length str'))) as [Hstr' | Hstr' ].
            { (* empty, empty *)
              rewrite Min.min_r in Hstr' by assumption.
              specialize (p_it valid' Hinit'); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* nonempty, empty *)
              specialize (p_it valid' Hinit'); specialize (p_prod initial_nonterminals_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* empty, nonempty *)
              specialize (p_it initial_nonterminals_data (reflexivity _)); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* nonempty, nonempty *)
              specialize (p_it initial_nonterminals_data (reflexivity _)); specialize (p_prod initial_nonterminals_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. } }
        Defined.
      End production.

      Section productions.
        Context {len0 : nat} {str : String} {valid : nonterminals_listT}.

        Fixpoint minimal_reachable_from_productions__of__reachable_from_productions
                 h
                 (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                  : forall h' (pf : h' < S h) {len0 str valid nonterminal}
                           (p : parse_of G str (Lookup G nonterminal)),
                      @of_parse_nonterminal_T len0 str valid nonterminal p h')
                 {struct h}
        : of_parse_T len0 h.
        Proof.
          intros str' pf valid' pats p H_h Hinit' H_forall.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [pat pats p' | pat pats p'].
          { clear minimal_reachable_from_productions__of__reachable_from_productions.
            edestruct (@minimal_reachable_from_production__of__reachable_from_production _ h' minimal_parse_of_nonterminal__of__parse_of_nonterminal _ pf valid' _ p') as [ [p'' p''H] | [nonterminal' H'] ];
            try solve [ exact (Lt.lt_S_n _ _ H_h)
                      | exact H_forall
                      | exact Hinit' ];
            [|].
            { left.
              exists (MinParseHead pats p'').
              simpl.
              split;
                solve [ exact (Le.le_n_S _ _ (fst p''H))
                      | exact (snd p''H) ]. }
            { right.
              exists nonterminal'.
              split;
                try solve [ exact (fst H') ];
                [].
              exists (projT1 (snd H'));
                split;
                try solve [ exact (snd (projT2 (snd H')))
                          | exact (Lt.lt_S _ _ (fst (projT2 (snd H')))) ]. } }
          { specialize (fun h' pf
                        => @minimal_parse_of_nonterminal__of__parse_of_nonterminal
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            edestruct (minimal_reachable_from_productions__of__reachable_from_productions h'  minimal_parse_of_nonterminal__of__parse_of_nonterminal _ pf valid' _ p') as [ [p'' p''H] | [nonterminal' H'] ];
            try solve [ exact (Lt.lt_S_n _ _ H_h)
                      | exact Hinit'
                      | exact H_forall ];
            [|].
            { left.
              exists (MinParseTail pat p'').
              simpl.
              split;
                solve [ exact (Le.le_n_S _ _ (fst p''H))
                      | exact (snd p''H) ]. }
            { right.
              exists nonterminal'.
              split;
                try solve [ exact (fst H') ];
                [].
              exists (projT1 (snd H'));
                split;
                try solve [ exact (snd (projT2 (snd H')))
                          | exact (Lt.lt_S _ _ (fst (projT2 (snd H')))) ]. } }
        Defined.
      End productions.

      Section nonterminal.
        Section step.
          Definition minimal_parse_of_nonterminal__of__parse_of_nonterminal_step
                     h
                     (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                      : forall h' (pf : h' < h) {len0 str valid nonterminal}
                               (p : parse_of G str (Lookup G nonterminal)),
                          @of_parse_nonterminal_T len0 str valid nonterminal p h')
                     {len0 str valid nonterminal}
                     (p : parse_of G str (Lookup G nonterminal))
          : @of_parse_nonterminal_T len0 str valid nonterminal p h.
          Proof.
            destruct h as [|h]; [ clear; repeat intro; exfalso; omega | ].
            intros pf Hstr Hinit' H_forall.
            let H := match goal with H : length str <= len0 |- _ => constr:H end in

            destruct (le_lt_eq_dec _ _ H) as [pf_lt|pf_eq].
            { (** [str] got smaller, so we reset the valid nonterminals list *)
              destruct (@minimal_reachable_from_productions__of__reachable_from_productions (length str) h minimal_parse_of_nonterminal__of__parse_of_nonterminal str (reflexivity _) initial_nonterminals_data (Lookup G nonterminal) p (Lt.lt_S_n _ _ pf) (reflexivity _) (snd H_forall)) as [p'|p'].
              { left.
                exists (MinParseNonTerminalStrLt valid _ pf_lt (fst H_forall) (projT1 p'));
                  simpl.
                simpl in *.
                split;
                  [ exact (Le.le_n_S _ _ (fst (projT2 p')))
                  | split;
                    [ exact (fst H_forall)
                    | exact (snd (projT2 p')) ] ]. }
              { simpl.
                right; eapply expand_alt_option; [..| exact p' ];
                solve [ apply Lt.lt_n_Sn
                      | assumption
                      | reflexivity ]. } }
            { (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
              destruct (Sumbool.sumbool_of_bool (is_valid_nonterminal valid nonterminal)) as [ Hvalid | Hinvalid ].
              { destruct (@minimal_reachable_from_productions__of__reachable_from_productions len0 h minimal_parse_of_nonterminal__of__parse_of_nonterminal str Hstr (remove_nonterminal valid nonterminal) (Lookup G nonterminal) p (Lt.lt_S_n _ _ pf) (transitivity (R := sub_nonterminals_listT) (@sub_nonterminals_listT_remove _ _ _ _) Hinit') (snd H_forall)) as [p'|p'].
                { left.
                  exists (@MinimalParse.MinParseNonTerminalStrEq _ _ _ _ _ _ _ _ pf_eq (fst H_forall) Hvalid (projT1 p')).
                  simpl in *.
                  split;
                    [ exact (Le.le_n_S _ _ (fst (projT2 p')))
                    | split;
                      [ exact (fst H_forall)
                      | exact (snd (projT2 p')) ] ]. }
                { destruct p' as [nonterminal' p'].
                  destruct (string_dec nonterminal nonterminal') as [|n].
                  { subst nonterminal; simpl in *.
                    edestruct (@minimal_parse_of_nonterminal__of__parse_of_nonterminal (S (size_of_parse p)) pf len0 _ valid nonterminal' (projT1 (snd p'))) as [p''|p''];
                    try solve [ apply Lt.lt_n_S, (fst (projT2 (snd p')))
                              | subst; reflexivity
                              | assumption
                              | split; [ exact (proj2 (fst p'))
                                       | exact (snd (projT2 (snd p'))) ] ];
                    [|].
                    { left.
                      exists (projT1 p'').
                      split.
                      { etransitivity;
                        [ exact (fst (projT2 p''))
                        | exact (Lt.lt_le_weak _ _ (Lt.lt_n_S _ _ (fst (projT2 (snd p'))))) ]. }
                      { exact (snd (projT2 p'')). } }
                    { right.
                      exists (projT1 p'').
                      split;
                        [ exact (fst (projT2 p''))
                        | ].
                      exists (projT1 (snd (projT2 p''))).
                      split;
                        [ etransitivity;
                          [ exact (fst (projT2 (snd (projT2 p''))))
                          | exact (Lt.lt_n_S _ _ (fst (projT2 (snd p')))) ]
                        | exact (snd (projT2 (snd (projT2 p'')))) ]. } }
                  { right.
                    exists nonterminal'.
                    destruct p' as [p'H p'p].
                    split.
                    { rewrite remove_nonterminal_5 in p'H by assumption.
                      exact p'H. }
                    { exists (projT1 p'p).
                      split; [ exact (Lt.lt_S _ _ (fst (projT2 p'p)))
                             | exact (snd (projT2 p'p)) ]. } } } }
              { (** oops, we already saw this nonterminal in the past.  ABORT! *)
                right.
                exists nonterminal.
                destruct H_forall.
                split; [ split; assumption
                       | ].
                exists p.
                split; solve [ assumption
                             | apply Lt.lt_n_Sn ]. } }
          Defined.
        End step.

        Section wf.
          Definition minimal_parse_of_nonterminal__of__parse_of_nonterminal
          : forall h
                   {len0 str valid nonterminal}
                   (p : parse_of G str (Lookup G nonterminal)),
              @of_parse_nonterminal_T len0 str valid nonterminal p h
            := @Fix
                 _ lt lt_wf
                 (fun h => forall {len0 str valid nonterminal}
                                  (p : parse_of G str (Lookup G nonterminal)),
                             @of_parse_nonterminal_T len0 str valid nonterminal p h)
                 (@minimal_parse_of_nonterminal__of__parse_of_nonterminal_step).
        End wf.
      End nonterminal.
    End wf_parts.
  End minimize.
End cfg.
