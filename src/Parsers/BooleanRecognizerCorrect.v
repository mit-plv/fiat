(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar Fiat.Parsers.BooleanRecognizer Fiat.Parsers.MinimalParse.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Splitters.RDPList Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammarProperties Fiat.Parsers.WellFoundedParse.
Require Import Fiat.Common Fiat.Common.Wf.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ContextFreeGrammarValid Fiat.Parsers.ContextFreeGrammarValidProperties.
Require Import Coq.Logic.Eqdep_dec.
Require Import Fiat.Common.List.ListFacts.

Local Hint Extern 0 =>
match goal with
  | [ H : false = true |- _ ] => solve [ destruct (Bool.diff_false_true H) ]
  | [ H : true = false |- _ ] => solve [ destruct (Bool.diff_true_false H) ]
end.

Local Open Scope string_like_scope.

Section sound.
  Section general.
    Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).
    Context {data : @boolean_parser_dataT Char _}
            {cdata : @boolean_parser_completeness_dataT' Char _ G data}
            {rdata : @parser_removal_dataT' predata}.

    Let P : String.string -> Prop
      := fun p => is_valid_nonterminal initial_nonterminals_data p.

    Let P' : item Char -> Prop
      := fun it => match it with
                     | NonTerminal nt => P nt
                     | Terminal _ => true
                   end.

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      Section item.
        Context (str : String)
                (str_matches_nonterminal : String.string -> bool).

        Definition str_matches_nonterminal_soundT
          := forall nt,
               (*is_valid_nonterminal initial_nonterminals_data nt
               ->*) str_matches_nonterminal nt
               -> { p : parse_of_item G str (NonTerminal nt)
                        & Forall_parse_of_item (fun _ => P) p }.

        Definition str_matches_nonterminal_completeT P len0
          := forall (valid : nonterminals_listT) nonterminal (H_sub : P len0 valid nonterminal),
               minimal_parse_of_item (G := G) len0 valid str (NonTerminal nonterminal)
               -> str_matches_nonterminal nonterminal.

        Lemma parse_item_sound'
              (str_matches_nonterminal_sound : str_matches_nonterminal_soundT)
              (it : item Char)
        : parse_item' str_matches_nonterminal str it
          -> { p : parse_of_item G str it
                   & Forall_parse_of_item (fun _ => P) p }.
        Proof.
          unfold parse_item', str_matches_nonterminal_soundT in *.
          repeat match goal with
                   | _ => intro
                   | [ H : context[match ?E with _ => _ end] |- _ ] => atomic E; destruct E
                   | [ |- context[match ?E with _ => _ end] ] => atomic E; destruct E
                   | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                   | [ H : context[match ?E with _ => _ end] |- context[?E] ] => destruct E
                   | _ => progress (simpl in *; subst)
                   | [ H : is_true (_ ~= [ _ ]) |- sigT _ ] => eexists (ParseTerminal _ _ _ H)
                   | [ |- unit ] => constructor
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | [ H : _ /\ _ |- _ ] => destruct H
                   | _ => progress unfold is_true in *
                   | _ => solve [ eauto ]
                 end.
        Defined.

        Lemma parse_item_complete'
              len0
              valid Pv
              (str_matches_nonterminal_complete : str_matches_nonterminal_completeT Pv len0)
              (it : item Char)
              (Hinit : forall nonterminal,
                         minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
                         -> Pv len0 valid nonterminal)
        : minimal_parse_of_item (G := G) len0 valid str it
          -> parse_item' str_matches_nonterminal str it.
        Proof.
          unfold parse_item', str_matches_nonterminal_completeT in *.
          repeat
            repeat
            match goal with
              | _ => intro
              | _ => reflexivity
              | _ => eassumption
              | _ => progress subst
              | _ => progress unfold is_true in *
              | [ |- _ /\ _ ] => split
              | [ |- ?x < ?x \/ _ ] => right
              | [ H : ?T |- ?T \/ _ ] => left; exact H
              | [ |- ?x = ?x \/ _ ] => left; reflexivity
              | [ |- _ \/ ?x = ?x ] => right; reflexivity
              | [ |- _ = true ] => apply bool_eq_correct
              | [ |- (_ && _)%bool = true ] => apply Bool.andb_true_iff
              | [ H : context[?E] |- context[match ?E with _ => _ end] ] => destruct E
              | [ H : minimal_parse_of _ _ _ [] |- _ ] => solve [ inversion H ]
              | [ |- str_matches_nonterminal _ = true ]
                => eapply str_matches_nonterminal_complete; [..| eassumption ]
              | [ H : minimal_parse_of_item _ _ _ (Terminal _) |- _ ] => inversion H; clear H
              | [ H : minimal_parse_of_item _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
              | [ H : forall nonterminal, _ -> Pv _ _ nonterminal |- Pv _ _ _ ] => eapply H
              | [ H : minimal_parse_of_nonterminal _ _ _ _ |- _ ] => inversion H; clear H
          end.
        Qed.
      End item.

      Section item_ext.
        Lemma parse_item_ext
              (str : String)
              (str_matches_nonterminal1 str_matches_nonterminal2 : String.string -> bool)
              (it : item Char)
              (ext : forall x, str_matches_nonterminal1 x = str_matches_nonterminal2 x)
        : parse_item' str_matches_nonterminal1 str it
          = parse_item' str_matches_nonterminal2 str it.
        Proof.
          unfold parse_item'.
          destruct it; trivial; rewrite ext; trivial.
        Qed.
      End item_ext.

      Section production.
        Context (len0 : nat)
                (parse_nonterminal : forall (str : String) (len : nat),
                                len <= len0
                                -> String.string
                                -> bool).

        Definition parse_nonterminal_soundT
          := forall str len (Hlen : length str = len) pf nt,
               (*is_valid_nonterminal initial_nonterminals_data nt
               ->*) @parse_nonterminal str len pf nt
               -> { p : parse_of_item G str (NonTerminal nt)
                        & Forall_parse_of_item (fun _ => P) p }.

        Definition parse_nonterminal_completeT P
          := forall valid (str : String) len (Hlen : length str = len) pf nonterminal (H_sub : P len0 valid nonterminal),
               minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
               -> @parse_nonterminal str len pf nonterminal.

        Lemma parse_production_sound'
                 (parse_nonterminal_sound : parse_nonterminal_soundT)
                 (str : String) (len : nat) (Hlen : length str = len)
                 (pf : len <= len0)
                 (its : production Char)
        : parse_production' parse_nonterminal str pf its
          -> { p : parse_of_production G str its
                   & Forall_parse_of_production (fun _ => P) p }.
        Proof.
          revert str len Hlen pf; induction its;
          repeat match goal with
                   | _ => intro
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => solve [ auto ]
                   | [ H : appcontext[fold_left] |- _ ] => rewrite (@fold_symmetric _ _ Bool.orb_assoc Bool.orb_comm) in H
                   | [ H : is_true (fold_right orb false (map _ _)) |- _ ] => apply fold_right_orb_map_sig1 in H
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | _ => progress destruct_head sumbool
                   | _ => progress destruct_head and
                   | _ => progress destruct_head prod
                   | _ => progress destruct_head sig
                   | _ => progress destruct_head @StringWithSplitState
                   | _ => progress simpl in *
                   | _ => progress subst
                   | [ H : is_true false |- _ ] => exfalso; clear -H; hnf in H; congruence
                   | [ H : is_true (beq_nat _ _) |- _ ] => apply beq_nat_true_iff in H
                   | [ H : context[NPeano.Nat.eq_dec ?x ?y] |- _ ] => destruct (NPeano.Nat.eq_dec x y)
                   | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
                   | [ H : (_ =s _) = true |- _ ]
                     => let H' := fresh in
                        pose proof H as H';
                          apply bool_eq_correct in H';
                          progress subst
                   | [ H : length ?str = 0 |- { p : parse_of_production ?G ?str nil & _ } ] => exists (ParseProductionNil G str H)
                   | [ |- ?x ] => not has_evar x; solve [ constructor ]
                   | _ => progress specialize_by assumption
                   | [ H : forall x y, y = _ -> _ |- _ ] => specialize (fun x => H x _ eq_refl)
                   | [ H : forall x y, _ = y -> _ |- _ ] => specialize (fun x => H x _ eq_refl)
                   | [ H : forall x y, is_true (parse_production' _ x _ _) -> _, H' : parse_production' _ ?str _ _ = true |- _ ]
                     => specialize (H str)
                   | [ H : forall y, is_true (parse_production' _ ?str y _) -> _, H' : parse_production' _ ?str ?pf _ = true |- _ ]
                     => specialize (H pf)
                   | [ H : context[length (drop _ _)] |- _ ] => rewrite drop_length in H
                 end.
          { match goal with
              | [ H : parse_item' _ _ _ = true |- _ ] => apply parse_item_sound' in H; try eassumption
            end.
            { destruct_head sigT.
              eexists (ParseProductionCons _ _ _ _).
              split; eassumption. }
            { hnf in parse_nonterminal_sound |- *.
              eapply parse_nonterminal_sound.
              rewrite take_length; repeat apply Min.min_case_strong; omega. } }
        Defined.

        Lemma parse_production_complete'
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT Pv)
              (Hinit : forall str len (Hlen : length str = len) (pf : len <= len0) nonterminal,
                         minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
                         -> Pv len0 valid nonterminal)
              (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0)
              (prod : production Char)
              (split_string_for_production_complete'
               : forall len0 valid str (pf : length str <= len0),
                   Forall_tails
                     (fun prod' =>
                        match prod' return Type with
                          | nil => True
                          | it::its => split_list_completeT (G := G) (valid := valid) (len0 := len0) it its str pf (split_string_for_production it its str)
                        end)
                     prod)
        : minimal_parse_of_production (G := G) len0 valid str prod
          -> parse_production' parse_nonterminal str pf prod.
        Proof.
          revert valid str len Hlen Hinit pf; induction prod;
          [
          | specialize (IHprod (fun len0 valid str pf => snd (split_string_for_production_complete' len0 valid str pf))) ];
          repeat match goal with
                   | _ => intro
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => solve [ auto ]
                   | [ H : appcontext[fold_left] |- _ ] => rewrite (@fold_symmetric _ _ Bool.orb_assoc Bool.orb_comm) in H
                   | [ |- appcontext[fold_left] ] => rewrite (@fold_symmetric _ _ Bool.orb_assoc Bool.orb_comm)
                   | [ H : is_true (fold_right orb false (map _ _)) |- _ ] => apply fold_right_orb_map_sig1 in H
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | [ H : minimal_parse_of_production _ _ _ nil |- _ ] => inversion_clear H
                   | [ |- context[NPeano.Nat.eq_dec ?x ?y] ] => destruct (NPeano.Nat.eq_dec x y)
                   | _ => progress destruct_head_hnf sumbool
                   | _ => progress destruct_head_hnf and
                   | _ => progress destruct_head_hnf sig
                   | _ => progress destruct_head_hnf sigT
                   | _ => progress destruct_head_hnf Datatypes.prod
                   | _ => progress simpl in *
                   | _ => progress subst
                   | [ H : minimal_parse_of_production _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ n : nat, H : length ?s <= _ |- context[split_string_for_production ?it ?p ?s] ]
                     => let H' := fresh in
                        pose proof
                             (fun v p0 p1
                              => fst (@split_string_for_production_complete' _ v s H) (existT _ n (p0, p1))) as H';
                          clear split_string_for_production_complete';
                          simpl in H'
                   | [ H : ?a -> ?b, H' : ?a |- _ ] => specialize (H H')
                   | [ H : forall (v : nonterminals_listT) (x : @?a v), @?b v x |- _ ]
                     => pose proof (H valid); pose proof (H initial_nonterminals_data); clear H
                   | [ |- is_true (fold_right orb false (map _ _)) ] => apply fold_right_orb_map_sig2
                   | [ H : minimal_parse_of_item _ _ _ _ |- _ ] => inversion H; clear H; subst
                   | [ |- is_true (beq_nat _ _) ] => apply beq_nat_true_iff
                 end;
          (lazymatch goal with
            | [ H : In ?n (split_string_for_production ?it ?prod ?str)
                |- { x : nat | _ } ]
              => exists n; split; [ exact H | ]
          end);
          repeat match goal with
                   | _ => split
                   | [ |- (_ && _)%bool = true ] => apply Bool.andb_true_iff
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
                   | [ |- In _ (combine_sig _) ] => apply In_combine_sig
                   | _ => progress specialize_by assumption
                   | _ => progress specialize_by ltac:(constructor; assumption)
                   | [ IHprod : _ |- _ ] => eapply IHprod; try eassumption; rewrite ?drop_length, ?take_length; omega
                   | [ H : minimal_parse_of_nonterminal _ _ _ ?nt |- is_valid_nonterminal _ ?nt = true ]
                     => inversion H; assumption
                 end;
          [].
          eapply parse_nonterminal_complete; [..| eassumption ]; simpl;
          repeat match goal with
                   | _ => eassumption
                   | _ => reflexivity
                   | _ => rewrite drop_length
                   | _ => rewrite take_length
                   | _ => omega
                   | [ |- Pv _ _ _ ] => eapply Hinit; [ .. | eassumption ]
                   | _ => etransitivity; [ | eassumption ];
                          solve [ apply str_le_take
                                | apply str_le_drop ]
                   | _ => apply Min.min_case_strong
                 end.
        Qed.
      End production.

      Section production_ext.

        Lemma parse_production_drop_ext
              len0
              (parse_nonterminal1 parse_nonterminal2 : forall (str : String) (len : nat),
                                           len <= len0
                                           -> String.string
                                           -> bool)
              (str : String) (len : nat) (pf : len <= len0) (prod : production Char)
              ms
              (ext : forall n ms len' pf' nonterminal',
                       parse_nonterminal1 (take n (fold_right drop str ms)) len' pf' nonterminal'
                       = parse_nonterminal2 (take n (fold_right drop str ms)) len' pf' nonterminal')
        : parse_production' parse_nonterminal1 (fold_right drop str ms) pf prod
          = parse_production' parse_nonterminal2 (fold_right drop str ms) pf prod.
        Proof.
          revert ms len pf.
          induction prod as [|? ? IHprod]; simpl; intros; try reflexivity; [].
          f_equal.
          apply map_ext; intros.
          apply f_equal2; [ apply parse_item_ext | apply (IHprod (_::_)) ].
          intros; apply ext.
        Qed.

        Lemma parse_production_ext
              len0
              (parse_nonterminal1 parse_nonterminal2 : forall (str : String) (len : nat),
                                           len <= len0
                                           -> String.string
                                           -> bool)
              (str : String) (len : nat) (pf : len <= len0) (prod : production Char)
              (ext : forall str' len' pf' nonterminal',
                       parse_nonterminal1 str' len' pf' nonterminal'
                       = parse_nonterminal2 str' len' pf' nonterminal')
        : parse_production' parse_nonterminal1 str pf prod
          = parse_production' parse_nonterminal2 str pf prod.
        Proof.
          change str with (fold_right drop str nil).
          apply parse_production_drop_ext.
          intros; apply ext.
        Qed.
      End production_ext.

      Section productions.
        Context len0
                (parse_nonterminal : forall (str : String) (len : nat),
                                len <= len0
                                -> String.string
                                -> bool).

        Local Ltac parse_productions_t' :=
          idtac;
          match goal with
            | _ => intro
            | _ => progress unfold is_true in *
            | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
            | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
            | [ |- (_ || _)%bool = true ] => apply Bool.orb_true_iff
            | _ => progress destruct_head_hnf sumbool
            | _ => progress destruct_head_hnf and
            | _ => progress destruct_head_hnf sig
            | _ => progress destruct_head_hnf sigT
            | _ => progress destruct_head_hnf Datatypes.prod
            | _ => progress simpl in *
            | _ => progress specialize_by assumption
            | [ H : context[map _ (map _ _)] |- _ ] => rewrite !map_map in H
            | [ H : fold_right orb false _ = true |- _ ] => apply fold_right_orb_map in H
            | [ H : parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
            | [ H : parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
            | [ H : minimal_parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
            | [ H : minimal_parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
            | [ H : parse_production' _ _ _ _ = true |- _ ] => apply parse_production_sound' in H; try eassumption; try exact eq_refl; []
            | _ => left; eapply parse_production_complete'; (eassumption || reflexivity)
            | [ H : ?A -> ?B |- ?A ] => clear H
            | [ H : option_rect _ _ _ ?x = true |- _ ] => destruct x eqn:?; simpl in H
            | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
            | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
            | [ H : match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?
            | [ H : parse_of_production _ _ ?p |- { p' : parse_of _ _ (?p :: ?ps) & _ } ]
              => exists (ParseHead ps H); assumption
            | [ H : parse_of _ _ ?ps |- { p' : parse_of _ _ (?p :: ?ps) & _ } ]
              => exists (ParseTail p H); assumption
            | _ => progress unfold value, error in *
            | _ => progress subst
            | [ H : forall y, Some _ = Some _ -> _ |- _ ] => specialize (fun y p => H y (f_equal Some p))
            | [ H : forall y, y = _ -> _ |- _ ] => specialize (H _ eq_refl)
            | [ H : forall y, _ = y -> _ |- _ ] => specialize (H _ eq_refl)
            | _ => discriminate
            | _ => solve [ eauto ]
          end.

        Local Ltac parse_productions_t := repeat parse_productions_t'.

        Lemma parse_productions_of_nonterminal_sound'
                 (parse_nonterminal_sound : parse_nonterminal_soundT parse_nonterminal)
                 (str : String) (len : nat) (Hlen : length str = len)
                 (pf : len <= len0)
                 (nt : String.string)
        : parse_productions' parse_nonterminal str pf (Lookup G nt)
          -> { p : parse_of G str (Lookup G nt)
                   & Forall_parse_of (fun _ => P) p }.
        Proof.
          subst.
          unfold parse_productions'; simpl.
          intro H'.
          rewrite !map_map in H'.
          apply fold_right_orb_map in H'.
          apply Exists_exists_dec in H'; [ | decide equality ].
          destruct H' as [n [_ H']].
          repeat match goal with
                   | [ H : option_rect _ _ _ ?x = true |- _ ] => destruct x eqn:?; simpl in H
                   | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                   | _ => progress subst
                   | _ => discriminate
                 end.
          match goal with
            | [ p : production Char |- _ ] => generalize dependent p
          end.
          generalize dependent (G nt); induction n as [|n IHn].
          { parse_productions_t. }
          { intros [|p ps] p'; [ | specialize (IHn ps p') ]; simpl; intros.
            { parse_productions_t. }
            { parse_productions_t. } }
        Defined.

        Lemma parse_productions_of_nonterminal_complete'
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT parse_nonterminal Pv)
              (Hinit : forall str len (Hlen : length str = len) (pf : len <= len0) nonterminal,
                         minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
                         -> Pv len0 valid nonterminal)
              (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0)
              (nt : String.string)
              (Hvalid : P nt)
        : minimal_parse_of (G := G) len0 valid str (Lookup G nt)
          -> parse_productions' parse_nonterminal str pf (Lookup G nt).
        Proof.
          subst.
          unfold parse_productions'; simpl.
          intro H'.
          rewrite !map_map.
          apply fold_right_orb_map.
          apply Exists_exists_dec; [ decide equality | ].
          pose proof (select_production_rules_complete (valid := valid) pf _ Hvalid H') as select_production_rules_complete'.
          destruct select_production_rules_complete' as [ n [ Hn [ its [ H0 H1 ] ] ] ].
          exists n; split; [ assumption | ].
          rewrite H0; simpl.

          eapply parse_production_complete'; [ .. | eassumption ]; try eassumption; try reflexivity; [].
          intros len1 valid1 str1 pf1.
          pose proof (split_string_for_production_complete valid1 _ pf1 _ Hvalid) as split_string_for_production_complete'.
          clear -H0 split_string_for_production_complete'.
          match goal with
              | [ H : ForallT ?f ?x |- ?f' ?y ]
                => change f' with f;
                  generalize dependent f
          end.
          generalize dependent (G nt); induction n.
          { intros []; simpl; intros; inversion H0; subst; intuition. }
          { intros []; simpl; intros; try discriminate.
            destruct_head prod.
            eapply IHn; eassumption. }
        Defined.
      End productions.

      Section productions_ext.
        Lemma parse_productions_ext
              len0
              (parse_nonterminal1 parse_nonterminal2 : forall (str : String) (len : nat),
                                           len <= len0
                                           -> String.string
                                           -> bool)
              (str : String) (len : nat) (pf : len <= len0) (prods : productions Char)
              (ext : forall str' len' pf' nonterminal',
                       parse_nonterminal1 str' len' pf' nonterminal'
                       = parse_nonterminal2 str' len' pf' nonterminal')
        : parse_productions' parse_nonterminal1 str pf prods
          = parse_productions' parse_nonterminal2 str pf prods.
        Proof.
          unfold parse_productions'.
          generalize (select_production_rules prods str); intro prods'.
          revert str len pf.
          induction prods' as [|? ? IHprod]; simpl; intros; try reflexivity; [].
          apply f_equal2; [ | apply IHprod ].
          edestruct nth_error; simpl; trivial; apply parse_production_ext.
          intros; apply ext.
        Qed.
      End productions_ext.

      Section nonterminals.
        Section step.
          Context len0 valid_len (valid : nonterminals_listT)
                  (parse_nonterminal
                   : forall (p : nat * nat),
                       prod_relation lt lt p (len0, valid_len)
                       -> forall (valid : nonterminals_listT)
                                 (str : String) (len : nat),
                            len <= fst p -> String.string -> bool).

          Lemma parse_nonterminal_step_sound
                (parse_nonterminal_sound : forall p pf valid, parse_nonterminal_soundT (@parse_nonterminal p pf valid))
                (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0) (nonterminal : String.string)
                (*(Hvalid : P nonterminal)*)
          : parse_nonterminal_step (G := G) parse_nonterminal valid str pf nonterminal
            -> { p : parse_of_item G str (NonTerminal nonterminal)
                        & Forall_parse_of_item (fun _ => P) p }.
          Proof.
            specialize (fun len' valid_len' => parse_nonterminal_sound (len', valid_len')).
            intro m.
            refine ((fun p : _ * { p' : parse_of G str (Lookup G nonterminal) & Forall_parse_of (fun _ => P) p' }
                     => existT _ (ParseNonTerminal _ (projT1 (snd p))) (fst p, projT2 (snd p)))
                      _).
            revert m.
            unfold parse_nonterminal_step.
            edestruct lt_dec as [|n]; simpl in *.
            { intro H'.
              apply Bool.andb_true_iff in H'.
              destruct H' as [H0 H'].
              apply parse_productions_of_nonterminal_sound' in H'; trivial.
              split; trivial. }
            { pose proof (le_lt_eq_dec _ _ pf) as pf'.
              destruct pf' as [pf'|]; subst.
              { destruct (n pf'). }
              { intro H'.
                apply Bool.andb_true_iff in H'.
                destruct H' as [H0 H'].
                unfold is_true in *.
                subst.
                repeat first [ hnf; simpl; intros; discriminate
                             | edestruct dec; simpl in *; trivial; [];
                               match goal with
                                 | [ H : ?T |- _ ] => has_evar T; fail 1
                                 | [ |- ?T ] => has_evar T; fail 1
                                 | _ => idtac
                               end
                             | apply parse_productions_of_nonterminal_sound' in H'; trivial ].
                split; trivial. } }
          Defined.

          Lemma parse_nonterminal_step_complete
                Pv
                (Hvalid_len : forall nt, is_valid_nonterminal valid nt -> negb (beq_nat valid_len 0))
                (parse_nonterminal_complete : forall p pf valid, parse_nonterminal_completeT (@parse_nonterminal p pf valid) (Pv p valid))
                (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0) (nonterminal : String.string)
                (Hnt : is_valid_nonterminal initial_nonterminals_data nonterminal)
                (Hinit : forall str1 len1,
                           len1 <= len ->
                           forall nonterminal0,
                             minimal_parse_of_nonterminal (G := G) len initial_nonterminals_data str1 nonterminal0 ->
                             Pv (len, nonterminals_length initial_nonterminals_data) initial_nonterminals_data len initial_nonterminals_data nonterminal0)
                (Hinit' : forall str len,
                            len <= len0 ->
                            forall nonterminal0 : String.string,
                              minimal_parse_of_nonterminal (G := G)
                                                    len0 (remove_nonterminal valid nonterminal) str nonterminal0 ->
                              Pv (len0, if is_valid_nonterminal valid nonterminal then pred valid_len else nonterminals_length initial_nonterminals_data) (remove_nonterminal valid nonterminal) len0 (remove_nonterminal valid nonterminal) nonterminal0)
          : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
            -> parse_nonterminal_step (G := G) parse_nonterminal valid str pf nonterminal.
          Proof.
            specialize (fun len' valid_len' => parse_nonterminal_complete (len', valid_len')).
            unfold parse_nonterminal_step.
            intro H'.
            apply Bool.andb_true_iff; split; [ inversion H'; assumption | ].
            revert H'.
            edestruct lt_dec as [|n]; simpl in *.
            { intros H'.
              inversion H'; clear H'; subst. (* Work around Anomaly: Evar ?425 was not declared. Please report. *)
              { eapply parse_productions_of_nonterminal_complete'; [ .. | eassumption ];
                intros; eauto; instantiate; eauto. }
              { match goal with
                  | [ H : ?x < ?x |- _ ]
                    => exfalso; clear -H; abstract omega
                end. } }
            { destruct (le_lt_eq_dec _ _ pf) as [pf'|]; subst.
              { destruct (n pf'). }
              { edestruct dec as [|pf'']; simpl.
                { intro H'.
                  inversion_clear H'.
                  { match goal with
                      | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
                    end. }
                  { let H' := match goal with H : minimal_parse_of _ _ _ _ |- _ => constr:H end in
                    eapply parse_productions_of_nonterminal_complete' in H';
                      intros; eauto; instantiate; eauto; [].
                    let nt := match type of Hinit' with context[is_valid_nonterminal _ ?nt] => constr:nt end in
                    generalize dependent (is_valid_nonterminal valid nt).
                    intros []; simpl; unfold is_true;
                    eauto. } }
                { intro H''; subst.
                  clear -pf'' Hvalid_len H''.
                  abstract (
                      inversion_clear H'';
                      first [ omega
                            | erewrite Hvalid_len in pf'' by eassumption;
                              simpl in *; congruence ]
                    ). } } }
          Qed.
        End step.

        Section step_extensional.
          Lemma parse_nonterminal_step_ext len0 valid_len
                (parse_nonterminal1 parse_nonterminal2
                 : forall (p : nat * nat),
                     prod_relation lt lt p (len0, valid_len)
                     -> forall (valid : nonterminals_listT)
                               (str : String) (len : nat),
                          len <= fst p -> String.string -> bool)
                (valid : nonterminals_listT)
                (str : String) (len : nat) (pf : len <= len0) (nonterminal : String.string)
                (ext : forall p pf0 valid' str' len' pf' nonterminal',
                         parse_nonterminal1 p pf0 valid' str' len' pf' nonterminal'
                         = parse_nonterminal2 p pf0 valid' str' len' pf' nonterminal')
          : parse_nonterminal_step (G := G) parse_nonterminal1 valid str pf nonterminal
            = parse_nonterminal_step (G := G) parse_nonterminal2 valid str pf nonterminal.
          Proof.
            unfold parse_nonterminal_step.
            apply f_equal.
            edestruct lt_dec; simpl.
            { apply parse_productions_ext; auto. }
            { edestruct dec; simpl; trivial.
              apply parse_productions_ext; auto. }
          Qed.
        End step_extensional.

        Section wf.
          Lemma parse_nonterminal_or_abort_sound
                (p : nat * nat) (valid : nonterminals_listT)
                (str : String) (len : nat)
                (Hlen : length str = len)
                (pf : len <= fst p)
                (nonterminal : String.string)
                (*(Hvalid : P nonterminal)*)
          : parse_nonterminal_or_abort (G := G) p valid str pf nonterminal
            -> { p : parse_of_item G str (NonTerminal nonterminal)
                     & Forall_parse_of_item (fun _ => P) p }.
          Proof.
            unfold parse_nonterminal_or_abort.
            revert valid str len Hlen pf nonterminal(* Hvalid*).
            let Acca := match goal with |- context[@Fix _ _ ?Rwf _ _ ?a _ _ _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros valid str len Hlen pf nonterminal(* Hvalid*).
            rewrite Fix5_eq.
            { apply parse_nonterminal_step_sound; eauto. }
            { intros.
              apply parse_nonterminal_step_ext.
              trivial. }
          Defined.

          Lemma prod_relation_elim_helper {A R x} {valid : A}
          : prod_relation (ltof _ length) R
                          (fst x, valid) x
            -> R valid (snd x).
          Proof.
            intros [ H | [? H] ].
            { exfalso; simpl in *; clear -H.
              unfold ltof in H; simpl in H.
              abstract omega. }
            { exact H. }
          Qed.

          Lemma parse_nonterminal_or_abort_complete
                (Pv := fun (p : nat * nat)
                           (validp : nonterminals_listT)
                           (len0 : nat) (valid0 : nonterminals_listT) (nt : String.string) =>
                         nonterminals_length validp <= snd p
                         /\ nonterminals_length valid0 <= nonterminals_length validp
                         /\ nonterminals_length validp <= nonterminals_length initial_nonterminals_data
                         /\ is_valid_nonterminal initial_nonterminals_data nt
                         /\ sub_nonterminals_listT valid0 validp
                         /\ sub_nonterminals_listT validp initial_nonterminals_data)
                (p : nat * nat) (validp : nonterminals_listT)
          : @parse_nonterminal_completeT
              (fst p)
              (parse_nonterminal_or_abort (G := G) p validp)
              (Pv p validp).
          Proof.
            unfold parse_nonterminal_or_abort.
            revert validp.
            let Acca := match goal with |- appcontext[@Fix _ _ ?Rwf _ _ ?a] => constr:(Rwf a) end in
            induction (Acca) as [x ? IHr];
              intros validp valid str len Hlen pf nonterminal ?.
            rewrite Fix5_eq;
              [
              | solve [ intros;
                        apply parse_nonterminal_step_ext;
                        trivial ] ].
            match goal with
              | [ H : appcontext[?f]
                  |- _ -> is_true (parse_nonterminal_step (fun y _ => ?f y) _ _ _ _) ]
                => revert H;
                  generalize f;
                  let H' := fresh "parse_nonterminal_step'" in
                  intros H' H
            end.
            destruct_head_hnf and.
            intro; eapply parse_nonterminal_step_complete with (Pv := Pv); subst Pv;
            [ let x := match goal with
                         | [ |- forall k, _ -> is_true (negb (beq_nat ?x 0)) ]
                             => constr:x
                       end in
              destruct x; simpl; unfold is_true; trivial; [];
              let H := fresh in
              intros ? H;
                pose proof (nonempty_nonterminals H); omega
            | exact IHr
            | .. ];
            instantiate;
            trivial; simpl in *;
            try solve [ assumption
                      | intros; reflexivity
                      | intros; repeat split; reflexivity
                      | intros; repeat split;
                        try inversion_one_head @minimal_parse_of_nonterminal;
                        try solve [ reflexivity
                                  | assumption
                                  | etransitivity; [ apply sub_nonterminals_listT_remove; apply remove_nonterminal_1 | assumption ] ] ].
            { intros; repeat split;
              inversion_one_head @minimal_parse_of_nonterminal;
              try solve [ reflexivity
                        | assumption
                        | rewrite remove_nonterminal_noninc'; assumption
                        | etransitivity; [ apply sub_nonterminals_listT_remove; apply remove_nonterminal_1 | assumption ]
                        | match goal with
                            | [ |- context[if is_valid_nonterminal ?p ?nt then _ else _] ]
                              => let H := fresh in
                                 case_eq (is_valid_nonterminal p nt);
                                   intro H;
                                   [ eapply NPeano.Nat.lt_le_pred, lt_le_trans;
                                     [ exact (remove_nonterminal_dec _ _ H)
                                     | assumption ]
                                   | rewrite remove_nonterminal_noninc'; assumption ]
                          end ]. }
            { eapply @expand_minimal_parse_of_nonterminal; [ .. | eassumption ];
              trivial;
              try solve [ reflexivity
                        | left; reflexivity
                        | apply remove_nonterminal_1
                        | apply remove_nonterminal_2 ]. }
          Defined.

          Lemma parse_nonterminal_sound
                (str : String) (nonterminal : String.string)
          : parse_nonterminal (G := G) str nonterminal
            = true
            -> { p : parse_of_item G str (NonTerminal nonterminal)
                     & Forall_parse_of_item (fun _ => P) p }.
          Proof.
            unfold parse_nonterminal, parse_nonterminal_or_abort.
            apply parse_nonterminal_or_abort_sound; trivial.
          Defined.

          Lemma parse_nonterminal_complete'
                (str : String) (len : nat) (Hlen : length str = len)
                (nonterminal : String.string)
          : minimal_parse_of_nonterminal (G := G) len initial_nonterminals_data str nonterminal
            -> parse_nonterminal (G := G) str nonterminal
               = true.
          Proof.
            unfold parse_nonterminal; subst.
            intro m.
            assert (is_valid_nonterminal initial_nonterminals_data nonterminal) by (inversion m; assumption).
            revert m.
            apply (@parse_nonterminal_or_abort_complete
                     (length str, nonterminals_length initial_nonterminals_data));
            repeat split; try reflexivity; try assumption.
          Defined.

          Lemma parse_nonterminal_complete
                (str : String)
                (nonterminal : String.string)
                (p : parse_of G str (Lookup G nonterminal))
                (H_valid_tree : Forall_parse_of_item (fun _ => P) (ParseNonTerminal _ p))
          : parse_nonterminal (G := G) str nonterminal = true.
          Proof.
            apply parse_nonterminal_complete' with (len := length str); try assumption; trivial.
            pose proof (@minimal_parse_of_nonterminal__of__parse_of_nonterminal
                          Char _ _ G
                          _
                          _
                          (S (size_of_parse_item (ParseNonTerminal _ p)))
                          (length str) str
                          initial_nonterminals_data
                          nonterminal
                          p
                          (Lt.lt_n_Sn _)
                          (reflexivity _)
                          (reflexivity _)
                          H_valid_tree)
              as p'.
            destruct p' as [ [ p' ] | [ nonterminal' [ [ H0 H1 ] ] ] ].
            { exact p'. }
            { exfalso; congruence. }
          Qed.
        End wf.
      End nonterminals.
    End parts.
  End general.
End sound.

Section correct.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {cdata : @boolean_parser_correctness_dataT Char _ G}.
  Context (str : String)
          (nt : String.string).

  Local Notation iffT A B := ((A -> B) * (B -> A))%type.

  Definition parse_nonterminal_correct
  : iffT (parse_nonterminal (G := G) str nt)
         { p : parse_of G str (G nt)
               & Forall_parse_of_item
                   (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
                   (ParseNonTerminal _ p) }.
  Proof.
    split.
    { intro H'.
      apply parse_nonterminal_sound in H'; trivial; [].
      destruct H' as [p H'].
      set (it := NonTerminal nt) in p, H'.
      assert (H'' : it = NonTerminal nt) by reflexivity.
      clearbody it.
      destruct p; try discriminate.
      inversion H''; subst.
      exists p; assumption. }
    { intros []; apply parse_nonterminal_complete; exact _. }
  Defined.
End correct.

Section convenience.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ G data}
          {rdata : @parser_removal_dataT' predata}.

  Definition parse_item_sound
             (str : String) (it : item Char)
  : parse_item (G := G) str it
    -> { p : parse_of_item G str it
             & Forall_parse_of_item
                 (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
                 p }.
  Proof.
    apply parse_item_sound'.
    hnf.
    apply parse_nonterminal_sound.
  Defined.

  Definition parse_item_complete
             (str : String) (it : item Char)
             (p : parse_of_item G str it)
  : Forall_parse_of_item
      (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
      p
    -> parse_item (G := G) str it.
  Proof.
    intro H.
    eapply (@parse_item_complete'
              _ _ G _ str (parse_nonterminal (G := G) str)
              (length str) initial_nonterminals_data);
      [
      |
      | refine (projT1
                 (alt_all_elim
                    _));
        eapply minimal_parse_of_item__of__parse_of_item;
        [ .. | eassumption ]; trivial; try exact (lt_n_Sn _); reflexivity ].
    { hnf.
      clear p it H.
      intros valid nt pf pit.
      unfold parse_nonterminal in *.
      pose proof (@parse_nonterminal_or_abort_complete
                    _ _ _ G _ _ _) as H'.
      let Pv := match type of H' with let Pv := ?P in _ => constr:P end in
      let pfT := (type of pf) in
      unify pfT ((fun len v nt =>
                    Pv (length str, nonterminals_length initial_nonterminals_data)
                       initial_nonterminals_data
                       len v nt)
                   (length str) valid nt).
      eapply H'; clear H'; trivial;
      [ exact pf
      | simpl in * ].
      dependent destruction pit; trivial. }
    { simpl.
      intros ? p'.
      dependent destruction p'; try omega; [].
      repeat intro; repeat split; trivial; try reflexivity. }
  Qed.

  Definition parse_production_sound
             (str : String) (pat : production Char)
  : parse_production (G := G) str pat
    -> { p : parse_of_production G str pat
             & Forall_parse_of_production
                 (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
                 p }.
  Proof.
    apply parse_production_sound'; trivial.
    hnf.
    apply parse_nonterminal_or_abort_sound.
  Defined.

  Fixpoint InT {A} (a : A) (ls : list A) : Type
    := match ls return Type with
         | nil => False
         | x::xs => InT a xs + {x = a}
       end.

  Lemma In_InT {A} {a : A} {ls : list A} {P : Prop}
        (H : InT a ls -> P)
        (H' : In a ls)
  : P.
  Proof.
    induction ls; simpl in *; auto.
    destruct H' as [H' | H'].
    { apply H; right; assumption. }
    { revert H'; apply IHls; intro H'.
      apply H; left; assumption. }
  Qed.

  Definition parse_production_complete
             (str : String) (pat : production Char)
             (H_reachable
              : exists (nt : string) (prefix : list (item Char)),
                  is_valid_nonterminal initial_nonterminals_data nt /\ In (prefix ++ pat) (G nt))
             (p : parse_of_production G str pat)
  : Forall_parse_of_production
      (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
      p
    -> parse_production (G := G) str pat.
  Proof.
    destruct H_reachable as [nt [prefix [Hnt H_reachable]]].
    revert H_reachable; refine (In_InT _); intro H_reachable.
    intro H.
    eapply (@parse_production_complete'
              _ _ _ G _ (length str) _
              initial_nonterminals_data); trivial;
    [
    |
    |
    | refine (projT1 (alt_all_elim _));
      eapply minimal_parse_of_production__of__parse_of_production;
      [ .. | eassumption ]; trivial; try exact (lt_n_Sn _); reflexivity ].
    { exact (@parse_nonterminal_or_abort_complete
               _ _ _ G _ _ _
               (length str, nonterminals_length initial_nonterminals_data)
               initial_nonterminals_data). }
    { simpl.
      intros ????? p'.
      dependent destruction p';
      repeat intro; repeat split; trivial; try reflexivity. }
    { hnf in H_reachable.
      intros len0 valid str' pf'.
      generalize (split_string_for_production_complete valid str' pf' nt Hnt) as H'.
      match goal with
        | [ |- ForallT (Forall_tails ?P) _ -> (Forall_tails ?P') _ ] => change P' with P; generalize P; intro
      end.
      clear -H_reachable.
      induction (G nt) as [ | y ys IHGnt ]; simpl in *; destruct_head False; [].
      destruct_head or; subst.
      destruct H_reachable as [H_reachable|H_reachable].
      { intros [_ ?]; auto. }
      { subst.
        intros [? _]; clear IHGnt.
        induction prefix; simpl in *; destruct_head prod; auto. } }
  Qed.

  Definition parse_productions_of_nonterminal_sound
             (str : String) (nt : String.string)
  : parse_productions (G := G) str (Lookup G nt)
    -> { p : parse_of G str (Lookup G nt)
             & Forall_parse_of
                 (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
                 p }.
  Proof.
    apply parse_productions_of_nonterminal_sound'; trivial.
    hnf.
    apply parse_nonterminal_or_abort_sound.
  Defined.

  Definition parse_productions_of_nonterminal_complete
             (str : String) (nt : String.string)
             (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
             (p : parse_of G str (Lookup G nt))
  : Forall_parse_of
      (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
      p
    -> parse_productions (G := G) str (Lookup G nt).
  Proof.
    intro H.
    eapply (@parse_productions_of_nonterminal_complete'
              _ _ _ G _ _ (length str) _
              initial_nonterminals_data); trivial;
    [
    |
    | refine (projT1 (alt_all_elim _));
      eapply minimal_parse_of__of__parse_of;
      [ .. | eassumption ]; trivial; try exact (lt_n_Sn _); reflexivity ].
    { exact (@parse_nonterminal_or_abort_complete
               _ _ _ G _ _ _
               (length str, nonterminals_length initial_nonterminals_data)
               initial_nonterminals_data). }
    { simpl.
      intros ????? p'.
      dependent destruction p';
      repeat intro; repeat split; trivial; try reflexivity. }
  Qed.
End convenience.
