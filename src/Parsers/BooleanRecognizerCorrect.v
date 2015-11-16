(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.BooleanRecognizer Fiat.Parsers.MinimalParse.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties Fiat.Parsers.WellFoundedParse.
Require Import Fiat.Common Fiat.Common.Wf.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Parsers.BooleanRecognizerExt.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Require Import Coq.Logic.Eqdep_dec.

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
            {rdata : @parser_removal_dataT' _ G predata}
            (GValid : grammar_valid G).

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      Section item.
        Context (str : String)
                (str_matches_nonterminal : String.string -> bool).

        Definition str_matches_nonterminal_soundT
          := forall nonterminal,
               is_valid_nonterminal initial_nonterminals_data nonterminal
               -> str_matches_nonterminal nonterminal
               -> parse_of_item G str (NonTerminal nonterminal).

        Definition str_matches_nonterminal_completeT P len0
          := forall (valid : nonterminals_listT) nonterminal (H_sub : P len0 valid nonterminal),
               minimal_parse_of_item (G := G) len0 valid str (NonTerminal nonterminal)
               -> str_matches_nonterminal nonterminal.

        Lemma parse_item_sound'
              (str_matches_nonterminal_sound : str_matches_nonterminal_soundT)
              (it : item Char)
              (Hvalid : item_valid it)
        : parse_item' str_matches_nonterminal str it -> parse_of_item G str it.
        Proof.
          unfold parse_item', str_matches_nonterminal_soundT in *.
          repeat match goal with
                   | _ => intro
                   | [ H : context[match ?E with _ => _ end] |- _ ] => atomic E; destruct E
                   | [ |- context[match ?E with _ => _ end] ] => atomic E; destruct E
                   | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                   | [ H : context[match ?E with _ => _ end] |- context[?E] ] => destruct E
                   | _ => progress (simpl in *; subst)
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
              | [ |- _ /\ _ ] => split
              | [ |- ?x < ?x \/ _ ] => right
              | [ H : ?T |- ?T \/ _ ] => left; exact H
              | [ |- ?x = ?x \/ _ ] => left; reflexivity
              | [ |- _ \/ ?x = ?x ] => right; reflexivity
              | [ |- _ = true ] => apply bool_eq_correct
              | [ H : context[?E] |- context[match ?E with _ => _ end] ] => destruct E
              | [ H : minimal_parse_of _ _ _ [] |- _ ] => solve [ inversion H ]
              | [ |- is_true (str_matches_nonterminal _) ]
                => eapply str_matches_nonterminal_complete; [..| eassumption ]
              | [ H : minimal_parse_of_item _ _ _ (Terminal _) |- _ ] => inversion H; clear H
              | [ H : minimal_parse_of_item _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
              | [ H : forall nonterminal, _ -> Pv _ _ nonterminal |- Pv _ _ _ ] => eapply H
          end.
        Qed.
      End item.

      Section production.
        Context (len0 : nat)
                (parse_nonterminal : forall (str : String) (len : nat),
                                len <= len0
                                -> String.string
                                -> bool).

        Definition parse_nonterminal_soundT
          := forall str len (Hlen : length str = len) pf nonterminal,
               is_valid_nonterminal initial_nonterminals_data nonterminal
               -> @parse_nonterminal str len pf nonterminal
               -> parse_of_item G str (NonTerminal nonterminal).

        Definition parse_nonterminal_completeT P
          := forall valid (str : String) len (Hlen : length str = len) pf nonterminal (H_sub : P len0 valid nonterminal),
               minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
               -> @parse_nonterminal str len pf nonterminal.

        Lemma parse_production_sound'
                 (parse_nonterminal_sound : parse_nonterminal_soundT)
                 (str : String) (len : nat) (Hlen : length str = len)
                 (pf : len <= len0)
                 (prod : production Char)
                 (Hvalid : production_valid prod)
        : parse_production' parse_nonterminal str pf prod
          -> parse_of_production G str prod.
        Proof.
          revert str len Hlen pf; induction prod;
          repeat match goal with
                   | _ => intro
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => solve [ auto ]
                   | [ H : appcontext[fold_left] |- _ ] => erewrite fold_symmetric in H by first [ apply Bool.orb_assoc | apply Bool.orb_comm ]
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
                 end.
          { econstructor;
            solve [ eapply IHprod; inversion Hvalid; subst; try eassumption; rewrite drop_length; omega
                  | eapply parse_item_sound'; try eassumption;
                    hnf in parse_nonterminal_sound |- *;
                    first [ apply parse_nonterminal_sound;
                            rewrite take_length; repeat apply Min.min_case_strong; omega
                          | inversion Hvalid; subst; assumption ] ]. }
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
                          | it::its => split_list_completeT (G := G) (valid := valid) (len0 := len0) it its str pf (@split_string_for_production _ _ data it its str)
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
                   | [ H : appcontext[fold_left] |- _ ] => erewrite fold_symmetric in H by first [ apply Bool.orb_assoc | apply Bool.orb_comm ]
                   | [ |- appcontext[fold_left] ] => erewrite fold_symmetric by first [ apply Bool.orb_assoc | apply Bool.orb_comm ]
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
                   | [ |- is_true (beq_nat _ _) ] => apply beq_nat_true_iff
                   | [ H : minimal_parse_of_item _ _ _ _ |- _ ] => inversion H; clear H; subst
                   | [ H : minimal_parse_of_nonterminal _ _ (take ?n ?str) _ |- _ ]
                     => is_var n; unique pose proof (expand_minimal_parse_of_nonterminal_beq (take_min_length _ _) H)
                   | [ H : minimal_parse_of_production _ _ (drop ?n ?str) _ |- _ ]
                     => is_var n; unique pose proof (expand_minimal_parse_of_production_beq (drop_min_length _ _) H)
                   | [ H : In (min _ _) (map (min _) _) |- _ ] => apply in_map_iffT_nat in H
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
                   | _ => progress unfold is_true in *
                   | [ H : (take ?x ?str ~= [?ch]) = true,
                           H' : min (length ?str) ?x' = min (length ?str) ?x
                       |- (take ?x' ?str ~= [?ch]) = true ]
                     => rewrite take_min_length in H |- *; rewrite H'; exact H
                   | [ H : min ?x ?y = min ?x ?y', H' : context[drop (min ?x ?y') _] |- _ ]
                     => rewrite <- H in H'
                   | [ H : min ?x ?y = min ?x ?y', H' : context[take (min ?x ?y') _] |- _ ]
                     => rewrite <- H in H'
                   | [ IHprod : _ |- _ ]
                     => eapply IHprod; try eassumption; rewrite ?drop_length, ?take_length;
                        solve [ omega
                              | eauto using expand_minimal_parse_of_production_beq, (fun x y => symmetry (drop_min_length x y)) with nocore ]
                 end;
          [].
          eapply parse_nonterminal_complete;
            [ ..
            | solve [ eauto using expand_minimal_parse_of_nonterminal_beq, (fun x y => symmetry (take_min_length x y)) with nocore ] ];
            simpl;
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

      Section productions.
        Context len0
                (parse_nonterminal : forall (str : String) (len : nat),
                                len <= len0
                                -> String.string
                                -> bool).

        Local Ltac parse_productions_t :=
          repeat match goal with
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
                   | [ H : parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
                   | [ H : parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : minimal_parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
                   | [ H : minimal_parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : parse_production' _ _ _ _ = true |- _ ] => apply parse_production_sound' in H; [ | eassumption.. ]
                   | [ H : productions_valid (?x::?xs) |- _ ]
                     => assert (production_valid x) by (inversion H; subst; assumption);
                       assert (productions_valid xs) by (inversion H; subst; assumption);
                       clear H
                   | _ => left; eapply parse_production_complete'; (eassumption' || reflexivity)
                   | _ => solve [ eauto ]
                 end.

        Lemma parse_productions_sound'
                 (parse_nonterminal_sound : parse_nonterminal_soundT parse_nonterminal)
                 (str : String) (len : nat) (Hlen : length str = len)
                 (pf : len <= len0)
                 (prods : productions Char)
                 (Hvalid : productions_valid prods)
        : parse_productions' parse_nonterminal str pf prods
          -> parse_of G str prods.
        Proof.
          revert str len Hlen pf; induction prods; simpl.
          { unfold parse_productions'; simpl; intros ???? H; exfalso; clear -H.
            abstract discriminate. }
          { unfold parse_productions' in *; simpl in *.
            parse_productions_t. }
        Defined.

        Lemma parse_productions_complete'
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT parse_nonterminal Pv)
              (Hinit : forall str len (Hlen : length str = len) (pf : len <= len0) nonterminal,
                         minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
                         -> Pv len0 valid nonterminal)
              (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0)
              (prods : productions Char)
              (split_string_for_production_complete'
               : forall len0 valid (str : String) (pf : length str <= len0),
                   ForallT
                     (Forall_tails
                        (fun prod' =>
                           match prod' return Type with
                             | nil => True
                             | it::its => split_list_completeT (G := G) (valid := valid) (len0 := len0) it its str pf (@split_string_for_production _ _ data it its str)
                           end))
                     prods)
        : minimal_parse_of (G := G) len0 valid str prods
          -> parse_productions' parse_nonterminal str pf prods.
        Proof.
          revert str len Hlen pf; induction prods; simpl.
          { unfold parse_productions'; simpl; intros ???? H; exfalso; clear -H.
            abstract inversion H. }
          { specialize (IHprods (fun len0 valid str pf => snd (split_string_for_production_complete' len0 valid str pf))).
            pose proof (fun len0 valid str pf => fst (split_string_for_production_complete' len0 valid str pf)) as split_string_for_production_complete''.
            clear split_string_for_production_complete'.
            unfold parse_productions' in *; simpl in *.
            parse_productions_t. }
        Defined.
      End productions.

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
                (Hvalid : is_valid_nonterminal initial_nonterminals_data nonterminal)
          : parse_nonterminal_step (G := G) parse_nonterminal valid str pf nonterminal
            -> parse_of_item G str (NonTerminal nonterminal).
          Proof.
            pose proof Hvalid as Hvalid'; rewrite initial_nonterminals_correct in Hvalid'.
            specialize (fun len' valid_len' => parse_nonterminal_sound (len', valid_len')).
            unfold parse_nonterminal_step.
            intro H'; constructor; trivial; revert H'; [].
            edestruct lt_dec as [|n]; simpl in *.
            { intro H'.
              apply parse_productions_sound' in H'; eauto with nocore. }
            { pose proof (le_lt_eq_dec _ _ pf) as pf'.
              destruct pf' as [pf'|]; subst.
              { destruct (n pf'). }
              { intro H'.
                unfold is_true in *.
                repeat first [ hnf; simpl; intros; discriminate
                             | edestruct dec; simpl in *; trivial; [];
                               match goal with
                                 | [ H : ?T |- _ ] => has_evar T; fail 1
                                 | [ |- ?T ] => has_evar T; fail 1
                                 | _ => idtac
                               end
                             | apply parse_productions_sound' in H'; trivial; []
                             | solve [ eauto with nocore ] ]. } }
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
            edestruct lt_dec as [|n]; simpl in *.
            { intros H'.
              inversion H'; clear H'; subst. (* Work around Anomaly: Evar ?425 was not declared. Please report. *)
              { eapply parse_productions_complete'; [ .. | eassumption ];
                intros; eauto; instantiate; eauto; [].
                apply split_string_for_production_complete; assumption. }
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
                    eapply parse_productions_complete' in H';
                      intros; eauto; instantiate; eauto; [|].
                    { let nt := match type of Hinit' with context[is_valid_nonterminal _ ?nt] => constr:nt end in
                      generalize dependent (is_valid_nonterminal valid nt).
                      intros []; simpl; unfold is_true;
                      eauto. }
                    { intros; apply split_string_for_production_complete; assumption. } } }
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

        Section wf.
          Lemma parse_nonterminal_or_abort_sound
                (p : nat * nat) (valid : nonterminals_listT)
                (str : String) (len : nat)
                (Hlen : length str = len)
                (pf : len <= fst p)
                (nonterminal : String.string)
                (Hvalid : is_valid_nonterminal initial_nonterminals_data nonterminal)
          : parse_nonterminal_or_abort (G := G) p valid str pf nonterminal
            -> parse_of_item G str (NonTerminal nonterminal).
          Proof.
            unfold parse_nonterminal_or_abort.
            revert valid str len Hlen pf nonterminal Hvalid.
            let Acca := match goal with |- context[@Fix _ _ ?Rwf _ _ ?a _ _ _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros valid str len Hlen pf nonterminal Hvalid.
            rewrite Fix5_eq.
            { apply parse_nonterminal_step_sound; assumption. }
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
            -> parse_of_item G str (NonTerminal nonterminal).
          Proof.
            unfold parse_nonterminal, parse_nonterminal_or_abort.
            intro H; generalize H.
            apply parse_nonterminal_or_abort_sound; trivial.
            rewrite Fix5_eq in H by (intros; apply parse_nonterminal_step_ext; assumption).
            unfold parse_nonterminal_step in H at 1.
            simpl in H.
            edestruct lt_dec; simpl in *; try omega.
            edestruct dec as [H'|H']; simpl in *; try discriminate.
            apply Bool.andb_true_iff in H'.
            destruct H'; assumption.
          Defined.

          Lemma parse_nonterminal_complete'
                (str : String) (len : nat) (Hlen : length str = len)
                (nonterminal : String.string)
                (H_init : is_valid_nonterminal initial_nonterminals_data nonterminal)
          : minimal_parse_of_nonterminal (G := G) len initial_nonterminals_data str nonterminal
            -> parse_nonterminal (G := G) str nonterminal
               = true.
          Proof.
            unfold parse_nonterminal; subst.
            eapply (@parse_nonterminal_or_abort_complete
                    (length str, nonterminals_length initial_nonterminals_data));
            repeat split; try reflexivity; assumption.
          Defined.

          Lemma parse_nonterminal_complete
                (str : String)
                (nonterminal : String.string)
                (p : parse_of G str (Lookup G nonterminal))
                (Hvalid : is_valid_nonterminal initial_nonterminals_data nonterminal)
          : parse_nonterminal (G := G) str nonterminal = true.
          Proof.
            apply parse_nonterminal_complete' with (len := length str); try assumption; trivial.
            pose proof Hvalid as Hvalid'; rewrite initial_nonterminals_correct in Hvalid'.
            pose proof (@minimal_parse_of_nonterminal__of__parse_of_nonterminal
                          Char _ _ G
                          _
                          _
                          (S (size_of_parse_item (ParseNonTerminal _ Hvalid' p)))
                          (length str) str
                          initial_nonterminals_data
                          nonterminal
                          p
                          Hvalid'
                          (Lt.lt_n_Sn _)
                          (reflexivity _)
                          (reflexivity _))
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
  Context {rdata : @parser_removal_dataT' Char G _}.
  Context (GValid : grammar_valid G).
  Context (str : String)
          (nt : String.string).

  Definition parse_nonterminal_correct
  : (parse_nonterminal (G := G) str nt -> parse_of_item G str (NonTerminal nt))
    * (parse_of G str (G nt) -> is_valid_nonterminal initial_nonterminals_data nt
       -> parse_nonterminal (G := G) str nt).
  Proof.
    split.
    { apply parse_nonterminal_sound; trivial. }
    { apply parse_nonterminal_complete; exact _. }
  Defined.
End correct.

Section convenience.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ G data}
          {rdata : @parser_removal_dataT' _ G predata}.
  Context (GValid : grammar_valid G).

  Definition parse_item_sound
             (str : String) (it : item Char)
             (Hvalid : item_valid it)
  : parse_item (G := G) str it
    -> parse_of_item G str it.
  Proof.
    eapply parse_item_sound'; trivial.
    hnf.
    intros ??; apply parse_nonterminal_sound; trivial.
  Defined.

  Definition parse_item_complete
             (str : String) (it : item Char)
             (p : parse_of_item G str it)
  : parse_item (G := G) str it.
  Proof.
    eapply (@parse_item_complete'
              _ _ G _ str (parse_nonterminal (G := G) str)
              (length str) initial_nonterminals_data);
      [
      |
      | exact (proj1_sig
                 (alt_all_elim
                    (@minimal_parse_of_item__of__parse_of_item
                       _ _ G _ _ (length str) (S (size_of_parse_item p))
                       (fun h' _ => @minimal_parse_of_nonterminal__of__parse_of_nonterminal _ _ _ G _ _ h')
                       str (reflexivity _) initial_nonterminals_data _ p (lt_n_Sn _)
                       (reflexivity _)))) ].
    { hnf.
      clear p it.
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
             (Hvalid : production_valid pat)
  : parse_production (G := G) str pat
    -> parse_of_production G str pat.
  Proof.
    apply parse_production_sound'; trivial.
    hnf.
    apply parse_nonterminal_or_abort_sound; trivial.
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
  : parse_production (G := G) str pat.
  Proof.
    destruct H_reachable as [nt [prefix [Hnt H_reachable]]].
    revert H_reachable; refine (In_InT _); intro H_reachable.
    eapply (@parse_production_complete'
              _ _ _ G _ _ (length str) _
              initial_nonterminals_data); trivial;
    [
    |
    |
    | exact (proj1_sig
               (alt_all_elim
                  (@minimal_parse_of_production__of__parse_of_production
                     _ _ _ G _ _ (length str) (S (size_of_parse_production p))
                     (fun h' _ => @minimal_parse_of_nonterminal__of__parse_of_nonterminal _ _ _ G _ _ h')
                     str (reflexivity _) initial_nonterminals_data _ p (lt_n_Sn _)
                     (reflexivity _)))) ].
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

  Definition parse_productions_sound
             (str : String) (pats : productions Char)
             (Hvalid : productions_valid pats)
  : parse_productions (G := G) str pats
    -> parse_of G str pats.
  Proof.
    apply parse_productions_sound'; trivial.
    hnf.
    apply parse_nonterminal_or_abort_sound; trivial.
  Defined.

  Definition parse_productions_complete
             (str : String) (pats : productions Char)
             (H_reachable
              : exists (nt : string) (prefix : productions Char),
                  is_valid_nonterminal initial_nonterminals_data nt /\ prefix ++ pats = G nt)
             (p : parse_of G str pats)
  : parse_productions (G := G) str pats.
  Proof.
    destruct H_reachable as [nt [prefix [Hnt H_reachable]]].
    eapply (@parse_productions_complete'
              _ _ _ G _ _ (length str) _
              initial_nonterminals_data); trivial;
    [
    |
    |
    | exact (proj1_sig
               (alt_all_elim
                  (@minimal_parse_of_productions__of__parse_of_productions
                     _ _ _ G _ _ (length str) (S (size_of_parse p))
                     (fun h' _ => @minimal_parse_of_nonterminal__of__parse_of_nonterminal _ _ _ G _ _ h')
                     str (reflexivity _) initial_nonterminals_data _ p (lt_n_Sn _)
                     (reflexivity _)))) ].
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
        | [ |- ForallT ?P _ -> ForallT ?P' _ ] => change P' with P; generalize P; intro
      end.
      rewrite <- H_reachable; clear.
      induction prefix; simpl; trivial.
      intros [_ ?]; auto. }
  Qed.
End convenience.

Section convenience_valid.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ G data}
          {rdata : @parser_removal_dataT' _ G predata}
          (Gvalid : grammar_valid G).

  Lemma parse_nonterminal_completev
        (str : String)
        (nonterminal : String.string)
        (Hnt : is_valid_nonterminal initial_nonterminals_data nonterminal)
        (p : parse_of G str (Lookup G nonterminal))
  : parse_nonterminal (G := G) str nonterminal = true.
  Proof.
    apply (parse_nonterminal_complete); try assumption.
  Qed.

  Definition parse_item_completev
             (str : String) (it : item Char)
             (Hit : item_valid it)
             (p : parse_of_item G str it)
  : parse_item (G := G) str it.
  Proof.
    apply (parse_item_complete p); try assumption.
  Qed.

  Definition parse_production_completev
             (str : String) (pat : production Char)
             (H_reachable
              : exists (nt : string) (prefix : list (item Char)),
                  is_valid_nonterminal initial_nonterminals_data nt /\ In (prefix ++ pat) (G nt))
             (p : parse_of_production G str pat)
  : parse_production (G := G) str pat.
  Proof.
    eapply (parse_production_complete H_reachable p).
  Qed.

  Definition parse_productions_completev
             (str : String) (pats : productions Char)
             (H_reachable
              : exists (nt : string) (prefix : productions Char),
                  is_valid_nonterminal initial_nonterminals_data nt /\ prefix ++ pats = G nt)
             (p : parse_of G str pats)
  : parse_productions (G := G) str pats.
  Proof.
    eapply (parse_productions_complete H_reachable p).
  Qed.
End convenience_valid.
