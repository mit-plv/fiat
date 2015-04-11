(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar ADTSynthesis.Parsers.BooleanRecognizer ADTSynthesis.Parsers.MinimalParse.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.Splitters.RDPList ADTSynthesis.Parsers.Splitters.BruteForce.
Require Import ADTSynthesis.Parsers.MinimalParseOfParse.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties ADTSynthesis.Parsers.WellFoundedParse.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Wf.
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
            {rdata : @parser_removal_dataT' predata}.

    Let P : String.string -> Prop
      := fun p => is_valid_nonterminal initial_nonterminals_data p.

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      (*Let H_subT valid
        := sub_productions_listT is_valid_nonterminal valid initial_nonterminals_data.*)

      Section item.
        Context (str : String)
                (str_matches_nonterminal : String.string -> bool).

        Definition str_matches_nonterminal_soundT
          := forall nonterminal, str_matches_nonterminal nonterminal
                          -> parse_of_item G str (NonTerminal nonterminal).

        Definition str_matches_nonterminal_completeT P str0
          := forall (valid : nonterminals_listT) nonterminal (H_sub : P str0 valid nonterminal),
               minimal_parse_of_item (G := G) str0 valid str (NonTerminal nonterminal)
               -> str_matches_nonterminal nonterminal.

        Lemma parse_item_sound
              (str_matches_nonterminal_sound : str_matches_nonterminal_soundT)
              (it : item Char)
        : parse_item str_matches_nonterminal str it -> parse_of_item G str it.
        Proof.
          unfold parse_item, str_matches_nonterminal_soundT in *.
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

        Lemma parse_item_complete
              str0
              valid Pv
              (str_matches_nonterminal_complete : str_matches_nonterminal_completeT Pv str0)
              (it : item Char)
              (Hinit : forall nonterminal,
                         minimal_parse_of_nonterminal (G := G) str0 valid str nonterminal
                         -> Pv str0 valid nonterminal)
        : minimal_parse_of_item (G := G) str0 valid str it
          -> parse_item str_matches_nonterminal str it.
        Proof.
          unfold parse_item, str_matches_nonterminal_completeT in *.
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

      Section item_ext.
        Lemma parse_item_ext
              (str : String)
              (str_matches_nonterminal1 str_matches_nonterminal2 : String.string -> bool)
              (it : item Char)
              (ext : forall x, str_matches_nonterminal1 x = str_matches_nonterminal2 x)
        : parse_item str_matches_nonterminal1 str it
          = parse_item str_matches_nonterminal2 str it.
        Proof.
          unfold parse_item.
          destruct it; auto;
          match goal with
            | [ |- context[match ?E with _ => _ end] ] => destruct E
          end;
          auto.
        Qed.
      End item_ext.

      Section production.
        Context (str0 : String)
                (parse_nonterminal : forall (str : String),
                                str ≤s str0
                                -> String.string
                                -> bool).

        Definition parse_nonterminal_soundT
          := forall str pf nonterminal,
               @parse_nonterminal str pf nonterminal
               -> parse_of_item G str (NonTerminal nonterminal).

        Definition parse_nonterminal_completeT P
          := forall valid (str : String) pf nonterminal (H_sub : P str0 valid nonterminal),
               minimal_parse_of_nonterminal (G := G) str0 valid str nonterminal
               -> @parse_nonterminal str pf nonterminal.

        Lemma parse_production_sound
                 (parse_nonterminal_sound : parse_nonterminal_soundT)
                 (str : String) (pf : str ≤s str0)
                 (prod : production Char)
        : parse_production parse_nonterminal pf prod
          -> parse_of_production G str prod.
        Proof.
          revert str pf; induction prod;
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
                 end.
          { econstructor;
            solve [ eapply IHprod; eassumption
                  | eapply parse_item_sound; try eassumption;
                    hnf in parse_nonterminal_sound |- *;
                    apply parse_nonterminal_sound ]. }
        Defined.

        Lemma parse_production_complete
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT Pv)
              (Hinit : forall str (pf : str ≤s str0) nonterminal,
                         minimal_parse_of_nonterminal (G := G) str0 valid str nonterminal
                         -> Pv str0 valid nonterminal)
              (str : String) (pf : str ≤s str0)
              (prod : production Char)
              (split_string_for_production_complete'
               : forall str0 valid (str : String) (pf : str ≤s str0),
                   Forall_tails
                     (fun prod' =>
                        match prod' return Type with
                          | nil => True
                          | it::its => split_list_completeT (G := G) (valid := valid) (str0 := str0) it its pf (split_string_for_production it its str)
                        end)
                     prod)
        : minimal_parse_of_production (G := G) str0 valid str prod
          -> parse_production parse_nonterminal pf prod.
        Proof.
          revert valid str Hinit pf; induction prod;
          [
          | specialize (IHprod (fun str0 valid str pf => snd (split_string_for_production_complete' str0 valid str pf))) ];
          repeat match goal with
                   | _ => intro
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => progress destruct_head @StringWithSplitState
                   | _ => solve [ auto ]
                   | [ H : appcontext[fold_left] |- _ ] => rewrite (@fold_symmetric _ _ Bool.orb_assoc Bool.orb_comm) in H
                   | [ |- appcontext[fold_left] ] => rewrite (@fold_symmetric _ _ Bool.orb_assoc Bool.orb_comm)
                   | [ H : is_true (fold_right orb false (map _ _)) |- _ ] => apply fold_right_orb_map_sig1 in H
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | [ H : minimal_parse_of_production _ _ _ nil |- _ ] => inversion_clear H
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
                   | [ |- context[NPeano.Nat.eq_dec ?x ?y] ] => destruct (NPeano.Nat.eq_dec x y)
                   | _ => progress destruct_head_hnf sumbool
                   | _ => progress destruct_head_hnf and
                   | _ => progress destruct_head_hnf sig
                   | _ => progress destruct_head_hnf sigT
                   | _ => progress destruct_head_hnf Datatypes.prod
                   | _ => progress simpl in *
                   | _ => progress subst
                   | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
                   | [ H : (_ =s _) = true |- _ ]
                     => let H' := fresh in
                        pose proof H as H';
                          apply bool_eq_correct in H';
                          progress subst
                   | [ H : minimal_parse_of_production _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ n : nat, H : ?s ≤s _ |- context[split_string_for_production ?it ?p ?s] ]
                     => let H' := fresh in
                        pose proof
                             (fun v p0 p1
                              => fst (@split_string_for_production_complete' _ v s H) (existT _ n (p0, p1))) as H';
                          clear split_string_for_production_complete';
                          simpl in H'
                   | [ H : forall a b, is_true (a ++ b =s _ ++ _) -> _ |- _ ]
                     => specialize (H _ _ (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : ?a -> ?b, H' : ?a |- _ ] => specialize (H H')
                   | [ H : forall (v : nonterminals_listT) (x : @?a v), @?b v x |- _ ]
                     => pose proof (H valid); pose proof (H initial_nonterminals_data); clear H
                   | [ |- is_true (fold_right orb false (map _ _)) ] => apply fold_right_orb_map_sig2
                   | [ H : minimal_parse_of_item _ _ _ _ |- _ ] => inversion H; clear H; subst
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
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
                   | [ IHprod : _ |- _ ] => eapply IHprod; eassumption
                 end;
          eapply parse_nonterminal_complete; [..| eassumption ]; simpl;
          repeat match goal with
                   | _ => eassumption
                   | _ => reflexivity
                   | [ |- Pv _ _ _ ] => eapply Hinit; [ .. | eassumption ]
                   | _ => etransitivity; [ | eassumption ];
                          solve [ apply str_le_take
                                | apply str_le_drop ]
                 end.
        Qed.
      End production.

      Section production_ext.
        Lemma parse_production_ext
              (str0 : String)
              (parse_nonterminal1 parse_nonterminal2 : forall (str : String),
                                           str ≤s str0
                                           -> String.string
                                           -> bool)
              (str : String) (pf : str ≤s str0) (prod : production Char)
              (ext : forall str' pf' nonterminal', parse_nonterminal1 str' pf' nonterminal'
                                            = parse_nonterminal2 str' pf' nonterminal')
        : parse_production parse_nonterminal1 pf prod
          = parse_production parse_nonterminal2 pf prod.
        Proof.
          revert str pf.
          induction prod as [|? ? IHprod]; simpl; intros; try reflexivity; [].
          f_equal.
          apply map_ext; intros.
          apply f_equal2; [ apply parse_item_ext | apply IHprod ].
          intros; apply ext.
        Qed.
      End production_ext.

      Section productions.
        Context (str0 : String)
                (parse_nonterminal : forall (str : String),
                                str ≤s str0
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
                   | _ => progress subst
                   | [ H : parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
                   | [ H : parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : minimal_parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
                   | [ H : minimal_parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : parse_production _ _ _ = true |- _ ] => apply parse_production_sound in H; try eassumption; []
                   | _ => left; eapply parse_production_complete; eassumption
                   | _ => solve [ eauto ]
                 end.

        Lemma parse_productions_sound
                 (parse_nonterminal_sound : parse_nonterminal_soundT parse_nonterminal)
                 (str : String) (pf : str ≤s str0)
                 (prods : productions Char)
        : parse_productions parse_nonterminal pf prods
          -> parse_of G str prods.
        Proof.
          revert str pf; induction prods; simpl.
          { unfold parse_productions; simpl; intros ?? H; exfalso; clear -H.
            abstract discriminate. }
          { unfold parse_productions in *; simpl in *.
            parse_productions_t. }
        Defined.

        Lemma parse_productions_complete
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT parse_nonterminal Pv)
              (Hinit : forall str (pf : str ≤s str0) nonterminal,
                         minimal_parse_of_nonterminal (G := G) str0 valid str nonterminal
                         -> Pv str0 valid nonterminal)
              (str : String) (pf : str ≤s str0)
              (prods : productions Char)
              (split_string_for_production_complete'
               : forall str0 valid (str : String) (pf : str ≤s str0),
                   ForallT
                     (Forall_tails
                        (fun prod' =>
                           match prod' return Type with
                             | nil => True
                             | it::its => split_list_completeT (G := G) (valid := valid) (str0 := str0) it its pf (split_string_for_production it its str)
                           end))
                     prods)
        : minimal_parse_of (G := G) str0 valid str prods
          -> parse_productions parse_nonterminal pf prods.
        Proof.
          revert str pf; induction prods; simpl.
          { unfold parse_productions; simpl; intros ?? H; exfalso; clear -H.
            abstract inversion H. }
          { specialize (IHprods (fun str0 valid str pf => snd (split_string_for_production_complete' str0 valid str pf))).
            pose proof (fun str0 valid str pf => fst (split_string_for_production_complete' str0 valid str pf)) as split_string_for_production_complete''.
            clear split_string_for_production_complete'.
            unfold parse_productions in *; simpl in *.
            parse_productions_t. }
        Defined.
      End productions.

      Section productions_ext.
        Lemma parse_productions_ext
              (str0 : String)
              (parse_nonterminal1 parse_nonterminal2 : forall (str : String),
                                           str ≤s str0
                                           -> String.string
                                           -> bool)
              (str : String) (pf : str ≤s str0) (prods : productions Char)
              (ext : forall str' pf' nonterminal', parse_nonterminal1 str' pf' nonterminal'
                                            = parse_nonterminal2 str' pf' nonterminal')
        : parse_productions parse_nonterminal1 pf prods
          = parse_productions parse_nonterminal2 pf prods.
        Proof.
          revert str pf.
          induction prods as [|? ? IHprod]; simpl; intros; try reflexivity; [].
          unfold parse_productions; simpl.
          apply f_equal2; [ apply parse_production_ext | apply IHprod ].
          intros; apply ext.
        Qed.
      End productions_ext.

      Section nonterminals.
        Section step.
          Context (str0 : String) (valid : nonterminals_listT)
                  (parse_nonterminal
                   : forall (p : String * nonterminals_listT),
                       prod_relation (ltof _ length) nonterminals_listT_R p (str0, valid)
                       -> forall str : String, str ≤s fst p -> String.string -> bool).

          Lemma parse_nonterminal_step_sound
                (parse_nonterminal_sound : forall p pf, parse_nonterminal_soundT (@parse_nonterminal p pf))
                (str : String) (pf : str ≤s str0) (nonterminal : String.string)
          : parse_nonterminal_step (G := G) parse_nonterminal pf nonterminal
            -> parse_of_item G str (NonTerminal nonterminal).
          Proof.
            unfold parse_nonterminal_step.
            intro H'; constructor; revert H'.
            edestruct lt_dec as [|n].
            { intro H'.
              apply parse_productions_sound in H'; trivial. }
            { edestruct dec; [ | intro H''; exfalso; clear -H'';
                                 abstract discriminate ].
              pose proof (strle_to_sumbool _ pf) as pf'.
              destruct pf' as [pf'|]; subst.
              { destruct (n pf'). }
              { intro H'.
                apply parse_productions_sound in H'; trivial;
                destruct_head @StringWithSplitState; subst; trivial. } }
          Defined.

          Lemma parse_nonterminal_step_complete
                Pv
                (parse_nonterminal_complete : forall p pf, parse_nonterminal_completeT (@parse_nonterminal p pf) (Pv p))
                (str : String) (pf : str ≤s str0) (nonterminal : String.string)
                (Hnt : is_valid_nonterminal initial_nonterminals_data nonterminal)
                (Hinit : forall str1,
                           str1 ≤s str ->
                           forall nonterminal0,
                             minimal_parse_of_nonterminal (G := G) str initial_nonterminals_data str1 nonterminal0 ->
                             Pv (str : String, initial_nonterminals_data) str initial_nonterminals_data nonterminal0)
                (Hinit' : forall str,
                            str ≤s str0 ->
                            forall nonterminal0 : String.string,
                              minimal_parse_of_nonterminal (G := G)
                                                    str0 (remove_nonterminal valid nonterminal) str nonterminal0 ->
                              Pv (str0, remove_nonterminal valid nonterminal) str0 (remove_nonterminal valid nonterminal) nonterminal0)
          : minimal_parse_of_nonterminal (G := G) str0 valid str nonterminal
            -> parse_nonterminal_step (G := G) parse_nonterminal pf nonterminal.
          Proof.
            unfold parse_nonterminal_step.
            edestruct lt_dec as [|n].
            { intros H'.
              inversion H'; clear H'; subst. (* Work around Anomaly: Evar ?425 was not declared. Please report. *)
              { eapply parse_productions_complete; [ .. | eassumption ];
                trivial.
                intros; apply split_string_for_production_complete; assumption. }
              { match goal with
                  | [ H : _ < _, H' : beq _ _ |- _ ]
                    => exfalso; clear -H H' HSLP; setoid_subst; abstract omega
                end. } }
            { destruct pf as [pf|]; subst.
              { destruct (n pf). }
              { edestruct dec as [|pf']; simpl.
                { intro H'.
                  inversion_clear H'.
                  { match goal with
                      | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
                    end. }
                  { let H' := match goal with H : minimal_parse_of _ _ _ _ |- _ => constr:H end in
                    eapply parse_productions_complete in H'; eauto.
                    eapply (@parse_nonterminal_complete (_, _)).
                    intros; apply split_string_for_production_complete; assumption. } }
                { intro H''; exfalso; clear -n H'' pf'.
                  abstract (
                      inversion_clear H'';
                      (omega || congruence)
                    ). } } }
          Qed.
        End step.

        Section step_extensional.
          Lemma parse_nonterminal_step_ext (str0 : String) (valid : nonterminals_listT)
                (parse_nonterminal1 parse_nonterminal2: forall (p : String * nonterminals_listT),
                                            prod_relation (ltof _ length) nonterminals_listT_R p (str0, valid)
                                            -> forall str : String, str ≤s fst p -> String.string -> bool)
                (str : String) (pf : str ≤s str0) (nonterminal : String.string)
                (ext : forall p pf0 str' pf' nonterminal', parse_nonterminal1 p pf0 str' pf' nonterminal'
                                                    = parse_nonterminal2 p pf0 str' pf' nonterminal')
          : parse_nonterminal_step (G := G) parse_nonterminal1 pf nonterminal
            = parse_nonterminal_step (G := G) parse_nonterminal2 pf nonterminal.
          Proof.
            unfold parse_nonterminal_step.
            edestruct lt_dec.
            { apply parse_productions_ext; auto. }
            { edestruct dec; trivial.
              apply parse_productions_ext; auto. }
          Qed.
        End step_extensional.

        Section wf.
          Lemma parse_nonterminal_or_abort_sound
                (p : String * nonterminals_listT) (str : String)
                (pf : str ≤s fst p)
                (nonterminal : String.string)
          : parse_nonterminal_or_abort (G := G) p pf nonterminal
            -> parse_of_item G str (NonTerminal nonterminal).
          Proof.
            unfold parse_nonterminal_or_abort.
            revert str pf nonterminal.
            let Acca := match goal with |- context[@Fix _ _ ?Rwf _ _ ?a _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str pf nonterminal.
            rewrite Fix3_eq.
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
                (Pv := fun (p : String * nonterminals_listT)
                           (str0 : String) (valid0 : nonterminals_listT) (nt : String.string) =>
                         is_valid_nonterminal initial_nonterminals_data nt
                         /\ sub_nonterminals_listT valid0 (snd p)
                         /\ sub_nonterminals_listT (snd p) initial_nonterminals_data)
                (p : String * nonterminals_listT)
          : @parse_nonterminal_completeT
              (fst p)
              (parse_nonterminal_or_abort (G := G) p)
              (Pv p).
          Proof.
            unfold parse_nonterminal_or_abort.

            let Acca := match goal with |- context[@Fix _ _ ?Rwf _ _ ?a] => constr:(Rwf a) end in
            induction (Acca) as [x ? IHr];
              intros valid str pf nonterminal ?.
            rewrite Fix3_eq;
              [
              | solve [ intros;
                        apply parse_nonterminal_step_ext;
                        trivial ] ].
            match goal with
              | [ H : appcontext[?f]
                  |- _ -> is_true (parse_nonterminal_step (fun y _ b c d => ?f y b c d) _ _ ) ]
                => revert H;
                  generalize f;
                  let H' := fresh "parse_nonterminal_step'" in
                  intros H' H
            end.
            destruct_head_hnf and.
            intro; eapply parse_nonterminal_step_complete with (Pv := Pv); subst Pv;
            [ intros; eapply IHr | .. ];
            instantiate;
            trivial; simpl in *;
            try solve [ assumption
                      | intros; reflexivity
                      | intros; repeat split; reflexivity
                      | intros; repeat split;
                        try inversion_one_head @minimal_parse_of_nonterminal;
                        try solve [ reflexivity
                                  | assumption
                                  | etransitivity; [ apply sub_nonterminals_listT_remove; apply remove_nonterminal_1 | assumption ] ] ];
            [].
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
            apply parse_nonterminal_or_abort_sound.
          Defined.

          Lemma parse_nonterminal_complete'
                (str : String)
                (nonterminal : String.string)
                (H_init : is_valid_nonterminal initial_nonterminals_data nonterminal)
          : minimal_parse_of_nonterminal (G := G) str initial_nonterminals_data str nonterminal
            -> parse_nonterminal (G := G) str nonterminal
               = true.
          Proof.
            unfold parse_nonterminal.
            eapply (@parse_nonterminal_or_abort_complete
                    (str : String, initial_nonterminals_data)).
            repeat split; try reflexivity; assumption.
          Defined.

          Lemma parse_nonterminal_complete
                (str : String)
                (nonterminal : String.string)
                (p : parse_of G str (Lookup G nonterminal))
                (H_valid_tree : Forall_parse_of_item
                                  (fun _ p =>
                                     is_valid_nonterminal initial_nonterminals_data p = true) (ParseNonTerminal _ p))
          : parse_nonterminal (G := G) str nonterminal = true.
          Proof.
            apply parse_nonterminal_complete'; try assumption.
            { exact (fst H_valid_tree). }
            { pose proof (@minimal_parse_of_nonterminal__of__parse_of_nonterminal
                            Char _ _ G
                            _
                            _
                            (S (size_of_parse_item (ParseNonTerminal _ p)))
                            str str
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
              { exfalso; congruence. } }
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

  Definition parse_nonterminal_correct
  : (parse_nonterminal (G := G) str nt -> parse_of_item G str (NonTerminal nt))
    * (forall p : parse_of G str (G nt),
         Forall_parse_of_item
           (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt)
           (ParseNonTerminal _ p)
         -> parse_nonterminal (G := G) str nt).
  Proof.
    split.
    { apply parse_nonterminal_sound. }
    { apply parse_nonterminal_complete; exact _. }
  Defined.
End correct.
