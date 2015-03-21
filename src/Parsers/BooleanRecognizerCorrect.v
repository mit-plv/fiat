(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
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

Local Coercion is_true : bool >-> Sortclass.

Local Open Scope string_like_scope.

Section sound.
  Section general.
    Context CharType (String : string_like CharType) (G : grammar CharType).
    Context `{data : @boolean_parser_dataT CharType String}.
    Context `{cdata : @boolean_parser_completeness_dataT' _ String G data}.

    Let P : string -> Prop
      := fun p => is_valid_nonterminal initial_nonterminals_data p = true.

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      (*Let H_subT valid
        := sub_productions_listT is_valid_nonterminal valid initial_nonterminals_data.*)

      Section item.
        Context (str : StringWithSplitState String split_stateT)
                (str_matches_nonterminal : string -> bool).

        Definition str_matches_nonterminal_soundT
          := forall nonterminal, str_matches_nonterminal nonterminal = true
                          -> parse_of_item _ G str (NonTerminal _ nonterminal).

        Definition str_matches_nonterminal_completeT P str0
          := forall (valid : nonterminals_listT) nonterminal (H_sub : P str0 valid nonterminal),
               minimal_parse_of_item _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str (NonTerminal _ nonterminal)
               -> str_matches_nonterminal nonterminal = true.

        Lemma parse_item_sound
              (str_matches_nonterminal_sound : str_matches_nonterminal_soundT)
              (it : item CharType)
        : parse_item str_matches_nonterminal str it = true -> parse_of_item _ G str it.
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
                   | [ H : StringWithSplitState _ _ |- _ ] => destruct H
                 end.
        Defined.

        Lemma parse_item_complete
              str0
              valid Pv
              (str_matches_nonterminal_complete : str_matches_nonterminal_completeT Pv str0)
              (it : item CharType)
              (Hinit : forall nonterminal,
                         minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
                         -> Pv str0 valid nonterminal)
        : minimal_parse_of_item _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str it
          -> parse_item str_matches_nonterminal str it = true.
        Proof.
          unfold parse_item, str_matches_nonterminal_completeT in *.
          repeat
            repeat
            match goal with
              | _ => intro
              | _ => reflexivity
              | _ => eassumption
              | [ |- _ /\ _ ] => split
              | [ |- ?x < ?x \/ _ ] => right
              | [ H : ?T |- ?T \/ _ ] => left; exact H
              | [ |- ?x = ?x \/ _ ] => left; reflexivity
              | [ |- _ \/ ?x = ?x ] => right; reflexivity
              | [ |- _ = true ] => apply bool_eq_correct
              | [ H : context[?E] |- context[match ?E with _ => _ end] ] => destruct E
              | [ H : minimal_parse_of _ _ _ _ _ _ _ [] |- _ ] => solve [ inversion H ]
              | [ |- str_matches_nonterminal _ = true ]
                => eapply str_matches_nonterminal_complete; [..| eassumption ]
              | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion_clear H
              | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _ _) |- _ ] => inversion_clear H
              | [ H : forall nonterminal, _ -> Pv _ _ nonterminal |- Pv _ _ _ ] => eapply H
          end.
        Qed.
      End item.

      Section item_ext.
        Lemma parse_item_ext
              (str : StringWithSplitState String split_stateT)
              (str_matches_nonterminal1 str_matches_nonterminal2 : string -> bool)
              (it : item CharType)
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
                (parse_nonterminal : forall (str : StringWithSplitState String split_stateT),
                                str ≤s str0
                                -> string
                                -> bool).

        Definition parse_nonterminal_soundT
          := forall str pf nonterminal,
               @parse_nonterminal str pf nonterminal = true
               -> parse_of_item _ G str (NonTerminal _ nonterminal).

        Definition parse_nonterminal_completeT P
          := forall valid (str : StringWithSplitState String split_stateT) pf nonterminal (H_sub : P str0 valid nonterminal),
               minimal_parse_of_name _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
               -> @parse_nonterminal str pf nonterminal = true.

        Lemma parse_production_sound
                 (parse_nonterminal_sound : parse_nonterminal_soundT)
                 (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                 (prod : production CharType)
        : parse_production parse_nonterminal str pf prod = true
          -> parse_of_production _ G str prod.
        Proof.
          revert str pf; induction prod;
          repeat match goal with
                   | _ => intro
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => solve [ auto ]
                   | [ H : fold_right orb false (map _ _) = true |- _ ] => apply fold_right_orb_map_sig1 in H
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | _ => progress destruct_head sumbool
                   | _ => progress destruct_head and
                   | _ => progress destruct_head prod
                   | _ => progress destruct_head sig
                   | _ => progress destruct_head @StringWithSplitState
                   | _ => progress simpl in *
                   | _ => progress subst
                   | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
                   | [ H : (_ =s _) = true |- _ ]
                     => let H' := fresh in
                        pose proof H as H';
                          apply bool_eq_correct in H';
                          progress subst
                   | [ |- parse_of_production _ _ (_ ++ Empty _) [?it] ]
                     => constructor
                   | [ |- parse_of_item _ _ ?s _ ]
                     => eapply parse_item_sound with (str := {| string_val := s |});
                       hnf in *; solve [ eauto with nocore ]
                 end.
          { constructor;
            solve [ eapply IHprod; eassumption
                  | eapply parse_item_sound; try eassumption;
                    hnf in parse_nonterminal_sound |- *;
                    apply parse_nonterminal_sound ]. }
        Defined.

        Lemma parse_production_complete
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT Pv)
              (Hinit : forall str (pf : str ≤s str0) nonterminal,
                         minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
                         -> Pv str0 valid nonterminal)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
              (prod : production CharType)
              (split_string_for_production_complete'
               : forall str0 valid str pf,
                   Forall_tails
                     (fun prod' =>
                        match prod' return Type with
                          | nil => True
                          | it::its => split_list_completeT (G := G) (valid := valid) (str0 := str0) str pf (split_string_for_production it its str) it its
                        end)
                     prod)
        : minimal_parse_of_production _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str prod
          -> parse_production parse_nonterminal str pf prod = true.
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
                   | [ H : fold_right orb false (map _ _) = true |- _ ] => apply fold_right_orb_map_sig1 in H
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ nil |- _ ] => inversion_clear H
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
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
                   | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : ?s ≤s _ |- context[split_string_for_production_correct ?it ?p {| string_val := ?s ; state_val := ?st |}] ]
                     => pose proof
                          (fun a b p0 v p1 p2
                           => fst (@split_string_for_production_complete' _ v {| string_val := s ; state_val := st |} H) (existT _ (a, b) (p0, p1, p2)));
                       clear split_string_for_production_complete'
                   | [ H : forall a b, is_true (string_val a ++ string_val b =s _ ++ _) -> _ |- _ ]
                     => specialize (fun st0 st1 => H {| state_val := st0 |} {| state_val := st1 |} (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : forall a b, is_true (a ++ b =s _ ++ _) -> _ |- _ ]
                     => specialize (H _ _ (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : ?a -> ?b, H' : ?a |- _ ] => specialize (H H')
                   | [ H : forall v : nonterminals_listT, @?a v -> @?b v |- _ ]
                     => pose proof (H valid); pose proof (H initial_nonterminals_data); clear H
                   | [ |- fold_right orb false (map _ _) = true ] => apply fold_right_orb_map_sig2
                   | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; clear H; subst
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
                 end;
          (lazymatch goal with
            | [ H : In (?s1, ?s2) (split_string_for_production ?it ?prod {| string_val := ?str ; state_val := ?st |})
                |- { x : { s1s2 : _ | (?f (fst s1s2) ++ ?f (snd s1s2) =s ?str) = true } | _ } ]
              => let H' := fresh in
                 pose proof (proj1 (@Forall_forall _ _ _) (split_string_for_production_correct it prod {| string_val := str ; state_val := st |}) _ H) as H';
                   refine (exist _ (exist _ (s1, s2) _) _);
                   simpl in *
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
                          solve [ apply str_le1_append
                                | apply str_le2_append ]
                 end.
          Grab Existential Variables.
          assumption.
          assumption.
        Qed.
      End production.

      Section production_ext.
        Lemma parse_production_ext
              (str0 : String)
              (parse_nonterminal1 parse_nonterminal2 : forall (str : StringWithSplitState String split_stateT),
                                           str ≤s str0
                                           -> string
                                           -> bool)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (prod : production CharType)
              (ext : forall str' pf' nonterminal', parse_nonterminal1 str' pf' nonterminal'
                                            = parse_nonterminal2 str' pf' nonterminal')
        : parse_production parse_nonterminal1 str pf prod
          = parse_production parse_nonterminal2 str pf prod.
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
                (parse_nonterminal : forall (str : StringWithSplitState String split_stateT),
                                str ≤s str0
                                -> string
                                -> bool).

        Local Ltac parse_productions_t :=
          repeat match goal with
                   | _ => intro
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | [ |- (_ || _)%bool = true ] => apply Bool.orb_true_iff
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
                   | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
                   | _ => progress destruct_head_hnf sumbool
                   | _ => progress destruct_head_hnf and
                   | _ => progress destruct_head_hnf sig
                   | _ => progress destruct_head_hnf sigT
                   | _ => progress destruct_head_hnf Datatypes.prod
                   | _ => progress simpl in *
                   | _ => progress subst
                   | [ H : parse_of _ _ _ nil |- _ ] => solve [ inversion H ]
                   | [ H : parse_of _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : minimal_parse_of _ _ _ _ _ _ _ _ nil |- _ ] => solve [ inversion H ]
                   | [ H : minimal_parse_of _ _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : parse_production _ _ _ _ = true |- _ ] => apply parse_production_sound with (str := {| string_val := _ |}) in H; try eassumption; []
                   | _ => left; eapply parse_production_complete; eassumption
                   | _ => solve [ eauto ]
                 end.

        Lemma parse_productions_sound
                 (parse_nonterminal_sound : parse_nonterminal_soundT parse_nonterminal)
                 (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                 (prods : productions CharType)
        : parse_productions parse_nonterminal str pf prods = true
          -> parse_of _ G str prods.
        Proof.
          destruct str as [str st]; simpl in *.
          revert str pf st; induction prods; simpl.
          { unfold parse_productions; simpl; intros ??? H; exfalso; clear -H.
            abstract discriminate. }
          { unfold parse_productions in *; simpl in *.
            parse_productions_t. }
        Defined.

        Lemma parse_productions_complete
              valid Pv
              (parse_nonterminal_complete : parse_nonterminal_completeT parse_nonterminal Pv)
              (Hinit : forall str (pf : str ≤s str0) nonterminal,
                         minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
                         -> Pv str0 valid nonterminal)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
              (prods : productions CharType)
              (split_string_for_production_complete'
               : forall str0 valid str pf,
                   ForallT
                     (Forall_tails
                        (fun prod' =>
                           match prod' return Type with
                             | nil => True
                             | it::its => split_list_completeT (G := G) (valid := valid) (str0 := str0) str pf (split_string_for_production it its str) it its
                           end))
                     prods)
        : minimal_parse_of _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str prods
          -> parse_productions parse_nonterminal str pf prods = true.
        Proof.
          destruct str as [str st]; simpl in *.
          revert str pf st; induction prods; simpl.
          { unfold parse_productions; simpl; intros ??? H; exfalso; clear -H.
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
              (parse_nonterminal1 parse_nonterminal2 : forall (str : StringWithSplitState String split_stateT),
                                           str ≤s str0
                                           -> string
                                           -> bool)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (prods : productions CharType)
              (ext : forall str' pf' nonterminal', parse_nonterminal1 str' pf' nonterminal'
                                            = parse_nonterminal2 str' pf' nonterminal')
        : parse_productions parse_nonterminal1 str pf prods
          = parse_productions parse_nonterminal2 str pf prods.
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
                       prod_relation (ltof _ Length) nonterminals_listT_R p (str0, valid)
                       -> forall str : StringWithSplitState String split_stateT, str ≤s fst p -> string -> bool).

          Lemma parse_nonterminal_step_sound
                (parse_nonterminal_sound : forall p pf, parse_nonterminal_soundT (@parse_nonterminal p pf))
                (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (nonterminal : string)
          : parse_nonterminal_step (G := G) parse_nonterminal _ pf nonterminal
            = true
            -> parse_of_item _ G str (NonTerminal _ nonterminal).
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
                (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (nonterminal : string)
                (Hnt : is_valid_nonterminal initial_nonterminals_data nonterminal)
                (Hinit : forall str1,
                           str1 ≤s str ->
                           forall nonterminal0,
                             minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal
                                                   remove_nonterminal str initial_nonterminals_data str1 nonterminal0 ->
                             Pv (str : String, initial_nonterminals_data) str initial_nonterminals_data nonterminal0)
                (Hinit' : forall str,
                            str ≤s str0 ->
                            forall nonterminal0 : string,
                              minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal
                                                    str0 (remove_nonterminal valid nonterminal) str nonterminal0 ->
                              Pv (str0, remove_nonterminal valid nonterminal) str0 (remove_nonterminal valid nonterminal) nonterminal0)
          : minimal_parse_of_name _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
            -> parse_nonterminal_step (G := G) parse_nonterminal _ pf nonterminal
            = true.
          Proof.
            unfold parse_nonterminal_step.
            edestruct lt_dec as [|n].
            { intros H'.
              inversion H'; clear H'; subst. (* Work around Anomaly: Evar ?425 was not declared. Please report. *)
              { eapply parse_productions_complete; [ .. | eassumption ];
                trivial.
                intros; apply split_string_for_production_complete; assumption. }
              { destruct_head @StringWithSplitState; subst.
                match goal with
                  | [ H : ?x < ?x |- _ ] => exfalso; clear -H; abstract omega
                end. } }
            { destruct pf as [pf|]; subst.
              { destruct (n pf). }
              { edestruct dec as [|pf']; simpl.
                { intro H'.
                  inversion_clear H'.
                  { match goal with
                      | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
                    end. }
                  { let H' := match goal with H : minimal_parse_of _ _ _ _ _ _ _ _ _ |- _ => constr:H end in
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
                                            prod_relation (ltof _ Length) nonterminals_listT_R p (str0, valid)
                                            -> forall str : StringWithSplitState String split_stateT, str ≤s fst p -> string -> bool)
                (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (nonterminal : string)
                (ext : forall p pf0 str' pf' nonterminal', parse_nonterminal1 p pf0 str' pf' nonterminal'
                                                    = parse_nonterminal2 p pf0 str' pf' nonterminal')
          : parse_nonterminal_step (G := G) parse_nonterminal1 _ pf nonterminal
            = parse_nonterminal_step (G := G) parse_nonterminal2 _ pf nonterminal.
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
                (p : String * nonterminals_listT) (str : StringWithSplitState String split_stateT)
                (pf : str ≤s fst p)
                (nonterminal : string)
          : parse_nonterminal_or_abort (G := G) p _ pf nonterminal
            = true
            -> parse_of_item _ G str (NonTerminal _ nonterminal).
          Proof.
            unfold parse_nonterminal_or_abort.
            revert str pf nonterminal.
            let Acca := match goal with |- context[@Fix3 _ _ _ _ _ ?Rwf _ _ ?a _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str pf nonterminal.
            rewrite Fix3_eq.
            { apply parse_nonterminal_step_sound; assumption. }
            { intros.
              apply parse_nonterminal_step_ext.
              trivial. }
          Defined.

          Lemma prod_relation_elim_helper {A R x} {valid : A}
          : prod_relation (ltof String Length) R
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
                           (str0 : String) (valid0 : nonterminals_listT) (nt : string) =>
                         is_valid_nonterminal initial_nonterminals_data nt
                         /\ sub_names_listT is_valid_nonterminal valid0 (snd p)
                         /\ sub_names_listT is_valid_nonterminal (snd p) initial_nonterminals_data)
                (p : String * nonterminals_listT)
          : @parse_nonterminal_completeT
              (fst p)
              (parse_nonterminal_or_abort (G := G) p)
              (Pv p).
          Proof.
            unfold parse_nonterminal_or_abort.

            let Acca := match goal with |- context[@Fix3 _ _ _ _ _ ?Rwf _ _ ?a] => constr:(Rwf a) end in
            induction (Acca) as [x ? IHr];
              intros valid str pf nonterminal ?.
            rewrite Fix3_eq;
              [
              | solve [ intros;
                        apply parse_nonterminal_step_ext;
                        trivial ] ].
            match goal with
              | [ H : appcontext[?f]
                  |- _ -> parse_nonterminal_step (fun y _ b c d => ?f y b c d) _ _ _ = true ]
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
                        try inversion_one_head @minimal_parse_of_name;
                        try solve [ reflexivity
                                  | assumption
                                  | etransitivity; [ apply sub_names_listT_remove; apply remove_nonterminal_1 | assumption ] ] ];
            [].
            { eapply expand_minimal_parse_of_name; [ .. | eassumption ];
              trivial;
              try solve [ reflexivity
                        | apply remove_nonterminal_1
                        | apply remove_nonterminal_2 ]. }
          Defined.

          Lemma parse_nonterminal_sound
                (str : StringWithSplitState String split_stateT) (nonterminal : string)
          : parse_nonterminal (G := G) str nonterminal
            = true
            -> parse_of_item _ G str (NonTerminal _ nonterminal).
          Proof.
            unfold parse_nonterminal, parse_nonterminal_or_abort.
            apply parse_nonterminal_or_abort_sound.
          Defined.

          Lemma parse_nonterminal_complete'
                (str : StringWithSplitState String split_stateT)
                (nonterminal : string)
                (H_init : is_valid_nonterminal initial_nonterminals_data nonterminal)
          : minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str initial_nonterminals_data str nonterminal
            -> parse_nonterminal (G := G) str nonterminal
               = true.
          Proof.
            unfold parse_nonterminal.
            eapply (@parse_nonterminal_or_abort_complete
                    (str : String, initial_nonterminals_data)).
            repeat split; try reflexivity; assumption.
          Defined.

          Lemma parse_nonterminal_complete
                (str : StringWithSplitState String split_stateT)
                (nonterminal : string)
                (p : parse_of _ G str (Lookup G nonterminal))
                (H_valid_tree : Forall_parse_of_item
                                  (fun _ p =>
                                     is_valid_nonterminal initial_nonterminals_data p = true) (ParseNonTerminal _ p))
          : parse_nonterminal (G := G) str nonterminal = true.
          Proof.
            apply parse_nonterminal_complete'; try assumption.
            { exact (fst H_valid_tree). }
            { pose proof (@minimal_parse_of_name__of__parse_of_name
                            _ String G
                            nonterminals_listT
                            initial_nonterminals_data
                            is_valid_nonterminal remove_nonterminal
                            remove_nonterminal_1
                            remove_nonterminal_2
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
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Context `{cdata : @boolean_parser_correctness_dataT _ String G}.
  Context (str : StringWithSplitState String split_stateT)
          (nt : string).

  Definition parse_nonterminal_correct
  : (parse_nonterminal (G := G) str nt -> parse_of_item String G str (NonTerminal _ nt))
    * (forall p : parse_of String G str (G nt),
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

Section brute_force_make_parse_of.
  Variable G : grammar Ascii.ascii.

  Definition brute_force_parse_sound
             (str : @String Ascii.ascii string_stringlike)
  : brute_force_parse G str = true -> parse_of_item _ G str (NonTerminal _ G).
  Proof.
    unfold brute_force_parse, brute_force_parse_nonterminal.
    apply parse_nonterminal_sound.
  Defined.

  Definition brute_force_parse_complete'
             (str : @String Ascii.ascii string_stringlike)
  : minimal_parse_of_name _ G (Valid_nonterminals G) rdp_list_is_valid_nonterminal rdp_list_remove_nonterminal str (Valid_nonterminals G) str G
    -> brute_force_parse G str = true.
  Proof.
    unfold brute_force_parse, brute_force_parse_nonterminal.
    simpl; intro.
    eapply parse_nonterminal_complete'; try eassumption; try exact _.
    inversion_one_head @minimal_parse_of_name; assumption.
  Defined.

  Definition brute_force_parse_complete
             (str : @String Ascii.ascii string_stringlike)
             (p : parse_of _ G str G)
             (H_valid_tree : Forall_parse_of_item
                               (fun _ p =>
                                  rdp_list_is_valid_nonterminal (Valid_nonterminals G) p = true) (ParseNonTerminal _ p))
  : brute_force_parse G str = true.
  Proof.
    unfold brute_force_parse, brute_force_parse_nonterminal.
    eapply parse_nonterminal_complete; try eassumption; try exact _.
  Qed.
End brute_force_make_parse_of.
