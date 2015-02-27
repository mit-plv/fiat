(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.BooleanRecognizer Parsers.MinimalParse.
Require Import Parsers.MinimalParseOfParse.
Require Import Parsers.ContextFreeGrammarProperties Parsers.WellFoundedParse.
Require Import Common Common.Wf.
Require Import Eqdep_dec.

Local Hint Extern 0 =>
match goal with
  | [ H : false = true |- _ ] => solve [ destruct (Bool.diff_false_true H) ]
  | [ H : true = false |- _ ] => solve [ destruct (Bool.diff_true_false H) ]
end.

Coercion is_true (b : bool) := b = true.

Local Open Scope string_like_scope.

Section sound.
  Section general.
    Context CharType (String : string_like CharType) (G : grammar CharType).
    Context (names_listT : Type)
            (initial_names_data : names_listT)
            (is_valid_name : names_listT -> string -> bool)
            (remove_name : names_listT -> string -> names_listT)
            (names_listT_R : names_listT -> names_listT -> Prop)
            (remove_name_dec : forall ls name, is_valid_name ls name = true
                                               -> names_listT_R (remove_name ls name) ls)
            (ntl_wf : well_founded names_listT_R)
            (split_stateT : String -> Type)
            (remove_name_1
             : forall ls ps ps',
                 is_valid_name (remove_name ls ps) ps' = true
                 -> is_valid_name ls ps' = true)
            (remove_name_2
             : forall ls ps ps',
                 is_valid_name (remove_name ls ps) ps' = false
                 <-> is_valid_name ls ps' = false \/ ps = ps')
            (split_string_for_production
             : forall (str0 : StringWithSplitState String split_stateT) (prod : production CharType), list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
            (split_string_for_production_correct
             : forall (str0 : StringWithSplitState String split_stateT) prod,
                 List.Forall (fun s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                              => fst s1s2 ++ snd s1s2 =s str0)
                             (split_string_for_production str0 prod)).

    Let P : string -> Prop
      := fun p => is_valid_name initial_names_data p = true.

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      (*Let H_subT valid
        := sub_productions_listT is_valid_name valid initial_names_data.*)

      Section item.
        Context (str : StringWithSplitState String split_stateT)
                (str_matches_name : string -> bool).

        Definition str_matches_name_soundT
          := forall name, str_matches_name name = true
                          -> parse_of_item _ G str (NonTerminal _ name).

        Definition str_matches_name_completeT P str0
          := forall (valid : names_listT) name (H_sub : P str0 valid name),
               minimal_parse_of_item _ G initial_names_data is_valid_name remove_name str0 valid str (NonTerminal _ name)
               -> str_matches_name name = true.

        Lemma parse_item_sound
              (str_matches_name_sound : str_matches_name_soundT)
              (it : item CharType)
        : parse_item str str_matches_name it = true -> parse_of_item _ G str it.
        Proof.
          unfold parse_item, str_matches_name_soundT in *.
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
              (str_matches_name_complete : str_matches_name_completeT Pv str0)
              (it : item CharType)
              (Hinit : forall name,
                         minimal_parse_of_name String G initial_names_data is_valid_name remove_name str0 valid str name
                         -> Pv str0 valid name)
        : minimal_parse_of_item _ G initial_names_data is_valid_name remove_name str0 valid str it
          -> parse_item str str_matches_name it = true.
        Proof.
          unfold parse_item, str_matches_name_completeT in *.
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
              | [ |- str_matches_name _ = true ]
                => eapply str_matches_name_complete; [..| eassumption ]
              | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion_clear H
              | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _ _) |- _ ] => inversion_clear H
              | [ H : forall name, _ -> Pv _ _ name |- Pv _ _ _ ] => eapply H
          end.
        Qed.
      End item.

      Section item_ext.
        Lemma parse_item_ext
              (str : StringWithSplitState String split_stateT)
              (str_matches_name1 str_matches_name2 : string -> bool)
              (it : item CharType)
              (ext : forall x, str_matches_name1 x = str_matches_name2 x)
        : parse_item str str_matches_name1 it
          = parse_item str str_matches_name2 it.
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
        Context (str0 : StringWithSplitState String split_stateT)
                (parse_name : forall (str : StringWithSplitState String split_stateT),
                                str ≤s str0
                                -> string
                                -> bool).

        Definition parse_name_soundT
          := forall str pf name,
               @parse_name str pf name = true
               -> parse_of_item _ G str (NonTerminal _ name).

        Definition parse_name_completeT P
          := forall valid (str : StringWithSplitState String split_stateT) pf name (H_sub : P str0 valid name),
               minimal_parse_of_name _ G initial_names_data is_valid_name remove_name str0 valid str name
               -> @parse_name str pf name = true.

        Definition split_correctT
                   (str1 : StringWithSplitState String split_stateT)
                   (split : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT)
          := fst split ++ snd split =s str1.

        Definition split_list_correctT str1 (split_list : list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
          := List.Forall (@split_correctT str1) split_list.

        Definition split_list_completeT
                   valid1 valid2
                   (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                   (split_list : list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
                   (prod : production CharType)
          := match prod return Type with
               | nil => True
               | it::its => ({ s1s2 : String * String
                                      & (fst s1s2 ++ snd s1s2 =s str)
                                        * (minimal_parse_of_item _ G initial_names_data is_valid_name remove_name str0 valid1 (fst s1s2) it)
                                        * (minimal_parse_of_production _ G initial_names_data is_valid_name remove_name str0 valid2 (snd s1s2) its) }%type)
                            -> ({ s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                                         & (In s1s2 split_list)
                                           * (minimal_parse_of_item _ G initial_names_data is_valid_name remove_name str0 valid1 (fst s1s2) it)
                                           * (minimal_parse_of_production _ G initial_names_data is_valid_name remove_name str0 valid2 (snd s1s2) its) }%type)
             end.

        Lemma parse_production_sound
                 (parse_name_sound : parse_name_soundT)
                 (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                 (prod : production CharType)
        : parse_production split_string_for_production split_string_for_production_correct str0 parse_name str pf prod = true
          -> parse_of_production _ G str prod.
        Proof.
          change (forall str0 prod, split_list_correctT str0 (split_string_for_production str0 prod)) in split_string_for_production_correct.
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
                 end.
          { constructor;
            solve [ eapply IHprod; eassumption
                  | eapply parse_item_sound; try eassumption;
                    hnf in parse_name_sound |- *;
                    apply parse_name_sound ]. }
        Defined.

        Lemma parse_production_complete
              valid Pv
              (parse_name_complete : parse_name_completeT Pv)
              (split_string_for_production_complete : forall valid1 valid2 str pf prod, @split_list_completeT valid1 valid2 str pf (split_string_for_production str prod) prod)
              (Hinit : forall str (pf : str ≤s str0) name,
                         minimal_parse_of_name String G initial_names_data is_valid_name remove_name str0 valid str name
                         -> Pv str0 valid name)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
              (prod : production CharType)
        : minimal_parse_of_production _ G initial_names_data is_valid_name remove_name str0 valid str prod
          -> parse_production split_string_for_production split_string_for_production_correct str0 parse_name str pf prod = true.
        Proof.
          change (forall str0 prod, split_list_correctT str0 (split_string_for_production str0 prod)) in split_string_for_production_correct.
          revert valid str Hinit pf; induction prod;
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
                   | [ H : ?s ≤s _ |- context[split_string_for_production_correct {| string_val := ?s ; state_val := ?st |} ?p] ]
                     => specialize (fun a b p0 v1 p1 v2 p2
                                    => @split_string_for_production_complete v1 v2 {| string_val := s ; state_val := st |} H p (existT _ (a, b) (p0, p1, p2)))
                   | [ H : forall a b, is_true (string_val a ++ string_val b =s _ ++ _) -> _ |- _ ]
                     => specialize (fun st0 st1 => H {| state_val := st0 |} {| state_val := st1 |} (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : forall a b, is_true (a ++ b =s _ ++ _) -> _ |- _ ]
                     => specialize (H _ _ (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : ?a -> ?b, H' : ?a |- _ ] => specialize (H H')
                   | [ H : forall v : names_listT, @?a v -> @?b v |- _ ]
                     => pose proof (H valid); pose proof (H initial_names_data); clear H
                   | [ |- fold_right orb false (map _ _) = true ] => apply fold_right_orb_map_sig2
                   | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; clear H; subst
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
                 end;
          match goal with
            | [ H : In (?s1, ?s2) (split_string_for_production {| string_val := ?str ; state_val := ?st |} ?prod)
                |- { x : { s1s2 : _ | (?f (fst s1s2) ++ ?f (snd s1s2) =s ?str) = true } | _ } ]
              => let H' := fresh in
                 pose proof (proj1 (@Forall_forall _ _ _) (@split_string_for_production_correct {| string_val := str ; state_val := st |} prod) _ H) as H';
                   unfold split_correctT in H';
                   refine (exist _ (exist _ (s1, s2) _) _);
                   simpl in *
          end;
          repeat match goal with
                   | _ => split
                   | [ |- (_ && _)%bool = true ] => apply Bool.andb_true_iff
                   | [ |- (_ =s _) = true ] => apply bool_eq_correct
                   | [ |- In _ (combine_sig _) ] => apply In_combine_sig
                   | [ IHprod : _ |- _ ] => eapply IHprod; eassumption
                 end;
          eapply parse_name_complete; [..| eassumption ]; simpl;
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
              (str0 : StringWithSplitState String split_stateT)
              (parse_name1 parse_name2 : forall (str : StringWithSplitState String split_stateT),
                                           str ≤s str0
                                           -> string
                                           -> bool)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (prod : production CharType)
              (ext : forall str' pf' name', parse_name1 str' pf' name'
                                            = parse_name2 str' pf' name')
        : parse_production split_string_for_production split_string_for_production_correct str0 parse_name1 str pf prod
          = parse_production split_string_for_production split_string_for_production_correct str0 parse_name2 str pf prod.
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
        Context (str0 : StringWithSplitState String split_stateT)
                (parse_name : forall (str : StringWithSplitState String split_stateT),
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
                   | [ H : parse_production _ _ _ _ _ _ _ = true |- _ ] => apply parse_production_sound in H; try eassumption; []
                   | _ => left; eapply parse_production_complete; eassumption
                   | _ => solve [ eauto ]
                 end.

        Lemma parse_productions_sound
                 (parse_name_sound : parse_name_soundT str0 parse_name)
                 (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
                 (prods : productions CharType)
        : parse_productions split_string_for_production split_string_for_production_correct str0 parse_name str pf prods = true
          -> parse_of _ G str prods.
        Proof.
          change (forall str0 prod, split_list_correctT str0 (split_string_for_production str0 prod)) in split_string_for_production_correct.
          destruct str as [str st]; simpl in *.
          revert str pf st; induction prods; simpl.
          { unfold parse_productions; simpl; intros ??? H; exfalso; clear -H.
            abstract discriminate. }
          { unfold parse_productions in *; simpl in *.
            parse_productions_t. }
        Defined.

        Lemma parse_productions_complete
              valid Pv
              (parse_name_complete : parse_name_completeT str0 parse_name Pv)
              (split_string_for_production_complete : forall valid1 valid2 str pf prod, @split_list_completeT str0 valid1 valid2 str pf (split_string_for_production str prod) prod)
              (Hinit : forall str (pf : str ≤s str0) name,
                         minimal_parse_of_name String G initial_names_data is_valid_name remove_name str0 valid str name
                         -> Pv str0 valid name)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
              (prods : productions CharType)
        : minimal_parse_of _ G initial_names_data is_valid_name remove_name str0 valid str prods
          -> parse_productions split_string_for_production split_string_for_production_correct str0 parse_name str pf prods = true.
        Proof.
          change (forall str0 prod, split_list_correctT str0 (split_string_for_production str0 prod)) in split_string_for_production_correct.
          destruct str as [str st]; simpl in *.
          revert str pf st; induction prods; simpl.
          { unfold parse_productions; simpl; intros ??? H; exfalso; clear -H.
            abstract inversion H. }
          { unfold parse_productions in *; simpl in *.
            parse_productions_t. }
        Defined.
      End productions.

      Section productions_ext.
        Lemma parse_productions_ext
              (str0 : StringWithSplitState String split_stateT)
              (parse_name1 parse_name2 : forall (str : StringWithSplitState String split_stateT),
                                           str ≤s str0
                                           -> string
                                           -> bool)
              (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (prods : productions CharType)
              (ext : forall str' pf' name', parse_name1 str' pf' name'
                                            = parse_name2 str' pf' name')
        : parse_productions split_string_for_production split_string_for_production_correct str0 parse_name1 str pf prods
          = parse_productions split_string_for_production split_string_for_production_correct str0 parse_name2 str pf prods.
        Proof.
          revert str pf.
          induction prods as [|? ? IHprod]; simpl; intros; try reflexivity; [].
          unfold parse_productions; simpl.
          apply f_equal2; [ apply parse_production_ext | apply IHprod ].
          intros; apply ext.
        Qed.
      End productions_ext.

      Section names.
        Section step.
          Context (str0 : StringWithSplitState String split_stateT) (valid : names_listT)
                  (parse_name
                   : forall (p : StringWithSplitState String split_stateT * names_listT),
                       prod_relation (ltof _ (fun s : StringWithSplitState String split_stateT => Length s)) names_listT_R p (str0, valid)
                       -> forall str : StringWithSplitState String split_stateT, str ≤s fst p -> string -> bool).

          Lemma parse_name_step_sound
                (parse_name_sound : forall p pf, parse_name_soundT _ (@parse_name p pf))
                (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (name : string)
          : parse_name_step G initial_names_data is_valid_name remove_name
                            remove_name_dec split_string_for_production
                            split_string_for_production_correct parse_name _ pf name
            = true
            -> parse_of_item _ G str (NonTerminal _ name).
          Proof.
            unfold parse_name_step.
            intro H'; constructor; revert H'.
            edestruct lt_dec as [|n].
            { intro H'.
              apply parse_productions_sound in H'; trivial. }
            { edestruct dec; [ | intro H''; exfalso; clear -H'';
                                 abstract discriminate ].
              apply strle_to_sumbool in pf.
              destruct pf as [pf|]; subst.
              { destruct (n pf). }
              { intro H'.
                apply parse_productions_sound in H'; trivial;
                destruct_head @StringWithSplitState; subst; trivial. } }
          Defined.

          Lemma parse_name_step_complete
                Pv
                (parse_name_complete : forall p pf, parse_name_completeT _ (@parse_name p pf) (Pv p))
                (split_string_for_production_complete : forall str0 valid1 valid2 str pf prod, @split_list_completeT str0 valid1 valid2 str pf (split_string_for_production str prod) prod)
                (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (name : string)
                (Hinit : forall str1,
                           str1 ≤s str ->
                           forall name0,
                             minimal_parse_of_name String G initial_names_data is_valid_name
                                                   remove_name str initial_names_data str1 name0 ->
                             Pv (str, initial_names_data) str initial_names_data name0)
                (Hinit' : forall str,
                            str ≤s str0 ->
                            forall name0 : string,
                              minimal_parse_of_name String G initial_names_data is_valid_name remove_name
                                                    str0 (remove_name valid name) str name0 ->
                              Pv (str0, remove_name valid name) str0 (remove_name valid name) name0)
          : minimal_parse_of_name _ G initial_names_data is_valid_name remove_name str0 valid str name
            -> parse_name_step G initial_names_data is_valid_name remove_name
                            remove_name_dec split_string_for_production
                            split_string_for_production_correct parse_name _ pf name
            = true.
          Proof.
            unfold parse_name_step.
            edestruct lt_dec as [|n].
            { intros H'.
              inversion H'; clear H'; subst. (* Work around Anomaly: Evar ?425 was not declared. Please report. *)
              { eapply parse_productions_complete; [ .. | eassumption ];
                trivial. }
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
                    eapply (@parse_name_complete (_, _)). } }
                { intro H''; exfalso; clear -n H'' pf'.
                  abstract (
                      inversion_clear H'';
                      (omega || congruence)
                    ). } } }
          Qed.
        End step.

        Section step_extensional.
          Lemma parse_name_step_ext (str0 : StringWithSplitState String split_stateT) (valid : names_listT)
                (parse_name1 parse_name2: forall (p : StringWithSplitState String split_stateT * names_listT),
                                            prod_relation (ltof _ (fun s : StringWithSplitState String split_stateT => Length s)) names_listT_R p (str0, valid)
                                            -> forall str : StringWithSplitState String split_stateT, str ≤s fst p -> string -> bool)
                (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) (name : string)
                (ext : forall p pf0 str' pf' name', parse_name1 p pf0 str' pf' name'
                                                    = parse_name2 p pf0 str' pf' name')
          : parse_name_step G initial_names_data is_valid_name remove_name
                            remove_name_dec split_string_for_production
                            split_string_for_production_correct parse_name1 _ pf name
            = parse_name_step G initial_names_data is_valid_name remove_name
                              remove_name_dec split_string_for_production
                              split_string_for_production_correct parse_name2 _ pf name.
          Proof.
            unfold parse_name_step.
            edestruct lt_dec.
            { apply parse_productions_ext; auto. }
            { edestruct dec; trivial.
              apply parse_productions_ext; auto. }
          Qed.
        End step_extensional.

        Section wf.
          Lemma parse_name_or_abort_sound
                (p : StringWithSplitState String split_stateT * names_listT) (str : StringWithSplitState String split_stateT)
                (pf : str ≤s fst p)
                (name : string)
          : parse_name_or_abort G initial_names_data is_valid_name remove_name
                                remove_name_dec ntl_wf split_string_for_production
                                split_string_for_production_correct
                                p _ pf name
            = true
            -> parse_of_item _ G str (NonTerminal _ name).
          Proof.
            unfold parse_name_or_abort.
            revert str pf name.
            let Acca := match goal with |- context[@Fix3 _ _ _ _ _ ?Rwf _ _ ?a _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str pf name.
            rewrite Fix3_eq.
            { apply parse_name_step_sound; assumption. }
            { intros.
              apply parse_name_step_ext.
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

          Lemma parse_name_or_abort_complete
                (split_string_for_production_complete : forall str0 valid1 valid2 str pf prod, @split_list_completeT str0 valid1 valid2 str pf (split_string_for_production str prod) prod)
                (Pv := fun (p : StringWithSplitState String split_stateT * names_listT)
                           (str0 : StringWithSplitState String split_stateT) (valid0 : names_listT) (_ : string) =>
                         sub_names_listT is_valid_name valid0 (snd p)
                         /\ sub_names_listT is_valid_name (snd p) initial_names_data)
                (p : StringWithSplitState String split_stateT * names_listT)
          : @parse_name_completeT
              (fst p)
              (parse_name_or_abort G initial_names_data is_valid_name remove_name
                                   remove_name_dec ntl_wf split_string_for_production
                                   split_string_for_production_correct
                                   p)
              (Pv p).
          Proof.
            unfold parse_name_or_abort.
            let Acca := match goal with |- context[@Fix3 _ _ _ _ _ ?Rwf _ _ ?a] => constr:(Rwf a) end in
            induction (Acca) as [x ? IHr];
              intros valid str pf name ?.
            rewrite Fix3_eq;
              [
              | solve [ intros;
                        apply parse_name_step_ext;
                        trivial ] ].
            match goal with
              | [ H : appcontext[?f]
                  |- _ -> parse_name_step _ _ _ _ _ _ _ (fun y _ b c d => ?f y b c d) _ _ _ = true ]
                => revert H;
                  generalize f;
                  let H' := fresh "parse_name_step'" in
                  intros H' H
            end.
            destruct_head_hnf and.
            intro; eapply parse_name_step_complete with (Pv := Pv); subst Pv;
            [ intros; eapply IHr | .. ];
            instantiate;
            trivial; simpl in *;
            try solve [ intros; reflexivity
                      | intros; split; reflexivity
                      | intros; split; try reflexivity;
                        etransitivity; [ apply sub_names_listT_remove; assumption | assumption ] ].
            { eapply expand_minimal_parse_of_name; [ .. | eassumption ];
              trivial;
              try reflexivity. }
          Defined.

          Lemma parse_name_sound
                (str : StringWithSplitState String split_stateT) (name : string)
          : parse_name G initial_names_data is_valid_name remove_name
                       remove_name_dec ntl_wf split_string_for_production
                       split_string_for_production_correct
                       str name
            = true
            -> parse_of_item _ G str (NonTerminal _ name).
          Proof.
            unfold parse_name, parse_name_or_abort.
            apply parse_name_or_abort_sound.
          Defined.

          Lemma parse_name_complete
                (split_string_for_production_complete : forall str0 valid1 valid2 str pf prod, @split_list_completeT str0 valid1 valid2 str pf (split_string_for_production str prod) prod)
                (str : StringWithSplitState String split_stateT)
                (name : string)
          : minimal_parse_of_name String G initial_names_data is_valid_name remove_name str initial_names_data str name
            -> parse_name G initial_names_data is_valid_name remove_name
                          remove_name_dec ntl_wf split_string_for_production
                          split_string_for_production_correct
                          str name
               = true.
          Proof.
            unfold parse_name.
            eapply (@parse_name_or_abort_complete
                    split_string_for_production_complete
                    (str, initial_names_data)).
            split; reflexivity.
          Defined.
        End wf.
      End names.
    End parts.
  End general.
End sound.

Section brute_force_spliter.
  Lemma make_all_single_splits_complete_helper
  : forall (str : String_with_no_state string_stringlike)
           (s1s2 : String_with_no_state string_stringlike * String_with_no_state string_stringlike),
      fst s1s2 ++ snd s1s2 =s str -> In s1s2 (make_all_single_splits str).
  Proof.
    intros [str [] ] [ [s1 [] ] [s2 [] ] ] H.
    apply bool_eq_correct in H; simpl in *; subst.
    revert s2.
    induction s1; simpl in *.
    { intros.
      destruct s2; left; simpl; reflexivity. }
    { intros; right.
      refine (@in_map _ _ _ _ ({| string_val := s1 |}, {| string_val := s2 |}) _).
      apply IHs1. }
  Qed.

  Lemma make_all_single_splits_complete
  : forall G names_listT initial_names_data is_valid_name remove_name str0 valid0 valid1 str pf prod, @split_list_completeT _ string_stringlike G names_listT initial_names_data is_valid_name remove_name _ str0 valid0 valid1 str pf (@make_all_single_splits str) prod.
  Proof.
    intros; hnf.
    destruct prod; trivial.
    intros [ [s1 s2] [ [ p1 p2 ] p3 ] ].
    exists ({| string_val := s1 ; state_val := I |}, {| string_val := s2 ; state_val := I |}).
    abstract (
        repeat split; try assumption;
        apply make_all_single_splits_complete_helper;
        assumption
      ).
  Defined.
End brute_force_spliter.

Section brute_force_make_parse_of.
  Variable G : grammar Ascii.ascii.

  Definition brute_force_make_parse_of_sound
             (str : @String Ascii.ascii string_stringlike)
             (name : string)
  : brute_force_make_parse_of G str name = true -> parse_of_item _ G str (NonTerminal _ name).
  Proof.
    unfold brute_force_make_parse_of.
    apply parse_name_sound.
  Defined.

  Definition brute_force_make_parse_of_complete
             (str : @String Ascii.ascii string_stringlike)
             (name : string)
  : minimal_parse_of_name _ G (Valid_nonterminal_symbols G) rdp_list_is_valid_name rdp_list_remove_name str (Valid_nonterminal_symbols G) str name
    -> brute_force_make_parse_of G str name = true.
  Proof.
    unfold brute_force_make_parse_of; simpl; intro.
    eapply parse_name_complete; try eassumption.
    { apply rdp_list_remove_name_1. }
    { apply rdp_list_remove_name_2. }
    { apply make_all_single_splits_complete. }
  Defined.

  Definition brute_force_make_parse_of_complete_p
             (str : @String Ascii.ascii string_stringlike)
             (name : string)
             (p : parse_of _ G str (Lookup G name))
             (H_valid_name : rdp_list_is_valid_name (Valid_nonterminal_symbols G) name = true)
             (H_valid_tree : Forall_parse_of
                               (fun _ p =>
                                  rdp_list_is_valid_name (Valid_nonterminal_symbols G) p = true) p)
  : brute_force_make_parse_of G str name = true.
  Proof.
    apply brute_force_make_parse_of_complete.
    pose proof (@minimal_parse_of_name__of__parse_of_name
                  _ string_stringlike G
                  rdp_list_names_listT
                  (Valid_nonterminal_symbols G)
                  rdp_list_is_valid_name rdp_list_remove_name
                  rdp_list_remove_name_1
                  rdp_list_remove_name_2
                  (S (size_of_parse_item (ParseNonTerminal name p)))
                  str str
                  (Valid_nonterminal_symbols G)
                  name
                  p
                  (Lt.lt_n_Sn _)
                  (reflexivity _)
                  (reflexivity _)
                  (H_valid_name, H_valid_tree))
      as p'.
    destruct p' as [ [ p' ] | [ name' [ [ H0 H1 ] ] ] ].
    { exact p'. }
    { exfalso; congruence. }
  Qed.
End brute_force_make_parse_of.
