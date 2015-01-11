(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.BooleanRecognizer Parsers.MinimalParse.
Require Import Common Common.ilist Common.Wf.
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
            (remove_name_1
             : forall ls ps ps',
                 is_valid_name (remove_name ls ps) ps' = true
                 -> is_valid_name ls ps' = true)
            (remove_name_2
             : forall ls ps ps',
                 is_valid_name (remove_name ls ps) ps' = false
                 <-> is_valid_name ls ps' = false \/ ps = ps')
            (split_string_for_production
             : forall (str0 : String) (prod : production CharType), list (String * String))
            (split_string_for_production_correct
             : forall str0 prod,
                 List.Forall (fun s1s2 => fst s1s2 ++ snd s1s2 =s str0)
                             (split_string_for_production str0 prod)).

    Let P : string -> Prop
      := fun p => is_valid_name initial_names_data p = true.

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      (*Let H_subT valid
        := sub_productions_listT is_valid_name valid initial_names_data.*)

      Section item.
        Context (str : String)
                (str_matches_name : string -> bool).

        Definition str_matches_name_soundT
          := forall name, str_matches_name name = true
                          -> parse_of_item _ G str (NonTerminal _ name).

        Definition str_matches_name_completeT P
          := forall valid name (H_sub : P valid name),
               minimal_parse_of_item _ G initial_names_data is_valid_name remove_name valid str (NonTerminal _ name)
               -> str_matches_name name = true.

        Lemma parse_item_sound
              (str_matches_name_sound : str_matches_name_soundT)
              (it : item CharType)
        : parse_item String str str_matches_name it = true -> parse_of_item _ G str it.
        Proof.
          unfold parse_item, str_matches_name_soundT in *.
          repeat match goal with
                   | _ => intro
                   | [ H : context[match ?E with _ => _ end] |- _ ] => atomic E; destruct E
                   | [ |- context[match ?E with _ => _ end] ] => atomic E; destruct E
                   | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                   | [ H : context[match ?E with _ => _ end] |- context[?E] ] => destruct E
                   | _ => progress subst
                   | _ => solve [ eauto ]
                 end.
        Defined.

        Lemma parse_item_complete
              valid Pv
              (H_sub : forall p, Pv (remove_name valid p) p)
              (str_matches_name_complete : str_matches_name_completeT Pv)
              (it : item CharType)
        : minimal_parse_of_item _ G initial_names_data is_valid_name remove_name valid str it
          -> parse_item String str str_matches_name it = true.
        Proof.
          unfold parse_item, str_matches_name_completeT in *.
          repeat match goal with
                   | _ => intro
                   | _ => reflexivity
                   | [ |- _ = true ] => apply bool_eq_correct
                   | [ H : minimal_parse_of_item _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion_clear H
                   | [ H : context[?E] |- context[match ?E with _ => _ end] ] => destruct E
                   | [ H : minimal_parse_of _ _ _ _ _ _ _ [] |- _ ] => solve [ inversion H ]
                   | [ |- str_matches_name _ = true ]
                     => eapply str_matches_name_complete; [..| eassumption ]
                   | [ H : minimal_parse_of_item _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion_clear H
                 end.
                   | _ => solve [ eauto using expand_minimal_parse_of, sub_names_listT_remove, remove_name_6 ]
               end.
          inversion X; subst.
          eapply str_matches_name_complete; [..| eassumption ]
          eapply str_matches_name_complete.
        Qed.*)
      End item.

      Section item_ext.
        Lemma parse_item_ext
              (str : String)
              (str_matches_name1 str_matches_name2 : string -> bool)
              (it : item CharType)
              (ext : forall x, str_matches_name1 x = str_matches_name2 x)
        : parse_item String str str_matches_name1 it
          = parse_item String str str_matches_name2 it.
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
                (parse_name : forall (str : String),
                                str ≤s str0
                                -> string
                                -> bool).

        Definition parse_name_soundT
          := forall str pf name,
               @parse_name str pf name = true
               -> parse_of_item _ G str (NonTerminal _ name).

        (*Definition parse_name_completeT P
          := forall valid str pf prod prods (H_sub : P valid (prod::prods)),
               minimal_parse_of _ G initial_names_data is_valid_name remove_name valid str (prod::prods)
               -> @parse_name str pf prod prods = true.*)

        Definition split_correctT
                   (str1 : String)
                   (split : String * String)
          := fst split ++ snd split =s str1.

        Definition split_list_correctT str1 (split_list : list (String * String))
          := List.Forall (@split_correctT str1) split_list.

        (*Definition split_list_completeT
                   valid1 valid2
                   (str : String) (pf : str ≤s str0)
                   (split_list : list (String * String))
                   (prod : production CharType)
          := match prod return Type with
               | nil => True
               | it::its => ({ s1s2 : String * String
                                      & (fst s1s2 ++ snd s1s2 =s str)
                                        * (minimal_parse_of_item _ G initial_names_data is_valid_name remove_name valid1 (fst s1s2) it)
                                        * (minimal_parse_of_production _ G initial_names_data is_valid_name remove_name valid2 (snd s1s2) its) }%type)
                            -> ({ s1s2 : String * String
                                         & (In s1s2 split_list)
                                           * (minimal_parse_of_item _ G initial_names_data is_valid_name remove_name valid1 (fst s1s2) it)
                                           * (minimal_parse_of_production _ G initial_names_data is_valid_name remove_name valid2 (snd s1s2) its) }%type)
             end.*)

        Lemma parse_production_sound
                 (parse_name_sound : parse_name_soundT)
                 (str : String) (pf : str ≤s str0)
                 (prod : production CharType)
        : parse_production split_string_for_production split_string_for_production_correct parse_name pf prod = true
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

        (*Lemma parse_production_complete
              valid Pv
              (Hv_init_rem : forall p, Pv (remove_name initial_names_data p) p)
              (Hv_rem : forall p, Pv (remove_name valid p) p)
              (parse_name_complete : parse_name_completeT Pv)
              (split_string_for_production_complete : forall valid1 valid2 str pf prod, @split_list_completeT valid1 valid2 str pf (split_string_for_production str prod) prod)
              (str : String) (pf : str ≤s str0)
              (prod : production CharType)
        : minimal_parse_of_production _ G initial_names_data is_valid_name remove_name valid str prod
          -> parse_production G split_string_for_production split_string_for_production_correct parse_name pf prod = true.
        Proof.
          change (forall str0 prod, split_list_correctT str0 (split_string_for_production str0 prod)) in split_string_for_production_correct.
          revert valid Hv_rem str pf; induction prod;
          repeat match goal with
                   | _ => intro
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => solve [ auto ]
                   | [ H : fold_right orb false (map _ _) = true |- _ ] => apply fold_right_orb_map_sig1 in H
                   | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
                   | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                   | [ H : minimal_parse_of_production _ _ _ _ _ _ _ nil |- _ ] => inversion_clear H
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
                   | [ H : minimal_parse_of_production _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : H_subT initial_names_data -> _ |- _ ]
                     => specialize (H (reflexivity _))
                   | [ H : ?s ≤s _ |- context[split_string_for_production_correct ?s ?p] ]
                     => specialize (fun a b p0 v1 p1 v2 p2
                                    => @split_string_for_production_complete v1 v2 s H p (existT _ (a, b) (p0, p1, p2)))
                   | [ H : forall a b, is_true (a ++ b =s _ ++ _) -> _ |- _ ]
                     => specialize (H _ _ (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : ?a -> ?b, H' : ?a |- _ ] => specialize (H H')
                   | [ H : forall v : names_listT, @?a v -> @?b v |- _ ]
                     => pose proof (H valid); pose proof (H initial_names_data); clear H
                   | [ |- fold_right orb false (map _ _) = true ] => apply fold_right_orb_map_sig2
                 end;
          match goal with
            | [ H : In (?s1, ?s2) (split_string_for_production ?str ?prod)
                |- { x : { s1s2 : _ | (fst s1s2 ++ snd s1s2 =s ?str) = true } | _ } ]
              => let H' := fresh in
                 pose proof (proj1 (@Forall_forall _ _ _) (@split_string_for_production_correct str prod) _ H) as H';
                   unfold split_correctT in H';
                   refine (exist _ (exist _ (s1, s2) _) _);
                   simpl in *
          end;
          repeat match goal with
                   | _ => split
                   | [ |- (_ && _)%bool = true ] => apply Bool.andb_true_iff
                   | _ => eapply parse_item_complete; [..| eassumption ];
                          try unfold H_subT; simpl;
                          try eassumption; try reflexivity;
                          hnf in parse_name_complete |- *;
                          solve [ apply parse_name_complete
                                | intro; apply parse_name_complete
                                | intros ??; apply parse_name_complete; eauto ]
                   | [ |- In _ (combine_sig _) ] => apply In_combine_sig
                   | [ IHprod : _ |- _ ] => eapply IHprod; eassumption
                 end.
          Grab Existential Variables.
          assumption.
          assumption.
          assumption.
          assumption.
        Qed.*)
      End production.

      Section production_ext.
        Lemma parse_production_ext
              (str0 : String)
              (parse_name1 parse_name2 : forall (str : String),
                                           str ≤s str0
                                           -> string
                                           -> bool)
              (str : String) (pf : str ≤s str0) (prod : production CharType)
              (ext : forall str' pf' name', parse_name1 str' pf' name'
                                            = parse_name2 str' pf' name')
        : parse_production split_string_for_production split_string_for_production_correct parse_name1 pf prod
          = parse_production split_string_for_production split_string_for_production_correct parse_name2 pf prod.
        Proof.
          revert str pf.
          induction prod as [|? ? IHprod]; simpl; intros; try reflexivity; [].
          f_equal.
          apply map_ext; intros.
          apply f_equal2; [ apply parse_item_ext | apply IHprod ].
          intros; apply ext.
        Qed.
      End production_ext.

      Section names.
        Section step.
          Variable str0 : String.
          Variable parse_name : forall (str : String)
                                       (pf : str ≤s str0),
                                  string -> bool.

          Local Ltac parse_name_step_t :=
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
                     | [ H : minimal_parse_of _ _ _ _ _ _ _ nil |- _ ] => solve [ inversion H ]
                     | [ H : minimal_parse_of _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                     | [ H : parse_production _ _ _ _ _ = true |- _ ] => apply parse_production_sound in H; try eassumption; []
                     | _ => solve [ eauto ]
                   end.


          (** To parse as a given name, we must parse as one of the [production]s that is associated to that name. *)
          Lemma parse_name_step_sound
                (parse_name_sound : parse_name_soundT parse_name)
                (str : String) (pf : str ≤s str0) (name : string)
          : parse_name_step G split_string_for_production split_string_for_production_correct parse_name pf name = true
            -> parse_of_item _ G str (NonTerminal _ name).
          Proof.
            unfold parse_name_step.
            intro H'; constructor; revert H'.
            generalize (Lookup G name); clear name.
            intros [|prod prods]; simpl; auto; [].
            revert prod.
            induction prods; simpl; auto; intros.
            { parse_name_step_t. }
            { parse_name_step_t.
              apply ParseTail.
              apply IHprods; clear IHprods.
              parse_name_step_t. }
          Defined.

          (*Lemma parse_name_step_complete
                valid Pv
                (Hv_init_rem : forall p, Pv (remove_name initial_names_data p) p)
                (Hv_rem : forall p, Pv (remove_name valid p) p)
                (parse_name_complete : parse_name_completeT parse_name Pv)
                (split_string_for_production_complete : forall valid1 valid2 str pf prod, @split_list_completeT str0 valid1 valid2 str pf (split_string_for_production str prod) prod)
                (str : String) (pf : str ≤s str0) (prod : production CharType) (prods : names CharType)
          : minimal_parse_of _ G initial_names_data is_valid_name remove_name valid str (prod::prods)
            -> parse_name_step G split_string_for_production split_string_for_production_correct parse_name pf (prod::prods) = true.
          Proof.
            unfold parse_name_step.
            revert prod.
            induction prods; simpl; auto.
            { parse_name_step_t.
              left; eapply parse_production_complete with (Pv := Pv); [..| eassumption ];
              solve [ eassumption | trivial ]. }
            { parse_name_step_t;
              match goal with
                | [ H : forall prod, minimal_parse_of _ _ _ _ _ _ ?s (prod::_) -> _,
                      H' : minimal_parse_of_production _ _ _ _ _ _ ?s ?prod |- _ ]
                  => specialize (H prod (MinParseHead _ H'))
                | [ H : forall prod, minimal_parse_of _ _ _ _ _ _ ?s (prod::?prods) -> _,
                      H' : minimal_parse_of _ _ _ _ _ _ ?s ?prods |- _ ]
                  => specialize (fun prod => H prod (MinParseTail _ H'))
              end;
              parse_name_step_t;
              solve [ right; parse_name_step_t]. }
          Qed.*)
        End step.

        Section step_extensional.
          Lemma parse_name_step_ext (str0 : String)
                (parse_name1 parse_name2 : forall (str : String)
                                                  (pf : str ≤s str0),
                                             string -> bool)
                (str : String) (pf : str ≤s str0) (name : string)
                (ext : forall str' pf' name', parse_name1 str' pf' name'
                                              = parse_name2 str' pf' name')
          : parse_name_step G split_string_for_production split_string_for_production_correct parse_name1 pf name
            = parse_name_step G split_string_for_production split_string_for_production_correct parse_name2 pf name.
          Proof.
            unfold parse_name_step.
            f_equal.
            apply map_ext; intros.
            apply parse_production_ext; auto.
          Qed.
        End step_extensional.

        (** TODO: move this elsewhere *)
        Lemma or_to_sumbool (s1 s2 : String) (f : String -> nat)
              (H : f s1 < f s2 \/ s1 = s2)
        : {f s1 < f s2} + {s1 = s2}.
        Proof.
          case_eq (s1 =s s2).
          { intro H'; right; apply bool_eq_correct in H'; exact H'. }
          { intro H'; left; destruct H; trivial.
            apply bool_eq_correct in H.
            generalize dependent (s1 =s s2)%string_like; intros; subst.
            discriminate. }
        Qed.

        (** TODO: move this elsewhere *)
        Lemma if_ext {T} (b : bool) (f1 f2 : b = true -> T true) (g1 g2 : b = false -> T false)
              (ext_f : forall H, f1 H = f2 H)
              (ext_g : forall H, g1 H = g2 H)
        : (if b as b' return (b = b' -> T b') then f1 else g1) eq_refl
          = (if b as b' return (b = b' -> T b') then f2 else g2) eq_refl.
        Proof.
          destruct b; auto.
        Defined.

        Section wf.
          Lemma parse_name_or_abort_sound
                (p : String * names_listT) (str : String)
                (pf : str ≤s fst p)
                (name : string)
          : parse_name_or_abort G initial_names_data is_valid_name remove_name
                                remove_name_dec ntl_wf split_string_for_production
                                split_string_for_production_correct
                                p pf name
            = true
            -> parse_of_item _ G str (NonTerminal _ name).
          Proof.
            unfold parse_name_or_abort.
            revert str pf name.
            let Acca := match goal with |- context[@Fix3 _ _ _ _ _ ?Rwf _ _ ?a _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str pf name.
            rewrite Fix3_eq.
            { match goal with
                | [ |- context[match lt_dec ?a ?b with _ => _ end] ] => destruct (lt_dec a b) as [Hlt|Hlt]
              end.
              { apply parse_name_step_sound; try assumption; simpl.
                hnf.
                intros str0 pf0 name0 H'; eapply IHr;
                try first [ exact H' | eassumption ].
                left; assumption. }
              { match goal with
                  | [ |- context[match Sumbool.sumbool_of_bool ?b with _ => _ end] ] => destruct (Sumbool.sumbool_of_bool b)
                end;
                [ | solve [ auto ] ].
                intros.
                hnf in pf.
                apply or_to_sumbool in pf.
                destruct pf as [ pf | pf ]; [ exfalso; hnf in *; solve [ auto ] | subst ].
                eapply parse_name_step_sound; try eassumption.
                hnf.
                intros str0 pf0 name0 H'; eapply IHr;
                try first [ exact H' | eassumption ].
                right; split; trivial; simpl.
                apply remove_name_dec; assumption. } }
            { repeat match goal with
                       | _ => intro
                       | _ => reflexivity
                       | [ |- context[match ?E with _ => _ end] ] => destruct E
                       | [ H : _ |- _ ] => rewrite H; reflexivity
                       | _ => apply parse_name_step_ext; auto
                       | _ => apply (@if_ext (fun _ => bool)); intros
                     end. }
          Defined.

          (*Lemma parse_name_or_abort_helper_complete
                Pv
                (p : String * names_listT) (str : String)
                (Hv_init_rem : forall p', Pv (remove_name initial_names_data p') p')
                (Hv_rem : forall p', Pv (remove_name (snd p) p') p')
                (Hv_expand
                 : forall str p' valid,
                     Pv valid p'
                     -> minimal_parse_of
                          String G initial_names_data
                          is_valid_name remove_name valid str
                          p'
                     -> minimal_parse_of
                          String G initial_names_data
                          is_valid_name remove_name initial_names_data str
                          p')
                (Hv_valid_init : forall ls p', Pv ls p' -> Pv initial_names_data p')
                (split_string_for_production_complete : forall valid0 valid1 str0 pf prod, @split_list_completeT str valid0 valid1 str0 pf (split_string_for_production str0 prod) prod)
                (pf : str ≤s fst p)
                (prod : production CharType)
                (prods : names CharType)
                (H_prods : Pv (snd p) (prod::prods))
                (H_init : Pv initial_names_data (prod::prods))
                (*(H_prods : is_valid_name (snd p) (prod::prods) = true)*)
          : minimal_parse_of _ G initial_names_data is_valid_name remove_name (snd p) str (prod::prods)
            -> parse_name_or_abort_helper G initial_names_data is_valid_name remove_name
                                              remove_name_dec ntl_wf split_string_for_production
                                              split_string_for_production_correct
                                              p pf prod prods
               = true.
          Proof.
            unfold parse_name_or_abort_helper.
            revert str split_string_for_production_complete pf prod prods H_prods H_init.
            let Acca := match goal with |- context[@Fix4 _ _ _ _ _ _ ?Rwf _ _ ?a _ _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str split_string_for_production_complete pf prod prods H_prods H_init.
            rewrite Fix4_eq;
              [
              | repeat match goal with
                       | _ => intro
                       | _ => reflexivity
                       | [ |- context[match ?E with _ => _ end] ] => destruct E
                       | [ H : _ |- _ ] => rewrite H; reflexivity
                       | _ => apply parse_name_step_ext; auto
                       | _ => apply (@if_ext (fun _ => bool)); intros
                     end ];
              [].
            { match goal with
                | [ |- context[if lt_dec ?a ?b then _ else _] ] => destruct (lt_dec a b)
              end.
              { (eapply parse_name_step_complete;
                 try solve [ eassumption | instantiate; intros; eauto ]);
                try solve [ eassumption | instantiate; intros; eauto ]; hnf; [].
                intros valid str0 pf0 prod0 prods0 H'; simpl.
                intro mp.
                eapply IHr;
                try solve [ exact H'
                          | eassumption
                          | reflexivity
                          | simpl in *; trivial
                          | eapply Hv_expand; eassumption
                          | eapply Hv_valid_init; eassumption ].
                { left; assumption. }
                { intros; apply split_string_for_production_complete.
                  etransitivity; eassumption. } }
              { let ivp := match goal with |- context[is_valid_name ?x ?y] => constr:(is_valid_name x y) end in
                set (ivp' := ivp);
                  assert (ivp = ivp') by reflexivity;
                  clearbody ivp';
                  destruct ivp'.
                { intros.
                  hnf in pf.
                  apply or_to_sumbool in pf.
                  destruct pf as [ pf | pf ]; [ exfalso; hnf in *; solve [ auto ] | subst ].
                  eapply parse_name_step_complete;
                    try solve [ eassumption | instantiate; intros; eauto ]; hnf; [].
                  intros valid str0 pf0 prod0 prods0 H'; simpl.
                  intro mp.
                  eapply IHr;
                    try solve [ exact H'
                              | eassumption
                              | simpl; trivial
                              | intros; eapply Hv_rem; eassumption
                              | intros; eapply Hv_init_rem; eassumption ];
                    admit. (*
                  Focus 4.
                  simpl in *.

                  eapply H

                  eapply expand_minimal_parse_of in mp;
                    [
                    | solve [ eassumption | apply Hv_valid_init; assumption ].. ].

                  eapply IHr.
                    try solve [ exact H' | eassumption | simpl; trivial ].
                  { right; split; trivial; simpl.
                    apply remove_name_dec; assumption. }
                  { simpl. eauto. }
                  { intros; apply split_string_for_production_complete.
                    etransitivity; eassumption. }
                  { simpl. hnf in Hv_valid_init; eapply Hv_valid_init; eassumption. } }
                  { simpl.

                  (** XXX Need to rework the assumptions / induction
                          to ensure that we can get this parse tree.
                          What to do? *)
                    admit. }*) }
                { (** INTERESTING CASE HERE - need to show that if not
                      [is_valid_name], then we can't have a
                      parse tree. *)
                  Print minimal_parse_of.
                  exfalso; clear; admit. } } }
            { repeat match goal with
                       | _ => intro
                       | _ => reflexivity
                       | [ |- context[match ?E with _ => _ end] ] => destruct E
                       | [ H : _ |- _ ] => rewrite H; reflexivity
                       | _ => apply parse_name_step_ext; auto
                       | _ => apply (@if_ext (fun _ => bool)); intros
                     end. }
          Defined.*)

          Lemma parse_name_sound
                (str : String) (name : string)
          : parse_name _ G initial_names_data is_valid_name remove_name
                       remove_name_dec ntl_wf split_string_for_production
                       split_string_for_production_correct
                       str name
            = true
            -> parse_of_item _ G str (NonTerminal _ name).
          Proof.
            unfold parse_name, parse_name_or_abort.
            apply parse_name_or_abort_sound.
          Defined.

          (*Lemma parse_name_complete
                valid
                (str : String)
                (split_string_for_production_complete : forall valid0 valid1 str0 pf prod, @split_list_completeT str valid0 valid1 str0 pf (split_string_for_production str0 prod) prod)
                (prods : names CharType)
          : minimal_parse_of _ G initial_names_data is_valid_name remove_name valid str prods
            -> parse_name _ G initial_names_data is_valid_name remove_name
                                 remove_name_dec ntl_wf split_string_for_production
                                 split_string_for_production_correct
                                 str prods
               = true.
          Proof.
            unfold parse_name, parse_name_or_abort.
            destruct prods; [ solve [ intro H'; inversion H' ] | ].
            apply parse_name_or_abort_helper_complete; try assumption.
          Defined.*)
        End wf.
      End names.
    End parts.
  End general.
End sound.

Section brute_force_spliter.
  Lemma make_all_single_splits_complete_helper
  : forall (str : string_stringlike)
           (s1s2 : string_stringlike * string_stringlike),
      fst s1s2 ++ snd s1s2 =s str -> In s1s2 (make_all_single_splits str).
  Proof.
    intros str [s1 s2] H.
    apply bool_eq_correct in H; subst.
    revert s2.
    induction s1; simpl in *.
    { intros.
      destruct s2; left; reflexivity. }
    { intros; right.
      refine (@in_map _ _ _ _ (s1, s2) _).
      auto. }
  Qed.

  (*Lemma make_all_single_splits_complete
  : forall G names_listT initial_names_data is_valid_name remove_name str0 valid0 valid1 str pf prod, @split_list_completeT _ string_stringlike G names_listT initial_names_data is_valid_name remove_name str0 valid0 valid1 str pf (@make_all_single_splits str) prod.
  Proof.
    intros; hnf.
    destruct prod; trivial.
    intros [ s1s2 [ [ p1 p2 ] p3 ] ].
    exists s1s2.
    abstract (
        repeat split; try assumption;
        apply make_all_single_splits_complete_helper;
        assumption
      ).
  Defined.*)
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

  (*Definition brute_force_make_parse_of_complete
             valid
             (str : @String Ascii.ascii string_stringlike)
             (name : string)
  : minimal_parse_of _ G (Valid_nonterminals G) rdp_list_is_valid_name (rdp_list_remove_name Ascii.ascii_dec) valid str name
    -> brute_force_make_parse_of G str name = true.
  Proof.
    unfold brute_force_make_parse_of; simpl; intro.
    eapply parse_name_complete; try eassumption.
    apply make_all_single_splits_complete.
  Defined.*)
End brute_force_make_parse_of.
