(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.
Require Import Common Common.ilist Common.Wf.
Require Import Eqdep_dec.

Local Open Scope string_like_scope.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (productions_listT : Type)
          (initial_productions_data : productions_listT)
          (is_valid_productions : productions_listT -> productions CharType -> bool)
          (remove_productions : productions_listT -> productions CharType -> productions_listT)
          (productions_listT_R : productions_listT -> productions_listT -> Prop)
          (remove_productions_dec : forall ls prods, is_valid_productions ls prods = true
                                                     -> productions_listT_R (remove_productions ls prods) ls)
          (ntl_wf : well_founded productions_listT_R).

  Inductive minimal_parse_of
  : productions_listT -> String -> productions CharType -> Type :=
  | MinParseHead : forall valid str pat pats,
                     minimal_parse_of_production valid str pat
                     -> minimal_parse_of valid str (pat::pats)
  | MinParseTail : forall valid str pat pats,
                     minimal_parse_of valid str pats
                     -> minimal_parse_of valid str (pat::pats)
  with minimal_parse_of_production
  : productions_listT -> String -> production CharType -> Type :=
  | MinParseProductionNil : forall valid,
                              minimal_parse_of_production valid (Empty _) nil
  | MinParseProductionCons : forall valid str pat strs pats,
                               minimal_parse_of_item valid str pat
                               -> minimal_parse_of_production valid strs pats
                               -> minimal_parse_of_production valid (str ++ strs) (pat::pats)
  with minimal_parse_of_item
  : productions_listT -> String -> item CharType -> Type :=
  | MinParseTerminal : forall valid x,
                         minimal_parse_of_item valid [[ x ]]%string_like (Terminal x)
  | MinParseNonTerminal
    : forall valid name str,
        is_valid_productions valid (Lookup G name) = true
        -> minimal_parse_of (remove_productions valid (Lookup G name)) str (Lookup G name)
        -> minimal_parse_of_item valid str (NonTerminal CharType name).

  Fixpoint parse_of__of__minimal_parse_of {valid str pats} (p : minimal_parse_of valid str pats)
  : parse_of String G str pats
    := match p with
         | MinParseHead valid str pat pats p'
           => ParseHead pats (parse_of_production__of__minimal_parse_of_production p')
         | MinParseTail valid str pat pats p'
           => ParseTail pat (parse_of__of__minimal_parse_of p')
       end
  with parse_of_production__of__minimal_parse_of_production {valid str pat} (p : minimal_parse_of_production valid str pat)
       := match p with
            | MinParseProductionNil valid
              => ParseProductionNil _ _
            | MinParseProductionCons valid str pat strs pats p' p''
              => ParseProductionCons
                   (parse_of_item__of__minimal_parse_of_item p')
                   (parse_of_production__of__minimal_parse_of_production p'')
          end
  with parse_of_item__of__minimal_parse_of_item {valid str it} (p : minimal_parse_of_item valid str it)
       := match p with
            | MinParseTerminal valid x
              => ParseTerminal String G x
            | MinParseNonTerminal valid name str H p'
              => ParseNonTerminal name (parse_of__of__minimal_parse_of p')
          end.

  Section minimize.
    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.
      Local Hint Constructors minimal_parse_of_item minimal_parse_of minimal_parse_of_production.

      Section item.
        Context (str : String).
        Context (minimal_parse_of__of__parse_of : forall valid name str,
        is_valid_productions valid (Lookup G name) = true
        -> minimal_parse_of (remove_productions valid (Lookup G name)) str (Lookup G name)
        -> minimal_parse_of_item valid str (NonTerminal CharType name).


        (** We require that the list of productions be non-empty; we
            do this by passing the first element separately, rather
            than invoking dependent types and proofs. *)
        Context (str : String)
                (str_matches_productions : production CharType -> productions CharType -> bool).

        Definition parse_item (it : item CharType) : bool
          := match it with
               | Terminal ch => [[ ch ]] =s str
               | NonTerminal name => match Lookup G name with
                                       | nil => (** No string can match an empty nonterminal *) false
                                       | p::ps => str_matches_productions p ps
                                     end
             end.
      End item.

      Section item.


        Context (str : String)
                (str_matches_productions : production CharType -> productions CharType -> bool).


  | MinParseTerminal : forall valid x,
                         minimal_parse_of_item valid [[ x ]]%string_like (Terminal x)
  | MinParseNonTerminal
    : forall valid name str,
        is_valid_productions valid (Lookup G name) = true
        -> minimal_parse_of (remove_productions valid (Lookup G name)) str (Lookup G name)
        -> minimal_parse_of_item valid str (NonTerminal CharType name).

        Definition str_matches_productions_soundT
          := forall prod prods, str_matches_productions prod prods = true
                                -> parse_of _ G str (prod::prods).

        Definition str_matches_productions_completeT
          := forall prod prods, parse_of _ G str (prod::prods)
                                -> str_matches_productions prod prods = true.

        Lemma parse_item_sound
              (str_matches_productions_sound : str_matches_productions_soundT)
              (it : item CharType)
        : parse_item String G str str_matches_productions it = true -> parse_of_item _ G str it.
        Proof.
          unfold parse_item, str_matches_productions_soundT in *.
          repeat match goal with
                   | _ => intro
                   | [ H : context[match ?E with _ => _ end] |- _ ] => atomic E; destruct E
                   | [ |- context[match ?E with _ => _ end] ] => atomic E; destruct E
                   | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                   | [ |- parse_of_item _ _ _ (NonTerminal _ _) ] => constructor
                   | [ H : context[match ?E with _ => _ end] |- context[?E] ] => destruct E
                   | _ => progress subst
                   | _ => solve [ eauto ]
                 end.
        Defined.

        Lemma parse_item_complete
              (str_matches_productions_complete : str_matches_productions_completeT)
              (it : item CharType)
        : parse_of_item _ G str it -> parse_item String G str str_matches_productions it = true.
        Proof.
          unfold parse_item, str_matches_productions_completeT in *.
          repeat match goal with
                   | _ => intro
                   | _ => reflexivity
                   | [ H : parse_of_item _ _ ?s ?i |- _ ] => atomic s; atomic i; destruct H
                   | [ |- _ = true ] => apply bool_eq_correct
                   | [ H : context[?E] |- context[match ?E with _ => _ end] ] => destruct E
                   | [ H : parse_of _ _ _ [] |- _ ] => solve [ inversion H ]
                   | _ => solve [ eauto ]
               end.
        Qed.
      End item.

      Section item_ext.
        Lemma parse_item_ext
              (str : String)
              (str_matches_productions1 str_matches_productions2 : production CharType -> productions CharType -> bool)
              (it : item CharType)
              (ext : forall x y, str_matches_productions1 x y = str_matches_productions2 x y)
        : parse_item String G str str_matches_productions1 it
          = parse_item String G str str_matches_productions2 it.
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
                (parse_productions : forall (str : String),
                                       str ≤s str0
                                       -> production CharType
                                       -> productions CharType
                                       -> bool).

        Definition parse_productions_soundT
          := forall str pf prod prods,
               @parse_productions str pf prod prods = true
               -> parse_of _ G str (prod::prods).

        Definition parse_productions_completeT
          := forall str pf prod prods,
               parse_of _ G str (prod::prods)
               -> @parse_productions str pf prod prods = true.

        Definition split_correctT
                   (str1 : String)
                   (split : String * String)
          := fst split ++ snd split =s str1.

        Definition split_list_correctT str1 (split_list : list (String * String))
          := List.Forall (@split_correctT str1) split_list.

        Definition split_list_completeT
                   (str : String) (pf : str ≤s str0)
                   (split_list : list (String * String))
                   (prod : production CharType)
          := match prod return Type with
               | nil => True
               | it::its => ({ s1s2 : String * String
                                      & (fst s1s2 ++ snd s1s2 =s str)
                                        * (parse_of_item _ G (fst s1s2) it)
                                        * (parse_of_production _ G (snd s1s2) its) }%type)
                            -> ({ s1s2 : String * String
                                         & (In s1s2 split_list)
                                           * (parse_of_item _ G (fst s1s2) it)
                                           * (parse_of_production _ G (snd s1s2) its) }%type)
             end.

        Lemma parse_production_sound
                 (parse_productions_sound : parse_productions_soundT)
                 (str : String) (pf : str ≤s str0)
                 (prod : production CharType)
        : parse_production G split_string_for_production split_string_for_production_correct parse_productions pf prod = true
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
                    hnf in parse_productions_sound |- *;
                    apply parse_productions_sound ]. }
        Defined.

        Lemma parse_production_complete
                 (parse_productions_complete : parse_productions_completeT)
                 (split_string_for_production_complete : forall str pf prod, @split_list_completeT str pf (split_string_for_production str prod) prod)
                 (str : String) (pf : str ≤s str0)
                 (prod : production CharType)
        : parse_of_production _ G str prod
          -> parse_production G split_string_for_production split_string_for_production_correct parse_productions pf prod = true.
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
                   | [ H : parse_of_production _ _ _ nil |- _ ] => inversion_clear H
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
                   | [ H : parse_of_production _ _ _ (_::_) |- _ ] => inversion H; clear H; subst
                   | [ H : ?s ≤s _ |- context[split_string_for_production_correct ?s ?p] ]
                     => specialize (fun a b p0 p1 p2
                                    => @split_string_for_production_complete s H p (existT _ (a, b) (p0, p1, p2)))
                   | [ H : forall a b, is_true (a ++ b =s _ ++ _) -> _ |- _ ]
                     => specialize (H _ _ (proj2 (@bool_eq_correct _ _ _ _) eq_refl))
                   | [ H : ?a -> ?b, H' : ?a |- _ ] => specialize (H H')
                   | [ |- fold_right orb false (map _ _) = true ] => apply fold_right_orb_map_sig2
                 end.
          match goal with
            | [ H : In (?s1, ?s2) (split_string_for_production ?str ?prod)
                |- { x : { s1s2 : _ | (fst s1s2 ++ snd s1s2 =s ?str) = true } | _ } ]
              => let H' := fresh in
                 pose proof (proj1 (@Forall_forall _ _ _) (@split_string_for_production_correct str prod) _ H) as H';
                   unfold split_correctT in H';
                   refine (exist _ (exist _ (s1, s2) _) _);
                   simpl in *
          end.
          repeat match goal with
                   | _ => split
                   | [ |- (_ && _)%bool = true ] => apply Bool.andb_true_iff
                   | _ => eapply parse_item_complete; try eassumption;
                          hnf in parse_productions_complete |- *;
                          solve [ apply parse_productions_complete ]
                   | _ => eapply IHprod; eassumption
                 end.
          apply In_combine_sig.
          Grab Existential Variables.
          assumption.
        Qed.
      End production.

      Section production_ext.
        Lemma parse_production_ext
              (str0 : String)
              (parse_productions1 parse_productions2 : forall (str : String),
                                                         str ≤s str0
                                                         -> production CharType
                                                         -> productions CharType
                                                         -> bool)
              (str : String) (pf : str ≤s str0) (prod : production CharType)
              (ext : forall str' pf' prod' prods', parse_productions1 str' pf' prod' prods'
                                                   = parse_productions2 str' pf' prod' prods')
        : parse_production G split_string_for_production split_string_for_production_correct parse_productions1 pf prod
          = parse_production G split_string_for_production split_string_for_production_correct parse_productions2 pf prod.
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
        Section step.
          Variable str0 : String.
          Variable parse_productions : forall (str : String)
                                              (pf : str ≤s str0),
                                         production CharType -> productions CharType -> bool.

          Local Ltac parse_productions_step_t :=
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
                     | [ H : parse_production _ _ _ _ _ _ = true |- _ ] => apply parse_production_sound in H; try eassumption; []
                     | _ => solve [ eauto ]
                   end.


          (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
          Lemma parse_productions_step_sound
                (parse_productions_sound : parse_productions_soundT parse_productions)
                (str : String) (pf : str ≤s str0) (prod : production CharType) (prods : productions CharType)
          : parse_productions_step G split_string_for_production split_string_for_production_correct parse_productions pf (prod::prods) = true
            -> parse_of _ G str (prod::prods).
          Proof.
            unfold parse_productions_step.
            revert prod.
            induction prods; simpl; auto; intros.
            { parse_productions_step_t. }
            { parse_productions_step_t.
              apply ParseTail.
              apply IHprods; clear IHprods.
              parse_productions_step_t. }
          Defined.

          Lemma parse_productions_step_complete
                (parse_productions_complete : parse_productions_completeT parse_productions)
                (split_string_for_production_complete : forall str pf prod, @split_list_completeT str0 str pf (split_string_for_production str prod) prod)
                (str : String) (pf : str ≤s str0) (prod : production CharType) (prods : productions CharType)
          : parse_of _ G str (prod::prods)
            -> parse_productions_step G split_string_for_production split_string_for_production_correct parse_productions pf (prod::prods) = true.
          Proof.
            unfold parse_productions_step.
            revert prod.
            induction prods; simpl; auto.
            { parse_productions_step_t.
              left; apply parse_production_complete; assumption. }
            { parse_productions_step_t.
              match goal with
                | [ H : forall prod, parse_of _ _ ?s (prod::_) -> _,
                      H' : parse_of_production _ _ ?s ?prod |- _ ]
                  => specialize (H prod (ParseHead _ H'))
              end.
              parse_productions_step_t.
              right.
              parse_productions_step_t. }
          Qed.
        End step.

        Section step_extensional.
          Lemma parse_productions_step_ext (str0 : String)
                (parse_productions1 parse_productions2 : forall (str : String)
                                                                (pf : str ≤s str0),
                                                           production CharType -> productions CharType -> bool)
                (str : String) (pf : str ≤s str0) (prods : productions CharType)
                (ext : forall str' pf' prod' prods', parse_productions1 str' pf' prod' prods'
                                                     = parse_productions2 str' pf' prod' prods')
          : parse_productions_step G split_string_for_production split_string_for_production_correct parse_productions1 pf prods
            = parse_productions_step G split_string_for_production split_string_for_production_correct parse_productions2 pf prods.
          Proof.
            unfold parse_productions_step.
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
          Lemma parse_productions_or_abort_helper_sound
                (p : String * productions_listT) (str : String)
                (pf : str ≤s fst p)
                (prod : production CharType)
                (prods : productions CharType)
          : parse_productions_or_abort_helper G initial_productions_data is_valid_productions remove_productions
                                              remove_productions_dec ntl_wf split_string_for_production
                                              split_string_for_production_correct
                                              p pf prod prods
            = true
            -> parse_of _ G str (prod::prods).
          Proof.
            unfold parse_productions_or_abort_helper.
            revert str pf prod prods.
            let Acca := match goal with |- context[@Fix4 _ _ _ _ _ _ ?Rwf _ _ ?a _ _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str pf prod prods.
            rewrite Fix4_eq.
            { match goal with
                | [ |- context[match lt_dec ?a ?b with _ => _ end] ] => destruct (lt_dec a b) as [Hlt|Hlt]
              end.
              { apply parse_productions_step_sound; try assumption; simpl.
                hnf.
                intros str0 pf0 prod0 prods0 H'; eapply IHr;
                try first [ exact H' | eassumption ].
                left; assumption. }
              { let ivp := match goal with |- context[is_valid_productions ?x ?y] => constr:(is_valid_productions x y) end in
                set (ivp' := ivp);
                  assert (ivp = ivp') by reflexivity;
                  clearbody ivp';
                  destruct ivp'; [ | solve [ auto ] ].
                intros.
                hnf in pf.
                apply or_to_sumbool in pf.
                destruct pf as [ pf | pf ]; [ exfalso; hnf in *; solve [ auto ] | subst ].
                eapply parse_productions_step_sound; try eassumption.
                hnf.
                intros str0 pf0 prod0 prods0 H'; eapply IHr;
                try first [ exact H' | eassumption ].
                right; split; trivial; simpl.
                apply remove_productions_dec; assumption. } }
            { repeat match goal with
                       | _ => intro
                       | _ => reflexivity
                       | [ |- context[match ?E with _ => _ end] ] => destruct E
                       | [ H : _ |- _ ] => rewrite H; reflexivity
                       | _ => apply parse_productions_step_ext; auto
                       | _ => apply (@if_ext (fun _ => bool)); intros
                     end. }
          Defined.

          Lemma parse_productions_or_abort_helper_complete
                (p : String * productions_listT) (str : String)
                (split_string_for_production_complete : forall str0 pf prod, @split_list_completeT str str0 pf (split_string_for_production str0 prod) prod)
                (pf : str ≤s fst p)
                (prod : production CharType)
                (prods : productions CharType)
          : parse_of _ G str (prod::prods)
            -> parse_productions_or_abort_helper G initial_productions_data is_valid_productions remove_productions
                                              remove_productions_dec ntl_wf split_string_for_production
                                              split_string_for_production_correct
                                              p pf prod prods
               = true.
          Proof.
            unfold parse_productions_or_abort_helper.
            revert str split_string_for_production_complete pf prod prods.
            let Acca := match goal with |- context[@Fix4 _ _ _ _ _ _ ?Rwf _ _ ?a _ _ _ _] => constr:(Rwf a) end in
            induction (Acca) as [? ? IHr];
              intros str split_string_for_production_complete pf prod prods.
            rewrite Fix4_eq.
            { match goal with
                | [ |- context[if lt_dec ?a ?b then _ else _] ] => destruct (lt_dec a b)
              end.
              { apply parse_productions_step_complete; try assumption.
                hnf.
                intros str0 pf0 prod0 prods0 H'; eapply IHr;
                try first [ exact H' | eassumption ].
                { left; assumption. }
                { intros; apply split_string_for_production_complete.
                  etransitivity; eassumption. } }
              { let ivp := match goal with |- context[is_valid_productions ?x ?y] => constr:(is_valid_productions x y) end in
                set (ivp' := ivp);
                  assert (ivp = ivp') by reflexivity;
                  clearbody ivp';
                  destruct ivp'.
                { intros.
                  hnf in pf.
                  apply or_to_sumbool in pf.
                  destruct pf as [ pf | pf ]; [ exfalso; hnf in *; solve [ auto ] | subst ].
                  eapply parse_productions_step_complete; try eassumption.
                  hnf.
                  intros str0 pf0 prod0 prods0 H'; eapply IHr;
                  try first [ exact H' | eassumption ].
                  { right; split; trivial; simpl.
                    apply remove_productions_dec; assumption. }
                  { intros; apply split_string_for_production_complete.
                    etransitivity; eassumption. } }
                { (** INTERESTING CASE HERE - need to show that if not
                      [is_valid_productions], then we can't have a
                      parse tree. *)
                  exfalso; clear; admit. } } }
            { repeat match goal with
                       | _ => intro
                       | _ => reflexivity
                       | [ |- context[match ?E with _ => _ end] ] => destruct E
                       | [ H : _ |- _ ] => rewrite H; reflexivity
                       | _ => apply parse_productions_step_ext; auto
                       | _ => apply (@if_ext (fun _ => bool)); intros
                     end. }
          Defined.

          Lemma parse_productions_sound
                (str : String) (prods : productions CharType)
          : parse_productions _ G initial_productions_data is_valid_productions remove_productions
                              remove_productions_dec ntl_wf split_string_for_production
                              split_string_for_production_correct
                              str prods
            = true
            -> parse_of _ G str prods.
          Proof.
            unfold parse_productions, parse_productions_or_abort.
            destruct prods; [ solve [ auto ] | ].
            apply parse_productions_or_abort_helper_sound.
          Defined.

          Lemma parse_productions_complete
                (str : String)
                (split_string_for_production_complete : forall str0 pf prod, @split_list_completeT str str0 pf (split_string_for_production str0 prod) prod)
                (prods : productions CharType)
          : parse_of _ G str prods
            -> parse_productions _ G initial_productions_data is_valid_productions remove_productions
                                 remove_productions_dec ntl_wf split_string_for_production
                                 split_string_for_production_correct
                                 str prods
               = true.
          Proof.
            unfold parse_productions, parse_productions_or_abort.
            destruct prods; [ solve [ intro H'; inversion H' ] | ].
            apply parse_productions_or_abort_helper_complete; try assumption.
          Defined.
        End wf.
      End productions.
    End parts.
  End general.
End sound.


  Section i


    (** A parse of a string into [productions] is a [production] in
        that list, together with a list of substrings which cover the
        original string, each of which is a parse of the relevant
        component of the [production]. *)
    Inductive parse_of : String -> productions -> Type :=
    | ParseHead : forall str pat pats, parse_of_production str pat
                                       -> parse_of str (pat::pats)
    | ParseTail : forall str pat pats, parse_of str pats
                                       -> parse_of str (pat::pats)
    with parse_of_production : String -> production -> Type :=
    | ParseProductionNil : parse_of_production (Empty _) nil
    | ParseProductionCons : forall str pat strs pats,
                           parse_of_item str pat
                           -> parse_of_production strs pats
                           -> parse_of_production (str ++ strs) (pat::pats)
    with parse_of_item : String -> item -> Type :=
    | ParseTerminal : forall x, parse_of_item [[ x ]]%string_like (Terminal x)
    | ParseNonTerminal : forall name str, parse_of str (Lookup G name)
                                          -> parse_of_item str (NonTerminal name).

    Definition ParseProductionSingleton str it (p : parse_of_item str it) : parse_of_production str [ it ].
    Proof.
      rewrite <- (RightId _ str).
      constructor; assumption || constructor.
    Defined.

    Definition ParseProductionApp str1 str2 p1 p2 (pop1 : parse_of_production str1 p1) (pop2 : parse_of_production str2 p2)
    : parse_of_production (str1 ++ str2) (p1 ++ p2)%list.
    Proof.
      induction pop1; simpl.
      { rewrite LeftId; assumption. }
      { rewrite Associativity.
        constructor; assumption. }
    Defined.

    Definition ParseApp str1 str2 p1 p2 (po1 : parse_of str1 [ p1 ]) (po2 : parse_of str2 [ p2 ])
    : parse_of (str1 ++ str2) [ (p1 ++ p2)%list ].
    Proof.
      inversion_clear po1; inversion_clear po2;
      try match goal with
            | [ H : parse_of _ [] |- _ ] => exfalso; revert H; clear; intro H; abstract inversion H
          end.
      { constructor. apply ParseProductionApp; assumption. }
    Defined.
  End parse.

  Definition parse_of_grammar (String : string_like CharType) (str : String) (G : grammar) :=
    parse_of String G str G.


  Section definitions.
    (** An [item] is the basic building block of a context-free
        grammar; it is either a terminal ([CharType]-literal) or a
        nonterminal of a given name. *)
    Inductive item :=
    | Terminal (_ : CharType)
    | NonTerminal (name : string).

    (** A [productions] is a list of possible [production]s; a
        [production] is a list of [item]s.  A string matches a
        [production] if it can be broken up into components that match
        the relevant element of the [production]. *)
    Definition production := list item.
    Definition productions := list production.

    Definition productions_dec (CharType_eq_dec : forall x y : CharType, {x = y} + {x <> y})
               (x y : productions) : {x = y} + {x <> y}.
    Proof.
      repeat (apply list_eq_dec; intros);
      decide equality.
      apply string_dec.
    Defined.

    (** A [grammar] consists of [productions] to match a string
        against, and a function mapping names to [productions]. *)
    (** TODO(jgross): also include list of valid starting non-terminals, for convenience and notation *)
    (** TODO(jgross): look up notations for specifying these nicely *)
    Record grammar :=
      {
        Start_symbol :> string;
        Lookup :> string -> productions;
        Start_production :> productions := Lookup Start_symbol;
        Valid_nonterminal_symbols : list string;
        Valid_nonterminals : list productions := map Lookup Valid_nonterminal_symbols
      }.
  End definitions.

End cfg.

Arguments parse_of _%type_scope _ _ _%string_like _.
Arguments parse_of_item _%type_scope _ _ _%string_like _.
Arguments parse_of_production _%type_scope _ _ _%string_like _.
Arguments parse_of_grammar _%type_scope _ _%string_like _.
Section sound.
