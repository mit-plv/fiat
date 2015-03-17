(** * Reflective lemmas for proving a splitter complete *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.BaseTypes Parsers.BooleanBaseTypes.
Require Import Parsers.Splitters.RDPList.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Common.Wf.
Require Import Common.

Set Implicit Arguments.

(** TODO: Generalize to more dependent splitters *)
Section helpers.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Context (split_valid_prod : forall (split_valid : string -> bool),
                                production CharType -> bool).
  Context (split_valid_prod_ext : forall (split_valid split_valid' : string -> bool)
                                         (H : forall s, split_valid s = split_valid' s)
                                         p,
                                    split_valid_prod split_valid p = split_valid_prod split_valid' p).

  Local Instance : parser_computational_predataT := @rdp_list_predata _ G.

  Definition split_valid_step
             (nt_valid : nonterminals_listT)
             (split_valid : forall nt_valid', nonterminals_listT_R nt_valid' nt_valid -> string -> bool)
             (nt : string)
  : bool.
  Proof.
    refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal nt_valid nt)
            then
              let split_valid' := split_valid (remove_nonterminal nt_valid nt) (remove_nonterminal_dec _ _ _)
              in fold_right
                   andb
                   true
                   (map (split_valid_prod split_valid') (Lookup G nt))
            else
              is_valid_nonterminal initial_nonterminals_data nt);
    try assumption.
  Defined.

  Lemma split_valid_step_ext (valid : nonterminals_listT)
        f g
        (H : forall (valid' : nonterminals_listT)
                    (pf : nonterminals_listT_R valid' valid)
                    nt,
               f valid' pf nt = g valid' pf nt)
        nt
  : split_valid_step f nt = split_valid_step g nt.
  Proof.
    unfold split_valid_step.
    edestruct dec;
      f_equal.
    apply map_ext; intro x.
    apply split_valid_prod_ext; trivial.
  Qed.

  Definition split_valid : bool
    := fold_right
         andb
         true
         (map
            (Fix1 _ ntl_wf _ split_valid_step (Valid_nonterminals G))
            (Valid_nonterminals G)).

  Context {premethods : @parser_computational_dataT' _ _ (@rdp_list_data' _ String G)}.
  Context split_stateT0 split_string_for_production0 split_string_for_production_correct0
          (dummy : @boolean_parser_dataT _ String
           := {| predata := @rdp_list_predata _ G;
                 split_stateT := split_stateT0;
                 split_string_for_production := split_string_for_production0;
                 split_string_for_production_correct := split_string_for_production_correct0 |}).
  Local Instance data0 : @boolean_parser_dataT _ String
    := {| predata := @rdp_list_predata _ G;
          split_stateT := split_stateT0;
          split_string_for_production := split_string_for_production0;
          split_string_for_production_correct := split_string_for_production_correct0 |}.

  Context (split_valid_prod_tail : forall f x xs, split_valid_prod f (x::xs) = true -> split_valid_prod f xs = true).
Print split_list_completeT.
  Lemma split_complete
        (H : split_valid = true)
        str0 valid str pf nt
        (H' : is_valid_nonterminal initial_nonterminals_data nt = true)
        (split_prod_each : forall it its,
                             split_valid_prod
                               (Fix1 _ ntl_wf _ split_valid_step (remove_nonterminal (Valid_nonterminals G) nt))
                               (it::its) = true
                             -> split_list_completeT
                                  (G := G) (str0 := str0) (valid := valid) str pf
                                  (split_string_for_production0 it its str) it its)
  : ForallT
      (Forall_tails
         (fun prod =>
            match prod with
              | [] => True
              | it :: its =>
                @split_list_completeT _ String G data0 str0 valid str pf
                                      (@split_string_for_production0 it its str) it its
            end)) (Lookup G nt).
  Proof.
    pose proof H' as H''.
    simpl in H''.
    unfold rdp_list_is_valid_nonterminal in H''.
    edestruct in_dec as [H'''|H''']; try discriminate; [].
    apply (fun H => fold_right_andb_map_in H _ H''') in H.
    simpl in H.
    rewrite Fix1_eq in H by apply split_valid_step_ext.
    unfold split_valid_step in H at 1.
    rewrite H' in H.
    edestruct dec; try (simpl in *; congruence).
    clear -H split_valid_prod_tail split_prod_each.
    { induction (Lookup G nt); simpl in *; trivial.
      intros; split;
      repeat match goal with
               | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | _ => solve [ eauto ]
             end.
      clear IHp.
      clear -H split_valid_prod_tail split_prod_each.
      let a := match goal with a : production _ |- _ => constr:a end in
      induction a; simpl in *; trivial.
      { intros; split;
        repeat match goal with
                 | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : context[match ?a with _ => _ end] |- _ ] => atomic a; destruct a
                 | _ => solve [ eauto ]
                 | _ => progress simpl in *
                 | _ => congruence
               end. } }
  Qed.

  Lemma split_complete_simple
        (split_prod_each
         : forall nt it its str0 valid s1 s2 (pf : s1 ++ s2 ≤s str0) st,
             MinimalParse.minimal_parse_of_item
               String G initial_nonterminals_data
               is_valid_nonterminal remove_nonterminal str0 valid
               s1 it
             -> MinimalParse.minimal_parse_of_production
                  String G
                  initial_nonterminals_data is_valid_nonterminal remove_nonterminal
                  str0 valid s2 its
             -> is_valid_nonterminal initial_nonterminals_data nt = true
             -> split_valid_prod
                  (Fix1 _ ntl_wf _ split_valid_step (remove_nonterminal (Valid_nonterminals G) nt))
                  (it::its) = true
             -> { st1st2 : _
                | In
                    ({| string_val := s1; state_val := fst st1st2 |},
                     {| string_val := s2; state_val := snd st1st2 |})
                    (split_string_for_production0 it its {| string_val := s1 ++ s2; state_val := st |}) })
        (H : split_valid = true)
  : forall str0 valid str pf nt,
      is_valid_nonterminal initial_nonterminals_data nt = true ->
      ForallT
        (Forall_tails
           (fun prod =>
              match prod with
                | [] => True
                | it :: its =>
                  @split_list_completeT _ String G data0 str0 valid str pf
                                        (@split_string_for_production0 it its str) it its
              end)) (Lookup G nt).
  Proof.
    intros str0 valid str pf nt H0.
    apply split_complete; try assumption.
    intros it its Hvalid [ [s1 s2] [ [ H' m1 ] m2 ] ].
    destruct str as [str st].
    simpl in *.
    apply bool_eq_correct in H'.
    subst.
    specialize (split_prod_each
                  nt it its str0 valid s1 s2 pf st m1 m2 H0 Hvalid).
    eexists; repeat split.
    exact (proj2_sig split_prod_each).
    assumption.
    assumption.
  Qed.
End helpers.
