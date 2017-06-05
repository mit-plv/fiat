(** * Definition of an optimized CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListMorphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.GenericCorrectnessBaseTypes.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Common Fiat.Common.Wf Fiat.Common.Wf2 Fiat.Common.Telescope.Core.
Require Import Fiat.Parsers.GenericRecognizerExt.
Require Import Fiat.Parsers.GenericRecognizer.
Require Import Fiat.Parsers.GenericRecognizerCorrect.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Parsers.ContextFreeGrammar.ReflectiveLemmas.
Require Import Fiat.Parsers.RecognizerPreOptimized.
Require Import Fiat.Common.Match.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Export Fiat.Common.SetoidInstances.
Require Export Fiat.Common.List.ListMorphisms.
Require Export Fiat.Common.OptionFacts.
Require Export Fiat.Common.BoolFacts.
Require Export Fiat.Common.NatFacts.
Require Export Fiat.Common.Sigma.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.GenericRecognizerOptimizedTactics.
Import NPeano.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Global Arguments string_dec : simpl never.
Global Arguments string_beq : simpl never.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
          {G : pregrammar Char}.

  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Char _ _}.

  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.
  Let optdata : boolean_parser_dataT :=
    {| split_data := optsplitdata |}.
  Local Existing Instance data.

  Let rdata' : @parser_removal_dataT' _ G predata := rdp_list_rdata'.
  Local Existing Instance rdata'.

  Context {gendata : generic_parser_dataT Char}
          {gencdata : generic_parser_correctness_dataT}.

  Local Arguments minus !_ !_.
  Local Arguments min !_ !_.

  Let is_correct pnt str nt
    := forall b,
      parse_nt_is_correct str (of_nonterminal nt) b pnt
      <-> parse_nt_is_correct str (of_nonterminal nt) b (parse_nonterminal (data := data) str nt).

  Local Arguments Compare_dec.leb !_ !_.
  Local Arguments to_nonterminal / _ _ _.

  Local Instance good_nth_proper {A}
  : Proper (eq ==> _ ==> _ ==> eq) (nth (A:=A))
    := _.
  Local Instance good_nth'_proper {A}
  : Proper (eq ==> _ ==> _ ==> eq) (nth' (A:=A))
    := _.

  Lemma parse_nonterminal_optdata_eq
        {HSLP : StringLikeProperties Char}
        {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}
        (str : String)
        (nt : String.string)
    : is_correct (parse_nonterminal (data := optdata) str nt) str nt.
  Proof.
    pose optsplitdata_correct.
    unfold is_correct.
    pose proof (GenericRecognizerMin.parse_nonterminal_correct str nt).
    pose proof (GenericRecognizerMin.parse_nonterminal_correct (cdata := optsplitdata_correct) str nt).
    do 2 edestruct @GenericRecognizerMin.parse_nonterminal; simpl in *;
      intros []; split; intro;
        try solve [ tauto
                  | exfalso; eauto using @parse_nt_is_correct_disjoint ].
  Qed.

  Let Let_In' {A B} (x : A) (f : forall y : A, B y) : B x
    := let y := x in f y.

  Local Notation "@ 'Let_In' A B" := (@Let_In' A B) (at level 10, A at level 8, B at level 8, format "@ 'Let_In'  A  B").
  Local Notation Let_In := (@Let_In' _ _).

  Let Let_In_Proper {A B} x
  : Proper (forall_relation (fun _ => eq) ==> eq) (@Let_In A B x).
  Proof.
    lazy; intros ?? H; apply H.
  Defined.

  Definition inner_nth' {A} := Eval unfold nth' in @nth' A.
  Definition inner_nth'_nth' : @inner_nth' = @nth'
    := eq_refl.

  Local Instance good_inner_nth'_proper {A}
  : Proper (eq ==> _ ==> _ ==> eq) (inner_nth' (A:=A))
    := _.


  Lemma rdp_list_to_production_opt_sig x
  : { f : _ | rdp_list_to_production (G := G) x = f }.
  Proof.
    eexists.
    set_evars.
    unfold rdp_list_to_production at 1.
    cbv beta iota delta [Carriers.default_to_production productions production].
    simpl @Lookup.
    match goal with
      | [ |- (let a := ?av in
              let b := @?bv a in
              let c := @?cv a b in
              let d := @?dv a b c in
              let e := @?ev a b c d in
              @?v a b c d e) = ?R ]
        => change (Let_In av (fun a =>
                   Let_In (bv a) (fun b =>
                   Let_In (cv a b) (fun c =>
                   Let_In (dv a b c) (fun d =>
                   Let_In (ev a b c d) (fun e =>
                   v a b c d e))))) = R);
          cbv beta
    end.
    lazymatch goal with
      | [ |- Let_In ?x ?P = ?R ]
        => subst R; refine (@Let_In_Proper _ _ x _ _ _); intro; set_evars
    end.
    unfold Lookup_idx.
    symmetry; rewrite_map_nth_rhs; symmetry.
    repeat match goal with
             | [ |- context G[@Let_In ?A ?B ?k ?f] ]
               => first [ let h := head k in constr_eq h @nil
                        | constr_eq k 0
                        | constr_eq k (snd (snd x)) ];
                 test pose f; (* make sure f is closed *)
                 let c := constr:(@Let_In A B k) in
                 let c' := (eval unfold Let_In' in c) in
                 let G' := context G[c' f] in
                 change G'; simpl
           end.
    rewrite drop_all by (simpl; omega).
    unfold productions, production.
    rewrite <- nth'_nth at 1.
    rewrite map_map; simpl.
    match goal with
      | [ H := ?e |- _ ] => is_evar e; subst H
    end.
    match goal with
      | [ |- nth' ?a ?ls ?d = ?e ?a ]
        => refine (_ : inner_nth' a ls d = (fun a' => inner_nth' a' _ d) a); cbv beta;
           apply f_equal2; [ clear a | reflexivity ]
    end.
    etransitivity.
    { apply (_ : Proper (pointwise_relation _ _ ==> eq ==> eq) (@List.map _ _));
      [ intro | reflexivity ].
      do 2 match goal with
             | [ |- Let_In ?x ?P = ?R ]
               => refine (@Let_In_Proper _ _ x _ _ _); intro
           end.
      etransitivity.
      { symmetry; rewrite_map_nth_rhs; symmetry.
        unfold Let_In' at 2 3 4; simpl.
        set_evars.
        rewrite drop_all by (simpl; omega).
        unfold Let_In'.
        rewrite <- nth'_nth.
        change @nth' with @inner_nth'.
        subst_body; reflexivity. }
      reflexivity. }
    reflexivity.
  Defined.

  Definition rdp_list_to_production_opt x
    := Eval cbv beta iota delta [proj1_sig rdp_list_to_production_opt_sig Let_In']
      in proj1_sig (rdp_list_to_production_opt_sig x).

  Lemma rdp_list_to_production_opt_correct x
  : rdp_list_to_production (G := G) x = rdp_list_to_production_opt x.
  Proof.
    exact (proj2_sig (rdp_list_to_production_opt_sig x)).
  Qed.

  Definition parse_nonterminal_opt'0
             (str : String)
             (nt : String.string)
  : { b : _ | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    exists (parse_nonterminal (data := optdata) str nt).
    reflexivity.
  Defined.

  Local Unset Keyed Unification.
  Definition parse_nonterminal_opt'1
             (str : String)
             (nt : String.string)
  : { b : _ | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'0 str nt) in
    let h := head c in
    let p := (eval cbv beta iota zeta delta [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].
    cbv beta iota zeta delta [parse_nonterminal GenericRecognizer.parse_nonterminal parse_nonterminal' GenericRecognizer.parse_nonterminal' parse_nonterminal_or_abort GenericRecognizer.parse_nonterminal_or_abort list_to_grammar].
    simpl @GenericBaseTypes.parse_nt_T.
    change (@GenericRecognizer.parse_nonterminal_step Char) with (fun b c d e f g h i j k l m => @GenericRecognizer.parse_nonterminal_step Char b c d e f g h i j k l m); cbv beta.
    evar (b' : parse_nt_T).
    sigL_transitivity b'; subst b';
    [
    | rewrite Fix5_2_5_eq by (intros; rapply (@parse_nonterminal_step_ext _ _ _ optdata _); assumption);
      reflexivity ].
    simpl @fst; simpl @snd.
    cbv beta iota zeta delta [parse_nonterminal_step parse_productions parse_productions' parse_production parse_item parse_item' GenericRecognizer.parse_nonterminal_step GenericRecognizer.parse_productions GenericRecognizer.parse_productions' GenericRecognizer.parse_production GenericRecognizer.parse_item GenericRecognizer.parse_item' Lookup list_to_grammar list_to_productions].
    simpl.
    cbv beta iota zeta delta [predata BaseTypes.predata initial_nonterminals_data nonterminals_length remove_nonterminal production_carrierT].
    cbv beta iota zeta delta [rdp_list_predata Carriers.default_production_carrierT rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data rdp_list_remove_nonterminal Carriers.default_nonterminal_carrierT rdp_list_nonterminals_listT rdp_list_production_tl Carriers.default_nonterminal_carrierT].
    (*cbv beta iota zeta delta [rdp_list_of_nonterminal].*)
    simpl; unfold pregrammar_nonterminals; simpl.
    evar (b' : parse_nt_T).
    sigL_transitivity b'; subst b';
    [
    | simpl;
      rewrite !map_length, !length_up_to;
      reflexivity ].

    refine_Fix2_5_Proper_eq_with_assumptions.
    etransitivity_rev _.
    { fix2_trans_with_assumptions;
      [
      | unfold parse_production', parse_production'_for, parse_item', GenericRecognizer.parse_production', GenericRecognizer.parse_production'_for, GenericRecognizer.parse_item', productions, production;
        solve [ t_reduce_fix;
                t_reduce_list;
                t_reduce_fix ] ].

      (** Now we take advantage of the optimized splitter *)
      etransitivity_rev _.
      { eapply option_rect_Proper_nondep_eq; [ intros ? Hv | reflexivity ].
        apply (f_equal (fun x => match x with Some _ => true | None => false end)) in Hv.
        simpl in Hv.
        lazymatch goal with
        | [ H : _ /\ (_ \/ is_true (is_valid_nonterminal initial_nonterminals_data ?nt)) |- _ ]
          => assert (Hvalid' : is_valid_nonterminal initial_nonterminals_data nt)
        end.
        { destruct_head and; destruct_head or; try assumption; [].
          edestruct lt_dec; simpl in *; [ omega | ].
          edestruct dec; simpl in *; [ | congruence ].
          match goal with
          | [ H : _ = true |- _ ] => apply Bool.andb_true_iff in H; destruct H as [? H']
          end.
          match goal with
          | [ H : sub_nonterminals_listT ?ls ?init, H' : list_bin_eq ?nt ?ls = true
              |- is_true (?R ?init ?nt) ]
            => apply H, H'
          end. }
        let nt := match type of Hvalid' with is_true (is_valid_nonterminal _ ?nt) => nt end in
        assert (Hvalid'' : productions_rvalid G (map to_production (nonterminal_to_production nt))).
        { unfold grammar_rvalid in Hvalid.
          eapply (proj1 fold_right_andb_map_in_iff) in Hvalid; [ eassumption | ].
          rewrite nonterminal_to_production_correct' by assumption.
          apply in_map, initial_nonterminals_correct'; assumption. }
        simpl @nonterminal_to_production in Hvalid''.
        unfold productions_rvalid in Hvalid''.
        rewrite map_map in Hvalid''.
        pose proof (proj1 fold_right_andb_map_in_iff Hvalid'') as Hvalid'''.
        cbv beta in Hvalid'''.

        misc_opt.
        step_opt'.
        step_opt'.
        step_opt'.
        step_opt'.
        apply map_Proper_eq_In; intros ? Hin.
        apply in_rev in Hin.
        specialize (Hvalid''' _ Hin).
        unfold parse_production', parse_production'_for, GenericRecognizer.parse_production', GenericRecognizer.parse_production'_for.
        simpl.
        (** Switch to using the list hypothesis, rather than lookup with the index *)
        etransitivity_rev _.
        { t_reduce_list_evar_with_hyp;
          [
          |
          | ].
          { step_opt'.
            reflexivity. }
          { rewrite rdp_list_production_tl_correct.
            match goal with
              | [ H : _ = ?x |- context[?x] ]
                => rewrite <- H; reflexivity
            end. }
          { match goal with
              | [ H : _ = ?x |- context[match ?x with _ => _ end] ]
                => rewrite <- H
            end.
            reflexivity. } }
        (** Pull out the nil case once and for all *)
        etransitivity_rev _.
        { lazymatch goal with
            | [ |- _ = list_rect ?P ?N ?C (?f ?a) ?a ?b ?c ]
              => let P0 := fresh in
                 let N0 := fresh in
                 let C0 := fresh in
                 set (P0 := P);
                   set (N0 := N);
                   set (C0 := C);
                   let IH := fresh "IH" in
                   let xs := fresh "xs" in
                   refine (list_rect
                             (fun ls' => forall a' (pf : ls' = f a') b' c',
                                           (bool_rect
                                              (fun _ => _)
                                              (N0 a' b' c')
                                              (list_rect P0 (fun _ _ _ => ret_production_nil_true) C0 ls' a' b' c')
                                              (EqNat.beq_nat (List.length ls') 0))
                                           = list_rect P0 N0 C0 ls' a' b' c')
                             _
                             _
                             (f a) a eq_refl b c);
                     simpl @list_rect;
                     [ subst P0 N0 C0; intros; cbv beta
                     | intros ? xs IH; intros; unfold C0 at 1 3; cbv beta;
                       match goal with
                         | [ |- context[list_rect P0 N0 C0 ?ls'' ?a''] ]
                           => specialize (IH a'')
                       end;
                       let T := match type of IH with ?T -> _ => T end in
                       let H_helper := fresh in
                       assert (H_helper : T);
                         [
                         | specialize (IH H_helper);
                           setoid_rewrite <- IH; clear IH ] ]
          end.
          { reflexivity. }
          { rewrite rdp_list_production_tl_correct.
            match goal with
              | [ H : _ = ?x |- context[?x] ]
                => rewrite <- H; reflexivity
            end. }
          { simpl.
            match goal with
            | [ |- context[EqNat.beq_nat (List.length ?ls) 0] ]
              => is_var ls; destruct ls; simpl; try reflexivity
            end; [].
            repeat match goal with
                   | [ |- ?x = ?x ] => reflexivity
                   | [ H := fun _ _ => _ |- _ ] => subst H; cbv beta
                   | [ |- context[?x - (?y + (?x - ?y)) ] ]
                     => replace (x - (y + (x - y))) with 0 by (clear; omega)
                   | _ => rewrite minusr_minus
                   | _ => progress simpl
                   end. } }
        simpl.
        step_opt'; [ | reflexivity ].
        etransitivity_rev _.
        { move Hvalid''' at bottom.
          simpl @to_production in Hvalid'''.
          unfold production_rvalid in Hvalid'''.
          t_prereduce_list_evar.
          t_postreduce_list_with_hyp_with_assumption;
            [ reflexivity
            | let lem := constr:(production_tl_correct) in
              simpl rewrite lem;
              match goal with
              | [ H : _::_ = ?y |- context[tl ?y] ] => generalize dependent y; intros; subst
              end;
              simpl in *;
              try reflexivity;
              try assumption..
            | ].
          { match goal with
            | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
            end.
            split_and; assumption. }
          match goal with
          | [ |- context[match ?nt with Terminal _ => _ | _ => _ end] ]
            => assert (Hvalid'''' : item_rvalid G nt)
          end.
          { repeat match goal with
                   | _ => assumption
                   | [ H : ?nt :: _ = ?ls, H' : context[?ls] |- is_true (item_rvalid _ ?nt) ]
                     => rewrite <- H in H'
                   | _ => progress simpl in *
                   | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
                   | _ => progress split_and
                   end. }
          etransitivity_rev _.
          { do 4 step_opt'; [].
            etransitivity_rev _.
            { step_opt'; [ reflexivity | ].
              repeat optsplit_t'.
              { reflexivity. }
              { reflexivity. } }
            unfold list_caset, item_rect.
            repeat optsplit_t'.
            { apply (f_equal2 ret_production_cons); [ | reflexivity ].
              repeat misc_opt'.
              rewrite Min.min_idempotent.
              reflexivity. }
            { apply (f_equal2 ret_production_cons).
              { apply (f_equal3 (fun (b : bool) x y => if b then x else y)); [ | reflexivity | reflexivity ].
                apply (f_equal2 andb); [ | reflexivity ].
                match goal with
                | [ |- _ = EqNat.beq_nat (min ?v ?x) ?v ]
                  => refine (_ : Compare_dec.leb v x = _)
                end.
                match goal with
                | [ |- Compare_dec.leb 1 ?x = _ ]
                  => destruct x as [|[|]]; try reflexivity
                end. }
              { rewrite !Nat.add_1_r.
                reflexivity. } }
            { simpl in *.
              match goal with
              | [ H : is_true ?x |- context[?x] ] => rewrite H
              end.
              reflexivity. } }
          etransitivity_rev _.
          { unfold parse_item', GenericRecognizer.parse_item'.
            simpl.
            repeat optsplit_t'; repeat step_opt';
              [ apply (f_equal2 ret_production_cons) | ];
              repeat optsplit_t'; try misc_opt; repeat step_opt'.
          { reflexivity. }
          { set_evars.
            match goal with
            | [ H : is_true ?x |- context[?x] ] => rewrite H
            end.
            match goal with
            | [ H := ?e |- _ ] => is_evar e; subst H
            end.
            reflexivity. }
          { rewrite !minusr_minus, <- max_def, <- !minusr_minus.
            reflexivity. }
          { reflexivity. } }
        reflexivity. }
      reflexivity. }

      progress unfold productions, production, rproductions, rproduction.
      progress cbv beta iota zeta delta [rdp_list_predata Carriers.default_production_carrierT rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data rdp_list_remove_nonterminal Carriers.default_nonterminal_carrierT rdp_list_nonterminals_listT rdp_list_production_tl Carriers.default_nonterminal_carrierT].

      step_opt'; [ | reflexivity ].
      step_opt'.
      step_opt'.
      etransitivity_rev _.
      { cbv beta iota delta [rdp_list_nonterminal_to_production Carriers.default_production_carrierT Carriers.default_nonterminal_carrierT].
        simpl rewrite list_to_productions_to_nonterminal; unfold Lookup_idx.
        etransitivity_rev _.
        { step_opt'; [ reflexivity | ].
          step_opt'.
          etransitivity_rev _.
          { step_opt'.
            rewrite_map_nth_rhs; simpl; rewrite !map_map; simpl.
            unfold interp_rproductions, interp_rproduction.
            apply (f_equal2 (@nth _ _)); [ | reflexivity ].
            step_opt'; [].
            rewrite map_length.
            reflexivity. }
          rewrite_map_nth_dep_rhs; simpl.
          rewrite map_length.
          unfold rproductions, rproduction.
          reflexivity. }
        rewrite_map_nth_rhs; rewrite !map_map; simpl.
        apply (f_equal2 (@nth _ _)); [ | reflexivity ].
        step_opt'; [ | reflexivity ].
        rewrite !map_map; simpl.
        reflexivity. }
      rewrite_map_nth_rhs; rewrite !map_map; simpl.
      rewrite <- nth'_nth.
      etransitivity_rev _.
      { step_opt'.
        step_opt'; [ | reflexivity ].
        reflexivity. }
      reflexivity. }
    etransitivity_rev _.
    { etransitivity_rev _.
      { repeat first [ rewrite uneta_bool
                     | idtac;
                       match goal with
                       | [ |- context[@rdp_list_of_nonterminal] ] => fail 1
                       | [ |- context[@Carriers.default_of_nonterminal] ] => fail 1
                       | [ |- context[@Carriers.default_production_tl] ] => fail 1
                       | _ => reflexivity
                       end
                     | step_opt'
                     | t_reduce_list_evar
                     | apply (f_equal2 andb)
                     | apply (f_equal2 ret_production_cons)
                     | apply (f_equal2 (@cons _))
                     | t_refine_item_match ];
        first [ progress unfold rdp_list_of_nonterminal, Carriers.default_of_nonterminal, Valid_nonterminals, grammar_of_pregrammar, pregrammar_nonterminals; simpl;
                rewrite !map_length;
                reflexivity
              | idtac;
                match goal with
                  | [ |- _ = ?f ?A ?b ?c ]
                    => refine (f_equal (fun A' => f A' b c) _)
                end;
                progress unfold Carriers.default_production_tl; simpl;
                repeat step_opt'; [ reflexivity | ];
                unfold Lookup_idx;
                unfold productions, production;
                rewrite_map_nth_rhs; simpl;
                rewrite <- nth'_nth;
                rewrite_map_nth_dep_rhs; simpl;
                step_opt'; simpl;
                rewrite !nth'_nth; simpl;
                rewrite map_length;
                rewrite <- !nth'_nth;
                change @nth' with @inner_nth';
                reflexivity
              | idtac ].
        reflexivity. }
      etransitivity_rev _.
      { set_evars.
        repeat first [ idtac;
                       match goal with
                         | [ |- context[@rdp_list_to_production] ] => fail 1
                         | _ => reflexivity
                       end
                     | rewrite rdp_list_to_production_opt_correct
                     | step_opt'
                     | t_reduce_list_evar ].
        subst_evars.
        reflexivity. }
      etransitivity_rev _.
      { step_opt'; [ | reflexivity ].
        step_opt'.
        step_opt'.
        step_opt'.
        step_opt'; [ | reflexivity ].
        unfold rdp_list_to_production_opt at 1; simpl.
        change @inner_nth' with @nth' at 3.
        etransitivity_rev _.
        { step_opt'.
          etransitivity_rev _.
          { repeat step_opt'; [ | reflexivity ].
            rewrite nth'_nth.
            rewrite_map_nth_rhs; rewrite !map_map; simpl.
            rewrite <- nth'_nth.
            change @nth' with @inner_nth'.
            apply (f_equal2 (inner_nth' _)); [ | reflexivity ].
            step_opt'; [].
            rewrite map_id.
            change @inner_nth' with @nth' at 3.
            rewrite nth'_nth.
            unfold interp_rproductions, interp_rproduction, rproductions, rproduction, production.
            rewrite !map_length.
            progress repeat match goal with
                            | [ |- context[List.nth (?minus (@List.length ?B (@List.map ?A ?B ?f ?ls)) _)] ]
                              => rewrite (@map_length A B f ls)
                            end.
            rewrite_map_nth_rhs; simpl.
            rewrite !map_map; simpl.
            unfold productions, production.
            rewrite <- nth'_nth.
            change @nth' with @inner_nth'.
            apply f_equal2; [ | reflexivity ].
            reflexivity. }
          etransitivity_rev _.
          { change @inner_nth' with @nth' at 1.
            rewrite nth'_nth.
            rewrite_map_nth_rhs; rewrite !map_map; simpl.
            rewrite <- nth'_nth.
            change @nth' with @inner_nth' at 1.
            reflexivity. }
          etransitivity_rev _.
          { apply f_equal2; [ reflexivity | ].
            lazymatch goal with
            | [ |- _ = bool_rect ?P (if ?b then ?t else ?f) ?t ?b' ]
              => transitivity (if (orb (negb b') b) then t else f); [ | destruct b, b'; reflexivity ]
            end; fin_step_opt.
            match goal with
            | [ |- context[negb (EqNat.beq_nat ?x 0)] ]
              => replace (negb (EqNat.beq_nat x 0)) with (Compare_dec.leb 1 x)
                by (destruct x as [|[]]; reflexivity)
            end.
            reflexivity. }
          etransitivity_rev _.
          { apply (f_equal2 (inner_nth' _)); [ | reflexivity ].
            step_opt'; [ ].
            change @inner_nth' with @nth' at 1.
            rewrite nth'_nth.
            rewrite_map_nth_rhs; rewrite !map_map; simpl.
            rewrite <- nth'_nth.
            change @nth' with @inner_nth' at 1.
            reflexivity. }
          etransitivity_rev _.
          { apply (f_equal2 (inner_nth' _)); [ | reflexivity ].
            step_opt'.
            apply (f_equal2 (inner_nth' _)); [ reflexivity | ].
            lazymatch goal with
            | [ |- _ = bool_rect ?P (if ?b then ?t else ?f) ?t ?b' ]
              => transitivity (if (orb (negb b') b) then t else f); [ | destruct b, b'; reflexivity ]
            end; fin_step_opt.
            match goal with
            | [ |- context[negb (EqNat.beq_nat ?x 0)] ]
              => replace (negb (EqNat.beq_nat x 0)) with (Compare_dec.leb 1 x)
                by (destruct x as [|[]]; reflexivity)
            end.
            reflexivity. }
          reflexivity. }
        reflexivity. }
      reflexivity. }
    etransitivity_rev _.
    { repeat first [ step_opt'
                   | apply (f_equal2 (inner_nth' _)); fin_step_opt
                   | apply (f_equal2 orb); fin_step_opt
                   | idtac;
                     match goal with
                     | [ |- _ = List.length (rdp_list_to_production_opt _) ]
                       => progress unfold rdp_list_to_production_opt at 1; simpl;
                          change @inner_nth' with @nth';
                          repeat match goal with
                                 | _ => progress simpl
                                 | _ => progress fin_step_opt
                                 | _ => rewrite !map_length
                                 | _ => rewrite !map_map
                                 | _ => progress unfold interp_rproductions, interp_rproduction, rproductions, rproduction
                                 | [ |- _ = nth' ?n ?ls ?d ]
                                   => refine (f_equal2 (nth' n) _ _)
                                 | [ |- _ = List.map _ (pregrammar_rproductions G) ]
                                   => step_opt'
                                 | [ |- _ = List.map (fun x : list (ritem _) => _) _ ]
                                   => step_opt'
                                 | _
                                   => progress (rewrite nth'_nth;
                                                progress rewrite_map_nth_rhs; rewrite !map_map; simpl;
                                                rewrite <- nth'_nth)
                                 | [ |- _ = List.length ?x ] => is_var x; reflexivity
                                 end;
                          fin_step_opt
                     end ];
      [ | reflexivity | reflexivity | ].
      { rewrite list_rect_map.
        t_reduce_list_evar; [ reflexivity | ].
        set_evars.
        setoid_rewrite list_caset_map.
        unfold predata in *. (* work around bug #4673, https://coq.inria.fr/bugs/show_bug.cgi?id=4673 *)
        setoid_rewrite item_rect_ritem_rect; cbv beta.
        try setoid_rewrite uneta_bool.
        subst_evars.

        step_opt'; [].
        step_opt'.
        { etransitivity_rev _.
          { set_evars.
            do 2 setoid_rewrite combine_map_r.
            do 3 setoid_rewrite map_map; simpl.
            setoid_rewrite map_length.
            progress change (fun x : ?A * ?B => fst x) with (@fst A B).
            subst_evars.

            reflexivity. }

          refine (f_equal2 ret_production_cons _ _); [ | reflexivity ].
          apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _ ==> _) (ritem_rect (fun _ => parse_item_T))); repeat intro;
            [ | reflexivity | reflexivity ].
          change_char_at_matches.
          reflexivity. }
        { set_evars.
          do 2 setoid_rewrite combine_map_r.
          subst_evars.

          step_opt'.
          { set_evars.
            change_char_at_matches.
            do 3 setoid_rewrite map_map; simpl.
            setoid_rewrite map_length.
            subst_evars.

            reflexivity. }
          { step_opt'; [ | reflexivity ].
            set_evars.
            do 3 setoid_rewrite map_map; simpl.
            setoid_rewrite map_length.
            progress change (fun x : ?A * ?B => fst x) with (@fst A B).
            subst_evars.

            reflexivity. } } }
      { reflexivity. } }

    simpl.
    progress change (fun x : list ?T => @List.length ?T x) with (@List.length T).
    progress change @inner_nth' with @nth'.

    (** change [nth'] back to [nth] *)
    etransitivity_rev _.
    { step_opt'; [ | reflexivity ].
      step_opt'.
      step_opt'.
      apply (f_equal2 (nth' _)); fin_step_opt; [].
      repeat lazymatch goal with
             | [ |- _ = nth' _ _ _ ]
               => rewrite nth'_nth; apply (f_equal2 (nth _))
             | [ |- _ = orb _ _ ] => apply f_equal2
             | [ |- _ = ret_production_cons _ _ ] => apply f_equal2
             | [ |- _ = list_rect _ _ _ ?x _ _ _ ]
               => is_var x; t_reduce_list_evar
             | [ |- _ = ?f (_, (_, _)) _ _ ]
               => is_var f; apply f_equal3
             | [ |- context[@nth'] ]
               => step_opt' || fin_step_opt
             | _ => reflexivity
             end. }

    simpl.
    reflexivity.
  Defined.


  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : _ | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'1 str nt) in
    let h := head c in
    let impl := (eval cbv beta iota zeta delta [h proj1_sig] in (proj1_sig c)) in
    (exists impl);
      abstract (exact (proj2_sig c)).
  Defined.

  Lemma parse_nonterminal_opt_eq
        {HSLP : StringLikeProperties Char}
        {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}
        (str : String)
        (nt : String.string)
    : is_correct (proj1_sig (parse_nonterminal_opt str nt)) str nt.
  Proof.
    let p := match goal with |- context[proj1_sig ?p] => p end in
    rewrite (proj2_sig p).
    apply parse_nonterminal_optdata_eq.
  Qed.
End recursive_descent_parser.
