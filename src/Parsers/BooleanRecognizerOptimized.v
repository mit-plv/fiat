(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListMorphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Common Fiat.Common.Wf Fiat.Common.Wf2 Fiat.Common.Telescope.Core.
Require Import Fiat.Parsers.GenericRecognizerExt.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.BooleanRecognizerExt.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
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
Import NPeano.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Global Arguments string_dec : simpl never.
Global Arguments string_beq : simpl never.

Module Export opt.
  Module Import opt.
    Definition first_index_default {A} := Eval compute in @Operations.List.first_index_default A.
    Definition map {A B} := Eval compute in @List.map A B.
    Definition length {A} := Eval compute in @List.length A.
    Definition uniquize {A} := Eval compute in @Operations.List.uniquize A.
    Definition string_beq := Eval compute in Equality.string_beq.
    Definition option_rect {A} := Eval compute in @option_rect A.
    Definition up_to := Eval compute in Operations.List.up_to.
    Definition rev {A} := Eval compute in @List.rev A.
    Definition combine {A B} := Eval compute in @List.combine A B.
    Definition fold_left {A B} := Eval compute in @List.fold_left A B.
    Definition fold_right {A B} := Eval compute in @List.fold_right A B.
    Definition list_rect {A} := Eval compute in @list_rect A.
    Definition hd {A} := Eval compute in @hd A.
    Definition tl {A} := Eval compute in @tl A.
    Definition nth {A} := Eval compute in @nth A.
    Definition nth' {A} := Eval cbv beta iota zeta delta -[EqNat.beq_nat] in @nth' A.
    Definition fst {A B} := Eval compute in @fst A B.
    Definition snd {A B} := Eval compute in @snd A B.
    Definition list_caset {A} := Eval compute in @list_caset A.
    Definition item_rect {A} := Eval compute in @item_rect A.
    Definition ritem_rect {A} := Eval compute in @ritem_rect A.
    Definition bool_rect := Eval compute in bool_rect.
    Definition pred := Eval compute in pred.
    Definition minusr := Eval compute in minusr.
    Definition id {A} := Eval compute in @id A.
    Definition beq_nat := Eval compute in EqNat.beq_nat.
    Definition leb := Eval compute in Compare_dec.leb.
    Definition interp_RCharExpr {Char idata} := Eval cbv -[andb orb negb Compare_dec.leb] in @interp_RCharExpr Char idata.
  End opt.

  Declare Reduction opt_red := cbv beta iota zeta delta [first_index_default map length uniquize string_beq option_rect up_to rev combine fold_left fold_right list_rect hd tl Common.opt.fst Common.opt.snd nth nth' fst snd list_caset item_rect ritem_rect bool_rect pred minusr id beq_nat leb interp_RCharExpr].
  Ltac opt_red x := eval opt_red in x.
End opt.

Module Export opt2.
  Module Import opt2.
    Definition first_index_default {A} := Eval compute in @Operations.List.first_index_default A.
    Definition map {A B} := Eval compute in @List.map A B.
    Definition length {A} := Eval compute in @List.length A.
    Definition uniquize {A} := Eval compute in @Operations.List.uniquize A.
    Definition string_beq := Eval compute in Equality.string_beq.
    Definition option_rect {A} := Eval compute in @option_rect A.
    Definition up_to := Eval compute in Operations.List.up_to.
    Definition rev {A} := Eval compute in @List.rev A.
    Definition combine {A B} := Eval compute in @List.combine A B.
    Definition fold_left {A B} := Eval compute in @List.fold_left A B.
    Definition fold_right {A B} := Eval compute in @List.fold_right A B.
    Definition list_rect {A} := Eval compute in @list_rect A.
    Definition hd {A} := Eval compute in @hd A.
    Definition tl {A} := Eval compute in @tl A.
    Definition nth {A} := Eval compute in @nth A.
    Definition nth' {A} := Eval cbv beta iota zeta delta -[EqNat.beq_nat] in @nth' A.
    Definition fst {A B} := Eval compute in @fst A B.
    Definition snd {A B} := Eval compute in @snd A B.
    Definition list_caset {A} := Eval compute in @list_caset A.
    Definition item_rect {A} := Eval compute in @item_rect A.
    Definition ritem_rect {A} := Eval compute in @ritem_rect A.
    Definition bool_rect := Eval compute in bool_rect.
    Definition pred := Eval compute in pred.
    Definition minusr := Eval compute in minusr.
    Definition id {A} := Eval compute in @id A.
    Definition beq_nat := Eval compute in EqNat.beq_nat.
    Definition leb := Eval compute in Compare_dec.leb.
    Definition interp_RCharExpr {Char idata} := Eval cbv -[andb orb negb Compare_dec.leb] in @interp_RCharExpr Char idata.
  End opt2.

  Declare Reduction opt2_red := cbv beta iota zeta delta [first_index_default map length uniquize string_beq option_rect up_to rev combine fold_left fold_right list_rect hd tl Common.opt.fst Common.opt.snd nth nth' fst snd list_caset item_rect ritem_rect bool_rect pred minusr id beq_nat leb interp_RCharExpr].
  Ltac opt2_red x := eval opt2_red in x.
End opt2.

Module Export opt3.
  Module Import opt3.
    Definition first_index_default {A} := Eval compute in @Operations.List.first_index_default A.
    Definition map {A B} := Eval compute in @List.map A B.
    Definition length {A} := Eval compute in @List.length A.
    Definition uniquize {A} := Eval compute in @Operations.List.uniquize A.
    Definition string_beq := Eval compute in Equality.string_beq.
    Definition option_rect {A} := Eval compute in @option_rect A.
    Definition up_to := Eval compute in Operations.List.up_to.
    Definition rev {A} := Eval compute in @List.rev A.
    Definition combine {A B} := Eval compute in @List.combine A B.
    Definition fold_left {A B} := Eval compute in @List.fold_left A B.
    Definition fold_right {A B} := Eval compute in @List.fold_right A B.
    Definition list_rect {A} := Eval compute in @list_rect A.
    Definition hd {A} := Eval compute in @hd A.
    Definition tl {A} := Eval compute in @tl A.
    Definition nth {A} := Eval compute in @nth A.
    Definition nth' {A} := Eval cbv beta iota zeta delta -[EqNat.beq_nat] in @nth' A.
    Definition fst {A B} := Eval compute in @fst A B.
    Definition snd {A B} := Eval compute in @snd A B.
    Definition list_caset {A} := Eval compute in @list_caset A.
    Definition item_rect {A} := Eval compute in @item_rect A.
    Definition ritem_rect {A} := Eval compute in @ritem_rect A.
    Definition bool_rect := Eval compute in bool_rect.
    Definition pred := Eval compute in pred.
    Definition minusr := Eval compute in minusr.
    Definition id {A} := Eval compute in @id A.
    Definition beq_nat := Eval compute in EqNat.beq_nat.
    Definition leb := Eval compute in Compare_dec.leb.
    Definition interp_RCharExpr {Char idata} := Eval cbv -[andb orb negb Compare_dec.leb] in @interp_RCharExpr Char idata.
  End opt3.

  Declare Reduction opt3_red := cbv beta iota zeta delta [first_index_default map length uniquize string_beq option_rect up_to rev combine fold_left fold_right list_rect hd tl Common.opt.fst Common.opt.snd nth nth' fst snd list_caset item_rect ritem_rect bool_rect pred minusr id beq_nat leb interp_RCharExpr].
  Ltac opt3_red x := eval opt3_red in x.
End opt3.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
          {G : pregrammar Char}.

  Let HNoDup' : NoDupR (fun x y => string_beq (fst x) (fst y)) (pregrammar_productions G).
  Proof.
    pose proof (nonterminals_unique G) as HNoDup.
    hnf in HNoDup |- *; unfold pregrammar_nonterminals in *; simpl in *.
    rewrite uniquize_map in HNoDup.
    apply uniquize_length.
    apply (f_equal (@List.length _)) in HNoDup.
    rewrite !map_length in HNoDup.
    rewrite !map_length, <- HNoDup; clear HNoDup.
    reflexivity.
  Qed.

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

  Local Arguments minus !_ !_.
  Local Arguments min !_ !_.

  Lemma parse_nonterminal_optdata_eq
        {HSLP : StringLikeProperties Char}
        {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}
        (str : String)
        (nt : String.string)
    : parse_nonterminal (data := optdata) str nt = parse_nonterminal (data := data) str nt.
  Proof.
    pose optsplitdata_correct.
    match goal with
    | [ |- ?LHS = ?RHS ]
      => destruct LHS eqn:HL;
        destruct RHS eqn:HR
    end;
    try reflexivity;
    exfalso;
    first [ apply (@parse_nonterminal_sound _ _ _ _ G) in HR
          | apply (@parse_nonterminal_sound _ _ _ _ G) in HL ];
    try eassumption; [ | ];
    try (apply grammar_rvalid_correct; eassumption);
    [ | ];
    first [ erewrite @parse_nonterminal_complete in HR; [ congruence | .. ]
          | erewrite @parse_nonterminal_complete in HL; [ congruence | .. ] ];
    instantiate;
    try first [ eassumption
              | apply grammar_rvalid_correct; eassumption
              | exact _ ].
  Defined.

  Local Ltac contract_drop_take_t :=
    idtac;
    match goal with
      | [ H : is_true (bool_eq ?x ?y) |- _ ] => change (beq x y) in H
      | [ H : context[is_true (bool_eq ?x ?y)] |- _ ] => change (is_true (bool_eq x y)) with (beq x y) in H
      | [ |- context[is_true (bool_eq ?x ?y)] ] => change (is_true (bool_eq x y)) with (beq x y)
      | _ => progress subst
      | [ H : beq _ _ |- _ ] => rewrite !H; clear H
      | [ |- _ = _ ] => reflexivity
      | [ |- beq _ _ ] => reflexivity
      | [ |- Equivalence _ ] => split; repeat intro
    end.

  Local Ltac t_reduce_fix :=
    repeat match goal with
             | _ => progress simpl sumbool_rect
             | _ => progress simpl option_rect
             | [ |- context[lt_dec ?x ?y] ]
               => destruct (lt_dec x y)
             | [ |- context[dec ?x] ]
               => destruct (dec x)
             | [ |- @fold_right ?A ?B ?f ?x ?ls = @fold_right ?A ?B ?f ?x ?ls' ]
               => apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@fold_right A B))
             | [ |- @fold_left ?A ?B ?f ?ls ?x = @fold_left ?A ?B ?f ?ls' ?x ]
               => apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@fold_left A B))
             | [ |- @list_caset ?A (fun _ => ?P) _ _ ?ls = @list_caset ?A (fun _ => ?P) _ _ ?ls' ]
               => apply (_ : Proper (_ ==> pointwise_relation _ (pointwise_relation _ _) ==> _ ==> eq) (@list_caset A (fun _ => P)))
             | [ |- @map ?A ?B ?f ?ls = @map ?A ?B ?f' ?ls' ]
               => apply (_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@map A B))
             | [ |- @nth' ?A ?n ?ls ?d = @nth' ?A ?n' ?ls' ?d' ]
               => apply f_equal3
             | [ |- @nth ?A ?n ?ls ?d = @nth ?A ?n' ?ls' ?d' ]
               => apply f_equal3
             | _ => intro
             | [ |- ?x = ?x ] => reflexivity
             | [ |- bool_rect ?P _ _ ?b = bool_rect ?P _ _ ?b ] => apply f_equal3
             | [ |- andb _ _ = andb _ _ ] => apply f_equal2
             | [ |- andbr _ _ = andbr _ _ ] => apply f_equal2
             | [ |- orb _ _ = orb _ _ ] => apply f_equal2
             | [ |- match ?it with Terminal _ => _ | _ => _ end = match ?it with _ => _ end ] => is_var it; destruct it
             | [ |- context[(fst ?x, snd ?x)] ] => rewrite <- !surjective_pairing
             | [ |- context[andb _ true] ] => rewrite Bool.andb_true_r
             | [ |- context[andb true _] ] => rewrite Bool.andb_true_l
             | [ |- context[andb _ false] ] => rewrite Bool.andb_false_r
             | [ |- context[andb false _] ] => rewrite Bool.andb_false_l
             | [ |- context[andb ?x true] ] => rewrite (andbr_andb x true)
             | [ |- context[andb true _] ] => rewrite (andbr_andb true)
             | [ |- context[andb ?x false] ] => rewrite (andbr_andb x false)
             | [ |- context[andbr false _] ] => rewrite (andbr_andb false)
             | [ |- context[orb _ true] ] => rewrite Bool.orb_true_r
             | [ |- context[orb true _] ] => rewrite Bool.orb_true_l
             | [ |- context[orb _ false] ] => rewrite Bool.orb_false_r
             | [ |- context[orb false _] ] => rewrite Bool.orb_false_l
             | [ |- cons _ _ = cons _ _ ]
               => apply f_equal2
             | _ => solve [ auto with nocore ]
             | [ |- prod_relation lt lt _ _ ] => hnf; simpl; omega
             | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
             | [ H : _ = in_left |- _ ] => clear H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : context[negb (EqNat.beq_nat ?x ?y)] |- _ ] => destruct (EqNat.beq_nat x y) eqn:?
             | [ H : EqNat.beq_nat _ _ = false |- _ ] => apply EqNat.beq_nat_false in H
             | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
             | [ H : snd ?x = _ |- _ ] => is_var x; destruct x
             | _ => progress simpl negb in *
             | [ H : false = true |- _ ] => inversion H
             | [ |- ?f _ (match ?p with eq_refl => ?k end) = ?f' _ ?k ]
               => destruct p
             | [ |- match ?ls with nil => _ | _ => _ end = match ?ls with _ => _ end ]
               => destruct ls eqn:?
             | [ |- match ?ls with NonTerminal _ => _ | _ => _ end = match ?ls with _ => _ end ]
               => destruct ls eqn:?
             | [ |- match ?ls with RNonTerminal _ => _ | _ => _ end = match ?ls with _ => _ end ]
               => destruct ls eqn:?
             | [ |- (if ?e then _ else _) = (if ?e then _ else _) ]
               => destruct e eqn:?
             | _ => solve [ intuition ]
             | [ H : context[sub_nonterminals_listT] |- _ ]
               => solve [ apply H;
                          intuition;
                          (etransitivity; [ | eapply sub_nonterminals_listT_remove_2; eassumption ]); simpl;
                          unfold remove_nonterminal; simpl;
                          unfold rdp_list_remove_nonterminal;
                          reflexivity ]
           end.

  Local Ltac t_reduce_list :=
    idtac;
    lazymatch goal with
    | [ |- list_rect ?P ?n ?c ?ls ?idx ?offset ?len = list_rect ?P' ?n' ?c' ?ls ?idx ?offset ?len ]
      => let n0 := fresh in
         let c0 := fresh in
         let n1 := fresh in
         let c1 := fresh in
         set (n0 := n);
         set (n1 := n');
         set (c0 := c);
         set (c1 := c');
         refine (list_rect
                   (fun ls' => forall idx' offset' len', list_rect P n0 c0 ls' idx' offset' len' = list_rect P' n1 c1 ls' idx' offset' len')
                   _
                   _
                   ls
                   idx
                   offset len);
         simpl list_rect;
         [ subst n0 c0 n1 c1; cbv beta
         | intros; unfold c0 at 1, c1 at 1 ]
    end.

  Local Ltac t_reduce_list_generalize :=
    idtac;
    match goal with
      | [ |- list_rect ?P ?n ?c ?ls ?offset ?len ?y = list_rect ?P' ?n' ?c' ?ls ?offset ?len ?y ]
        => let n0 := fresh in
           let c0 := fresh in
           let n1 := fresh in
           let c1 := fresh in
           set (n0 := n);
             set (n1 := n');
             set (c0 := c);
             set (c1 := c');
             refine (list_rect
                       (fun ls' => forall offset' len' y', list_rect P n0 c0 ls' offset' len' y' = list_rect P' n1 c1 ls' offset' len' y')
                       _
                       _
                       ls
                       offset len y);
             simpl list_rect;
             [ subst n0 c0 n1 c1; cbv beta
             | intros; unfold n0 at 1, c0 at 1, n1 at 1, c1 at 1 ]
    end.

  Local Ltac refine_Fix2_5_Proper_eq :=
    idtac;
    (lazymatch goal with
    | [ |- context[_ = @Fix2 ?A ?A' ?R ?Rwf ?T (fun a0 b0 c0 d0 e0 h0 i0 => @?f a0 b0 c0 d0 e0 h0 i0) ?a ?a' ?b ?c ?d ?e ?h] ]
      => (lazymatch T with
         | (fun a' : ?A0 => forall (b' :@?B a') (c' : @?C a' b') (d' : @?D a' b' c') (e' : @?E a' b' c' d') (h' : @?H a' b' c' d' e'), @?P a' b' c' d' e' h')
           => let H' := fresh in
              (*refine (_ : @Fix A R Rwf T (fun a0 b0 c0 d0 e0 h0 i0 => _) a b c d e h = _);
                 let f' := match goal with |- @Fix _ _ _ _ ?f' _ _ _ _ _ _ = _ => constr:(f') end in*)
              pose proof ((fun f' H0 => @Fix2_5_Proper_eq A A' B C D E H R Rwf P f' f H0 a a' b c d e h)) as H';
          cbv beta in H';
          (lazymatch type of H' with
          | forall f' : ?f'T, @?H'T f' -> _
            => let H'' := fresh in
               let f'' := fresh in
               assert (H'' : { f' : f'T & H'T f' });
           [ clear H'
           | destruct H'' as [f'' H''];
             specialize (H' f'' H'');
             clear H''; eexists; exact H' ]
           end)
          end)
     end);
    unfold forall_relation, pointwise_relation, respectful;
    cbv beta;
    eexists (fun a0 a0' b0 c0 d0 e0 h0 i0 => _); intros.

  Local Ltac refine_Fix2_5_Proper_eq_with_assumptions' HP HPpf :=
    idtac;
      (lazymatch goal with
        | [ |- context[_ = @Fix2 ?A ?A' ?R ?Rwf ?T (fun a0 b0 c0 d0 e0 h0 i0 => @?f a0 b0 c0 d0 e0 h0 i0) ?a ?a' ?b ?c ?d ?e ?h] ]
          => (lazymatch T with
               | (fun a' : ?A0 => forall (b' :@?B a') (c' : @?C a' b') (d' : @?D a' b' c') (e' : @?E a' b' c' d') (h' : @?H a' b' c' d' e'), @?P a' b' c' d' e' h')
                 => let H' := fresh in
                    pose proof ((fun f' H0 => @Fix2_5_Proper_eq_with_assumption A A' B C D E H R Rwf P HP f' f H0 a a' b c d e h HPpf)) as H';
                    cbv beta in H';
                    (lazymatch type of H' with
                      | forall f' : ?f'T, @?H'T f' -> _
                        => let H'' := fresh in
                           let f'' := fresh in
                           assert (H'' : { f' : f'T & H'T f' });
                           [ clear H'
                           | destruct H'' as [f'' H''];
                             specialize (H' f'' H'');
                             clear H''; eexists; exact H' ]
                      end)
               end)
        end);
      unfold forall_relation, pointwise_relation, respectful;
      cbv beta;
      eexists (fun a0 a0' b0 c0 d0 e0 h0 i0 => _); intros.

  Local Ltac refine_Fix2_5_Proper_eq_with_assumptions :=
    idtac;
    let HPHPpf := lazymatch goal with
        | [ |- context[Fix2 _ _ (fun (a0 : ?A0) (b0 :@?B a0) (c0 : @?C a0 b0) (d0 : @?D a0 b0) (e0 : @?E a0 b0 d0) (h0 : @?H a0 b0 d0 e0) (i0 : @?I a0 b0 d0 e0 h0) (j0 : @?J a0 b0 d0 e0 h0 i0) => _) ?a ?b ?d ?e ?h ?i ?j] ]
          => let HP := constr:(fun a0 b0 d0 e0 h0 i0 (j0 : J a0 b0 d0 e0 h0 i0) => sub_nonterminals_listT d0 initial_nonterminals_data /\ (a0 <= h0 \/ is_valid_nonterminal initial_nonterminals_data j0)) in
             let HPpfT := (eval cbv beta in (HP a b d e h i j)) in
             let HPpf := constr:(fun pf => conj pf (or_introl (reflexivity _)) : HPpfT) in
             (eval cbv beta in (HP, HPpf))
        end in
    let HP := match HPHPpf with (?HP, ?HPpf) => HP end in
    let HPpf := match HPHPpf with (?HP, ?HPpf) => HPpf end in
    let T := match type of HPpf with ?T -> _ => T end in
    let H0 := fresh "H" in
    assert (H0 : T)
      by (simpl; unfold rdp_list_initial_nonterminals_data, pregrammar'_of_pregrammar, pregrammar_productions; rewrite !map_length; reflexivity);
    let HPpf := constr:(HPpf H0) in
    refine_Fix2_5_Proper_eq_with_assumptions' HP HPpf.

  Local Ltac fin_step_opt :=
    repeat match goal with
             | [ |- _ = true ] => reflexivity
             | [ |- _ = false ] => reflexivity
             | [ |- ?x = ?x ] => reflexivity
             | [ |- _ = ?x ] => is_var x; reflexivity
             | [ |- _ = (_::_) ] => apply (f_equal2 (@cons _))
             | [ |- _ = nil ] => reflexivity
             | [ |- _ = 0 ] => reflexivity
             | [ |- _ = 1 ] => reflexivity
             | [ |- _ = None ] => reflexivity
             | [ |- _ = EqNat.beq_nat _ _ ] => apply f_equal2
             | [ |- _ = Compare_dec.leb _ _ ] => apply f_equal2
             | [ |- _ = S _ ] => apply f_equal
             | [ |- _ = string_beq _ _ ] => apply f_equal2
             | [ |- _ = fst ?x ] => is_var x; reflexivity
             | [ |- _ = snd ?x ] => is_var x; reflexivity
             | [ |- _ = pregrammar_productions ?x ] => is_var x; reflexivity
             | [ |- _ = pregrammar_rproductions ?x ] => is_var x; reflexivity
             | [ |- context[(0 - _)%natr] ] => rewrite (minusr_minus 0); simpl (minus 0)
             | [ |- _ = (_, _) ] => apply f_equal2
             | _ => progress cbv beta
             | [ |- context[orb _ false] ] => rewrite Bool.orb_false_r
             | [ |- context[orb _ true] ] => rewrite Bool.orb_true_r
             | [ |- context[andbr _ false] ] => rewrite (andbr_andb _ false)
             | [ |- context[andbr _ true] ] => rewrite (andbr_andb _ true)
             | [ |- context[andb _ false] ] => rewrite Bool.andb_false_r
             | [ |- context[andb _ true] ] => rewrite Bool.andb_true_r
           end.

  Local Ltac misc_opt' :=
    idtac;
    match goal with
    | _ => progress rewrite ?max_min_n, ?Minus.minus_diag, ?Nat.sub_0_r, ?uneta_bool, ?beq_nat_min_0(*, ?bool_rect_flatten*)
    | _ => rewrite Min.min_l by assumption
    | _ => rewrite Min.min_r by assumption
    | [ |- context[if ?ltb ?x ?y then _ else _] ] => rewrite if_to_min
    | [ |- context[min ?x ?y - ?x] ] => rewrite min_sub_same
    | [ |- context[(min ?x ?y - ?x)%natr] ] => rewrite min_subr_same
    | [ |- context[?x - (?x - ?y)%natr] ]
      => rewrite !(minusr_minus x y), sub_twice, <- ?minusr_minus
    | _ => progress fin_step_opt
    end.

  Local Ltac misc_opt := set_evars; progress repeat misc_opt'; subst_evars.

  Local Ltac step_opt' :=
    idtac;
    match goal with
      | _ => rewrite <- !minusr_minus
      | [ |- _ = @option_rect ?A ?B (fun s => _) _ _ ]
        => refine (_ : @option_rect A B (fun s => _) _ _ = _);
          apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _ ==> eq) (@option_rect A B));
          repeat intro
      | [ |- _ = @bool_rect ?A _ _ _ ]
        => refine (_ : @bool_rect A _ _ _ = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@bool_rect A));
          repeat intro
      | [ |- _ = fold_right orb false _ ]
        => rewrite <- !(@fold_symmetric _ orb) by first [ apply Bool.orb_assoc | apply Bool.orb_comm ]
      | [ |- _ = @fold_left ?A ?B orb _ false ]
        => refine (_ : fold_left orb _ false = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
      | [ |- _ = @fold_left ?A ?B orbr _ false ]
        => refine (_ : fold_left orbr _ false = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
      | [ |- _ = @fold_right ?A ?B (fun x y => _) _ _ ]
        => refine (_ : fold_right (fun x y => _) _ _ = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_right A B)); repeat intro
      | [ |- _ = @map ?A ?B _ _ ]
        => refine (_ : @map A B (fun x => _) _ = _);
          apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _) (@map A B)); repeat intro
      | [ |- _ = @list_caset ?A ?P _ _ _ ]
        => refine (_ : @list_caset A P _ _ _ = _);
          apply (_ : Proper (forall_relation _ ==> forall_relation (fun _ => forall_relation _) ==> forall_relation _) (@list_caset A P)); repeat intro
      | [ |- _ = @list_caset ?A (fun _ => ?P) _ _ _ ]
        => refine (_ : @list_caset A (fun _ => P) _ _ _ = _);
          apply (_ : Proper (_ ==> pointwise_relation _ (pointwise_relation _ _) ==> _ ==> _) (@list_caset A (fun _ => P))); repeat intro
      | [ |- _ = @nth ?A _ _ _ ]
        => rewrite <- nth'_nth
      | [ |- _ = @nth' ?A _ _ _ ]
        => refine (_ : @nth' A _ _ _ = _);
          apply f_equal3
      | [ |- _ = sumbool_rect ?T ?A ?B ?c ]
        => let A' := fresh in
           let B' := fresh in
           let TA := type of A in
           let TB := type of B in
           evar (A' : TA); evar (B' : TB);
           refine (sumbool_rect
                     (fun c' => sumbool_rect T A' B' c' = sumbool_rect T A B c')
                     _ _ c); intro; subst A' B'; simpl @sumbool_rect
      | [ |- ?e = match ?ls with nil => _ | _ => _ end ]
        => is_evar e; refine (_ : match ls with nil => _ | _ => _ end = _)
      | [ |- match ?ls with nil => ?A | x::xs => @?B x xs end = match ?ls with nil => ?A' | x'::xs' => @?B' x' xs' end ]
        => refine (match ls
                         as ls'
                         return match ls' with nil => A | x::xs => B x xs end = match ls' with nil => A' | x'::xs' => B' x' xs' end
                   with
                     | nil => _
                     | _ => _
                   end)
      | [ |- _ = item_rect ?T ?A ?B ?c ] (* evar kludge following *)
        => revert c;
          let RHS := match goal with |- forall c', _ = ?RHS c' => RHS end in
          let f := constr:(fun TC NC =>
                             forall c, item_rect T TC NC c = RHS c) in
          let f := (eval cbv beta in f) in
          let e1 := fresh in
          let e2 := fresh in
          match type of f with
            | ?X -> ?Y -> _
              => evar (e1 : X); evar (e2 : Y)
          end;
            intro c;
            let ty := constr:(item_rect T e1 e2 c = RHS c) in
            etransitivity_rev _; [ refine (_ : ty) | reflexivity ];
            revert c;
            refine (item_rect
                      (fun c => item_rect T e1 e2 c = RHS c)
                      _ _);
            intro c; simpl @item_rect; subst e1 e2
      | [ |- _ = ritem_rect ?T ?A ?B ?c ] (* evar kludge following *)
        => revert c;
          let RHS := match goal with |- forall c', _ = ?RHS c' => RHS end in
          let f := constr:(fun TC NC =>
                             forall c, ritem_rect T TC NC c = RHS c) in
          let f := (eval cbv beta in f) in
          let e1 := fresh in
          let e2 := fresh in
          match type of f with
            | ?X -> ?Y -> _
              => evar (e1 : X); evar (e2 : Y)
          end;
            intro c;
            let ty := constr:(ritem_rect T e1 e2 c = RHS c) in
            etransitivity_rev _; [ refine (_ : ty) | reflexivity ];
            revert c;
            refine (ritem_rect
                      (fun c => ritem_rect T e1 e2 c = RHS c)
                      _ _);
            intro c; simpl @ritem_rect; subst e1 e2
      | [ |- _ = match ?x with true => true | false => false end ]
        => transitivity x; [ | destruct x; reflexivity ]
    end;
    fin_step_opt.

  Local Ltac step_opt := repeat step_opt'.

  Local Ltac sigL_transitivity term :=
    idtac;
    (lazymatch goal with
    | [ |- ?sig (fun x : ?T => @?A x = ?B) ]
      => (let H := fresh in
          let H' := fresh in
          assert (H : sig (fun x : T => A x = term));
          [
          | assert (H' : term = B);
            [ clear H
            | let x' := fresh in
              destruct H as [x' H];
                exists x'; transitivity term; [ exact H | exact H' ] ] ])
     end).

  Local Ltac fix_trans_helper RHS x y :=
    match RHS with
      | context G[y] => let RHS' := context G[x] in
                           fix_trans_helper RHS' x y
      | _ => constr:(RHS)
    end.

  Local Ltac fix2_trans :=
    match goal with
      | [ H : forall a0 a0' a1 a2 a3 a4 a5 a6, ?x a0 a0' a1 a2 a3 a4 a5 a6 = ?y a0 a0' a1 a2 a3 a4 a5 a6 |- _ = ?RHS ]
        => let RHS' := fix_trans_helper RHS x y
           in transitivity RHS'; [ clear H y | ]
    end.

  Local Ltac fix2_trans_with_assumptions :=
    match goal with
      | [ H : forall a0 a0' a1 a2 a3 a4 a5 a6, _ -> ?x a0 a0' a1 a2 a3 a4 a5 a6 = ?y a0 a0' a1 a2 a3 a4 a5 a6 |- _ = ?RHS ]
        => let RHS' := fix_trans_helper RHS x y
           in transitivity RHS'; [ clear H y | ]
    end.

  Local Ltac t_prereduce_list_evar :=
    idtac;
    let RHS := match goal with |- _ = ?RHS => RHS end in
    lazymatch RHS with
    | context RHS'[list_rect ?P ?f ?g]
      => let ft := type of f in
         let gt := type of g in
         let f' := fresh in
         let g' := fresh in
         evar (f' : ft); evar (g' : gt);
         let f0 := (eval unfold f' in f') in
         let g0 := (eval unfold g' in g') in
         let RHS'' := context RHS'[list_rect P f0 g0] in
         refine (_ : RHS'' = _)
    end.

  Local Ltac t_postreduce_list :=
    idtac;
    lazymatch goal with
      | [ |- list_rect ?P ?N ?C ?ls ?a ?b ?c = list_rect ?P ?N' ?C' ?ls ?a ?b ?c ]
        => let P0 := fresh in
           let N0 := fresh in
           let C0 := fresh in
           let N1 := fresh in
           let C1 := fresh in
           set (P0 := P);
             set (N0 := N);
             set (C0 := C);
             set (N1 := N');
             set (C1 := C');
             let IH := fresh "IH" in
             let xs := fresh "xs" in
             refine (list_rect
                       (fun ls' => forall a' b' c',
                                     list_rect P0 N0 C0 ls' a' b' c'
                                     = list_rect P0 N1 C1 ls' a' b' c')
                       _
                       _
                       ls a b c);
               simpl @list_rect;
               [ subst P0 N0 C0 N1 C1; intros; cbv beta
               | intros ? xs IH; intros; unfold C0 at 1, C1 at 1; cbv beta;
                 setoid_rewrite <- IH; clear IH N1 C1;
                 generalize (list_rect P0 N0 C0 xs); intro ]
    end.

  Local Ltac t_reduce_list_evar :=
    t_prereduce_list_evar;
    t_postreduce_list.

  Local Ltac t_postreduce_list_with_hyp :=
    idtac;
    match goal with
      | [ |- list_rect ?P ?N ?C (?f ?a) ?a ?b ?c = list_rect ?P ?N' ?C' (?f ?a) ?a ?b ?c ]
        => let P0 := fresh in
           let N0 := fresh in
           let C0 := fresh in
           let N1 := fresh in
           let C1 := fresh in
           set (P0 := P);
             set (N0 := N);
             set (C0 := C);
             set (N1 := N');
             set (C1 := C');
             let IH := fresh "IH" in
             let xs := fresh "xs" in
             refine (list_rect
                       (fun ls' => forall a' (pf : ls' = f a') b' c',
                                     list_rect P0 N0 C0 ls' a' b' c'
                                     = list_rect P0 N1 C1 ls' a' b' c')
                       _
                       _
                       (f a) a eq_refl b c);
               simpl @list_rect;
               [ subst P0 N0 C0 N1 C1; intros; cbv beta
               | intros ? xs IH; intros; unfold C0 at 1, C1 at 1; cbv beta;
                 match goal with
                   | [ |- context[list_rect P0 N1 C1 ?ls'' ?a''] ]
                     => specialize (IH a'')
                 end;
                 let T := match type of IH with ?T -> _ => T end in
                 let H_helper := fresh in
                 assert (H_helper : T);
                   [
                     | specialize (IH H_helper);
                       setoid_rewrite <- IH; clear IH N1 C1;
                       generalize (list_rect P0 N0 C0 xs); intro ] ]
    end.

  Local Ltac t_postreduce_list_with_hyp_with_assumption :=
    idtac;
    lazymatch goal with
      | [ H : ?HP (?HP' (?f ?a)) = true |- list_rect ?P ?N ?C (?f ?a) ?a ?b ?c = list_rect ?P ?N' ?C' (?f ?a) ?a ?b ?c ]
        => let P0 := fresh in
           let N0 := fresh in
           let C0 := fresh in
           let N1 := fresh in
           let C1 := fresh in
           set (P0 := P);
             set (N0 := N);
             set (C0 := C);
             set (N1 := N');
             set (C1 := C');
             let IH := fresh "IH" in
             let xs := fresh "xs" in
             let pf := fresh "pf" in
             refine (list_rect
                       (fun ls' => forall a' (pf : ls' = f a') (H' : HP (HP' (f a')) = true) b' c',
                                     list_rect P0 N0 C0 ls' a' b' c'
                                     = list_rect P0 N1 C1 ls' a' b' c')
                       _
                       _
                       (f a) a eq_refl H b c);
               simpl @list_rect;
               [ subst P0 N0 C0 N1 C1; intros; cbv beta
               | intros ? xs IH pg; intros; unfold C0 at 1, C1 at 1; cbv beta;
                 match goal with
                   | [ |- context[list_rect P0 N1 C1 ?ls'' ?a''] ]
                     => specialize (IH a'')
                 end;
                 let T := match type of IH with ?T1 -> ?T2 -> _ => constr:((T1 * T2)%type) end in
                 let H_helper := fresh in
                 let H_helper' := fresh in
                 assert (H_helper : T);
                   [ split
                     | specialize (IH (fst H_helper) (snd H_helper));
                       setoid_rewrite <- IH; clear IH N1 C1;
                       generalize (list_rect P0 N0 C0 xs); intro ] ]
    end.

  Local Ltac t_reduce_list_evar_with_hyp :=
    t_prereduce_list_evar;
    t_postreduce_list_with_hyp.

  Local Ltac t_refine_item_match_terminal :=
    idtac;
    match goal with
      | [ |- _ = match ?it with Terminal _ => _ | NonTerminal nt => @?NT nt end :> ?T ]
        => refine (_ : item_rect (fun _ => T) _ NT it = _);
          revert it;
          refine (item_rect
                    _
                    _
                    _); simpl @item_rect; intro;
          [ | reflexivity ]
    end.

  Local Ltac t_refine_item_match :=
    idtac;
    (lazymatch goal with
      | [ |- _ = match ?it with Terminal _ => _ | _ => _ end :> ?T ]
        => (refine (_ : item_rect (fun _ => T) _ _ it = _);
          (lazymatch goal with
            | [ |- item_rect ?P ?TC ?NC it = match it with Terminal t => @?TC' t | NonTerminal nt => @?NC' nt end ]
              => refine (item_rect
                           (fun it' => item_rect (fun _ => T) TC NC it'
                                       = item_rect (fun _ => T) TC' NC' it')
                           _
                           _
                           it)
          end;
          clear it; simpl @item_rect; intro))
    end).

  Local Arguments Compare_dec.leb !_ !_.
  Local Arguments to_nonterminal / _ _ _.

  Local Instance good_nth_proper {A}
  : Proper (eq ==> _ ==> _ ==> eq) (nth (A:=A))
    := _.
  Local Instance good_nth'_proper {A}
  : Proper (eq ==> _ ==> _ ==> eq) (nth' (A:=A))
    := _.

  Local Ltac rewrite_map_nth_rhs :=
    idtac;
    match goal with
      | [ |- _ = ?RHS ]
        => let v := match RHS with
                      | context[match nth ?n ?ls ?d with _ => _ end]
                        => constr:(nth n ls d)
                      | context[nth ?n ?ls ?d]
                        => constr:(nth n ls d)
                    end in
           let P := match (eval pattern v in RHS) with
                      | ?P _ => P
                    end in
           rewrite <- (map_nth P)
    end.

  Local Ltac rewrite_map_nth_dep_rhs :=
    idtac;
    match goal with
      | [ |- _ = ?RHS ]
        => let v := match RHS with
                      | context[match nth ?n ?ls ?d with _ => _ end]
                        => constr:(nth n ls d)
                      | context[nth ?n ?ls ?d]
                        => constr:(nth n ls d)
                    end in
           let n := match v with nth ?n ?ls ?d => n end in
           let ls := match v with nth ?n ?ls ?d => ls end in
           let d := match v with nth ?n ?ls ?d => d end in
           let P := match (eval pattern v in RHS) with
                      | ?P _ => P
                    end in
           let P := match (eval pattern n in P) with
                      | ?P _ => P
                    end in
           rewrite <- (map_nth_dep P ls d n)
    end.

  Local Ltac t_pull_nth :=
    repeat match goal with
             | _ => rewrite drop_all by (simpl; omega)
             | [ |- _ = nth _ _ _ ] => step_opt'
             | [ |- _ = nth' _ _ _ ] => step_opt'
             | _ => rewrite !map_map
             | _ => progress simpl
             | _ => rewrite <- !surjective_pairing
             | _ => progress rewrite_map_nth_rhs
           end;
    fin_step_opt.
  Local Ltac t_after_pull_nth_fin :=
    idtac;
    match goal with
      | [ |- context[@nth] ] => fail 1
      | [ |- context[@nth'] ] => fail 1
      | _ => repeat step_opt'
    end.

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

  Lemma opt_helper_minusr_proof
  : forall {len0 len}, len <= len0 -> forall n : nat, (len - n)%natr <= len0.
  Proof.
    clear.
    intros.
    rewrite minusr_minus; omega.
  Qed.

  Definition parse_nonterminal_opt'0
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    exists (parse_nonterminal (data := optdata) str nt).
    reflexivity.
  Defined.

  Local Ltac optsplit_t' :=
    idtac;
    match goal with
      | [ |- _ = ?f match ?v with nil => ?N | x::xs => @?C x xs end ]
        => let RHS := match goal with |- _ = ?RHS => RHS end in
           let P := match (eval pattern v in RHS) with ?P _ => P end in
           transitivity (match v with
                           | nil => P nil
                           | x::xs => P (x::xs)
                         end);
             [ simpl | destruct v; reflexivity ]
      | [ |- _ = ?f match ?v with Terminal t => @?T t | NonTerminal nt => @?NT nt end ]
        => let RHS := match goal with |- _ = ?RHS => RHS end in
           let P := match (eval pattern v in RHS) with ?P _ => P end in
           transitivity (match v with
                           | Terminal t => P (Terminal t)
                           | NonTerminal nt => P (NonTerminal nt)
                         end);
             [ simpl | destruct v; reflexivity ]
      | [ |- ?e = match ?v with nil => ?N | x::xs => @?C x xs end :> ?T ]
        => idtac;
          repeat match goal with
                 | [ H : context[v] |- _ ]
                   => hnf in H;
                     match type of H with
                     | context[v] => fail 1
                     | _ => idtac
                     end
                 end;
          let P := match (eval pattern v in T) with ?P _ => P end in
          change (e = list_caset P N C v);
            revert dependent v;
            let NT := type of N in
            let CT := type of C in
            let N' := fresh in
            let C' := fresh in
            evar (N' : NT);
              evar (C' : CT);
              intro v; intros;
              refine (_ : list_caset P N' C' v = list_caset P N C v);
              refine (list_caset
                        (fun v' => list_caset P N' C' v' = list_caset P N C v')
                        _
                        _
                        v);
              subst N' C'; simpl @list_caset; repeat intro
      | [ H : is_true (item_rvalid ?G ?v)
          |- ?e = match ?v with Terminal t => @?T t | NonTerminal nt => @?NT nt end ]
        => idtac; let TT := type of T in
                  let NTT := type of NT in
                  let T' := fresh in
                  let NT' := fresh in
                  revert dependent v;
                    evar (T' : TT);
                    evar (NT' : NTT);
                    intro v; intros;
                    let eqP := match goal with |- _ = _ :> ?P => P end in
                    let P := match (eval pattern v in eqP) with ?P _ => P end in
                      change (e = item_rect P T NT v);
                      refine (_ : item_rect P T' NT' v = item_rect P T NT v);
                      refine (item_rect
                                (fun v' => item_rvalid G v' -> item_rect P T' NT' v' = item_rect P T NT v')
                                _
                                _
                                v H);
                      subst T' NT';
                      simpl @item_rect; intros ??
      | [ |- ?e = match ?v with Terminal t => @?T t | NonTerminal nt => @?NT nt end ]
        => idtac; let TT := type of T in
                  let NTT := type of NT in
                  let T' := fresh in
                  let NT' := fresh in
                  revert dependent v;
                    evar (T' : TT);
                    evar (NT' : NTT);
                    intro v; intros;
                    let eqP := match goal with |- _ = _ :> ?P => P end in
                    let P := match (eval pattern v in eqP) with ?P _ => P end in
                      change (e = item_rect P T NT v);
                      refine (_ : item_rect P T' NT' v = item_rect P T NT v);
                      refine (item_rect
                                (fun v' => item_rect P T' NT' v' = item_rect P T NT v')
                                _
                                _
                                v);
                      subst T' NT';
                      simpl @item_rect; intro
      | [ |- _ = _::_ ] => etransitivity_rev (_::_);
                          [ apply f_equal2
                          | reflexivity ]
      | _ => progress fin_step_opt
    end.

  Local Unset Keyed Unification.
  Definition parse_nonterminal_opt'1
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'0 str nt) in
    let h := head c in
    let p := (eval cbv beta iota zeta delta [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].
    cbv beta iota zeta delta [parse_nonterminal GenericRecognizer.parse_nonterminal parse_nonterminal' GenericRecognizer.parse_nonterminal' parse_nonterminal_or_abort GenericRecognizer.parse_nonterminal_or_abort list_to_grammar].
    simpl @GenericBaseTypes.parse_nt_T.
    change (@GenericRecognizer.parse_nonterminal_step Char) with (fun b c d e f g h i j k l m => @GenericRecognizer.parse_nonterminal_step Char b c d e f g h i j k l m); cbv beta.
    evar (b' : bool).
    sigL_transitivity b'; subst b';
    [
    | rewrite Fix5_2_5_eq by (intros; rapply (@parse_nonterminal_step_ext _ _ _ optdata _); assumption);
      reflexivity ].
    simpl @fst; simpl @snd.
    cbv beta iota zeta delta [parse_nonterminal_step parse_productions parse_productions' parse_production parse_item parse_item' GenericRecognizer.parse_nonterminal_step GenericRecognizer.parse_productions GenericRecognizer.parse_productions' GenericRecognizer.parse_production GenericRecognizer.parse_item GenericRecognizer.parse_item' Lookup list_to_grammar list_to_productions GenericBaseTypes.parse_nt_T boolean_gendata GenericBaseTypes.ret_nt GenericBaseTypes.ret_nt_invalid].
    simpl.
    cbv beta iota zeta delta [predata BaseTypes.predata initial_nonterminals_data nonterminals_length remove_nonterminal production_carrierT].
    cbv beta iota zeta delta [rdp_list_predata Carriers.default_production_carrierT rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data rdp_list_remove_nonterminal Carriers.default_nonterminal_carrierT rdp_list_nonterminals_listT rdp_list_production_tl Carriers.default_nonterminal_carrierT].
    (*cbv beta iota zeta delta [rdp_list_of_nonterminal].*)
    simpl; unfold pregrammar_nonterminals; simpl.
    evar (b' : bool).
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
        apply map_Proper_eq_In; intros ? Hin.
        specialize (Hvalid''' _ Hin).
        unfold parse_production', parse_production'_for, GenericRecognizer.parse_production', GenericRecognizer.parse_production'_for.
        cbv [GenericBaseTypes.parse_production_T].
        simpl.
        (** Switch to using the list hypothesis, rather than lookup with the index *)
        etransitivity_rev _.
        { t_reduce_list_evar_with_hyp;
          [
          |
          | ].
          { misc_opt; reflexivity. }
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
                                              (list_rect P0 (fun _ _ _ => true) C0 ls' a' b' c')
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
            unfold parse_item', GenericRecognizer.parse_item'.
            step_opt'.
            repeat match goal with
                     | [ |- context[List.map _ match ?e with _ => _ end] ]
                       => is_var e; destruct e
                     | _ => progress simpl
                     | [ |- ?x = ?x ] => reflexivity
                     | _ => progress rewrite ?Bool.andb_true_r, ?Min.min_idempotent, ?Minus.minus_diag
                     | [ H : EqNat.beq_nat _ _ = true |- _ ]
                       => apply EqNat.beq_nat_true in H
                     | _ => progress subst
                     | [ |- context[EqNat.beq_nat ?x ?y] ]
                       => is_var x; destruct (EqNat.beq_nat x y) eqn:?
                     | [ H := _ |- _ ] => subst H
                     | [ |- context[orb _ false] ] => rewrite Bool.orb_false_r
                     | _ => rewrite minusr_minus
                     | [ |- context[?x - (?y + (?x - ?y)) ] ]
                       => replace (x - (y + (x - y))) with 0 by (clear; omega)
                   end. } }
        cbv beta.
        misc_opt.
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
          { do 3 step_opt'; [].
            etransitivity_rev _.
            { repeat optsplit_t'.
              { misc_opt.
                rewrite <- andbr_andb.
                apply (f_equal2 andbr); [ | reflexivity ].
                rewrite Min.min_idempotent.
                reflexivity. }
              { apply (f_equal2 andb); [ | reflexivity ].
                step_opt'; [].
                apply (f_equal2 andb); [ | reflexivity ].
                match goal with
                | [ |- _ = EqNat.beq_nat (min ?v ?x) ?v ]
                  => refine (_ : Compare_dec.leb v x = _)
                end.
                match goal with
                | [ |- Compare_dec.leb 1 ?x = _ ]
                  => destruct x as [|[|]]; try reflexivity
                end. }
              { simpl in *.
                match goal with
                | [ H : is_true ?x |- context[?x] ] => rewrite H
                end.
                reflexivity. } }
            reflexivity. }
          etransitivity_rev _.
          { rewrite !(@fold_symmetric _ orb) by first [ apply Bool.orb_assoc | apply Bool.orb_comm ].
            unfold parse_item', GenericRecognizer.parse_item'.
            simpl.
            repeat optsplit_t'; repeat step_opt';
              [ apply (f_equal2 andb) | ];
              repeat optsplit_t'; try misc_opt; repeat step_opt'.
            { rewrite !minusr_minus, <- max_def, <- !minusr_minus.
              reflexivity. }
            { reflexivity. }
            { simpl in *.
              set_evars.
              match goal with
              | [ H : is_true ?x |- context[?x] ] => rewrite H
              end.
              match goal with
              | [ H := ?e |- _ ] => is_evar e; subst H
              end.
              reflexivity. }
            { reflexivity. } }
          reflexivity. }
        reflexivity. }

      unfold productions, production, rproductions, rproduction.
      progress cbv beta iota zeta delta [rdp_list_predata Carriers.default_production_carrierT rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data rdp_list_remove_nonterminal Carriers.default_nonterminal_carrierT rdp_list_nonterminals_listT rdp_list_production_tl Carriers.default_nonterminal_carrierT].

      step_opt'; [ | reflexivity ].
      step_opt'.
      step_opt'.
      etransitivity_rev _.
      { cbv beta iota delta [rdp_list_nonterminal_to_production Carriers.default_production_carrierT Carriers.default_nonterminal_carrierT].
        simpl rewrite list_to_productions_to_nonterminal; unfold Lookup_idx.
        etransitivity_rev _.
        { step_opt'; [ reflexivity | ].
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
                     | apply (f_equal2 (@cons _))
                     | t_refine_item_match ];
        first [ progress unfold rdp_list_of_nonterminal, default_of_nonterminal, Valid_nonterminals, grammar_of_pregrammar, pregrammar_nonterminals; simpl;
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
                            | [ |- context[List.nth (@List.length ?B (@List.map ?A ?B ?f ?ls) - _)] ]
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
            rewrite bool_rect_andb; simpl.
            rewrite Bool.andb_true_r.
            match goal with
            | [ |- _ = (orb (negb (EqNat.beq_nat ?x 0)) (andb (EqNat.beq_nat ?x 0) ?y)) ]
              => let z := fresh in
                 let y' := fresh in
                 set (z := x);
                   set (y' := y);
                   refine (_ : orb (Compare_dec.leb 1 x) y = _);
                   change (orb (Compare_dec.leb 1 z) y' = orb (negb (EqNat.beq_nat z 0)) (andb (EqNat.beq_nat z 0) y'));
                   destruct z, y'; reflexivity
            end. }
          etransitivity_rev _.
          { apply (f_equal2 (inner_nth' _)); [ | reflexivity ].
            step_opt'; [ ].
            change @inner_nth' with @nth' at 1.
            rewrite nth'_nth.
            rewrite_map_nth_rhs; rewrite !map_map; simpl.
            rewrite <- nth'_nth.
            change @nth' with @inner_nth' at 1.
            reflexivity. }
          reflexivity. }
        (*etransitivity_rev _.
        { change @inner_nth' with @nth' at 1.
          etransitivity_rev _.
          { step_opt'.
            etransitivity_rev _.
            { step_opt'.
              rewrite nth'_nth; reflexivity. }
            match goal with
              | [ |- _ = map (fun x => nth ?n (@?ls x) ?d) ?ls' ]
                => etransitivity_rev (map (fun ls'' => nth n ls'' d) (map ls ls'));
                  [ rewrite !map_map; reflexivity | ]
            end.
            reflexivity. }*)
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
        { set_evars.
          setoid_rewrite combine_map_r.
          do 2 setoid_rewrite map_map; simpl.
          setoid_rewrite map_length.
          progress change (fun x : ?A * ?B => fst x) with (@fst A B).
          subst_evars.

          reflexivity. }
        { set_evars.
          setoid_rewrite combine_map_r.
          subst_evars.

          step_opt'.
          { set_evars.
            do 2 setoid_rewrite map_map; simpl.
            setoid_rewrite map_length.
            rewrite !Nat.add_1_r.
            subst_evars.

            reflexivity. }
          { step_opt'; [ | reflexivity ].
            set_evars.
            do 2 setoid_rewrite map_map; simpl.
            setoid_rewrite map_length.
            progress change (fun x : ?A * ?B => fst x) with (@fst A B).
            subst_evars.

            reflexivity. } } }
      { reflexivity. } }

    simpl.
    reflexivity.
  Defined.

  Local Ltac change_char_at_matches :=
    idtac;
    lazymatch goal with
    | [ |- context G[@char_at_matches ?Char ?HSLM ?n ?str (@interp_RCharExpr _ ?data ?P)] ]
      => idtac;
         let G' := context G[@char_at_matches_interp Char HSLM data n str P] in
         change G'
    end.

  Definition parse_nonterminal_opt'2
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'1 str nt) in
    let h := head c in
    let p := (eval cbv beta iota zeta delta [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].
    refine_Fix2_5_Proper_eq.
    etransitivity_rev _.
    { fix2_trans;
      [
      | solve [ change @opt3.nth' with @nth';
                change @opt2.map with @List.map;
                change @inner_nth' with @nth';
                t_reduce_fix;
                t_postreduce_list;
                unfold ritem_rect;
                t_reduce_fix ] ].
      reflexivity. }

    (** [nth'] is useful when the index is unknown at top-level, but performs poorly in [simpl] when the index is eventually known at compile-time.  So we need to remove the [nth'] *)
    etransitivity_rev _.
    { change @inner_nth' with @nth'.
      step_opt'; [ | reflexivity ].
      step_opt'; [].
      apply (f_equal2 (nth' _)); [ | reflexivity ].
      step_opt'; [ | reflexivity ].
      step_opt'; [].
      rewrite !nth'_nth; apply (f_equal2 (nth _)); [ | ].
      { step_opt'; [ ].
        rewrite !nth'_nth; apply (f_equal2 (nth _)); [ | ].
        { step_opt'; [].
          match goal with
          | [ |- _ = @bool_rect (fun _ => ?P) _ _ _ ]
            => apply (f_equal3 (bool_rect (fun _ => P)))
          end; [ reflexivity | | ];
          fin_step_opt.
          { t_reduce_list_evar; [ reflexivity | ].
            step_opt'; [].
            step_opt'; [ | ].
            { rewrite nth'_nth.
              rewrite <- andbr_andb at 1.
              apply (f_equal2 andbr).
              { match goal with
                | [ |- _ = ?f ?x ?a ?b ]
                  => refine (f_equal (fun x' => f x' a b) _)
                end.
                fin_step_opt; [ reflexivity | ].
                apply (f_equal2 (nth _)); [ | reflexivity ].
                step_opt'; [ | reflexivity ].
                rewrite nth'_nth; reflexivity. }
              { step_opt'; [ | reflexivity ].
                change_char_at_matches.
                reflexivity. } }
            { step_opt'.
              { rewrite <- andbr_andb at 1.
                apply (f_equal2 andbr); [ | ].
                { change_char_at_matches.
                  reflexivity. }
                { rewrite nth'_nth.
                  match goal with
                  | [ |- _ = ?f ?x ?a ?b ]
                    => refine (f_equal (fun x' => f x' a b) _)
                  end.
                  fin_step_opt; [ reflexivity | ].
                  apply (f_equal2 (nth _)); [ | reflexivity ].
                  step_opt'; [ | reflexivity ].
                  rewrite nth'_nth; reflexivity. } }
              { step_opt'; [ | reflexivity ].
                apply (f_equal2 andb); [ reflexivity | ].
                rewrite nth'_nth.
                match goal with
                | [ |- _ = ?f ?x ?a ?b ]
                  => refine (f_equal (fun x' => f x' a b) _)
                end.
                fin_step_opt; [ reflexivity | ].
                apply (f_equal2 (nth _)); [ | reflexivity ].
                step_opt'; [ | reflexivity ].
                rewrite nth'_nth; reflexivity. } } }
          { apply (f_equal2 (nth _)); [ | reflexivity ].
            step_opt'; [ ].
            step_opt'; [ progress simpl ].
            rewrite nth'_nth.
            apply (f_equal2 (nth _)); [ | reflexivity ].
            reflexivity. } }
        { etransitivity_rev _.
          { rewrite bool_rect_andb.
            rewrite Bool.andb_true_r.
            match goal with
            | [ |- _ = (orb (negb (EqNat.beq_nat ?x 0)) (andb (EqNat.beq_nat ?x 0) ?y)) ]
              => let z := fresh in
                 let y' := fresh in
                 set (z := x);
                   set (y' := y);
                   refine (_ : orb (Compare_dec.leb 1 x) y = _);
                   change (orb (Compare_dec.leb 1 z) y' = orb (negb (EqNat.beq_nat z 0)) (andb (EqNat.beq_nat z 0) y'));
                   destruct z, y'; reflexivity
            end. }
          apply (f_equal2 orb); fin_step_opt; [].
          apply (f_equal2 (nth _)); [ | reflexivity ].
          step_opt'; [ ].
          step_opt'; [ progress simpl ].
          rewrite nth'_nth.
          apply (f_equal2 (nth _)); [ | reflexivity ].
          reflexivity. } }
      { apply (f_equal2 orb); fin_step_opt; [].
        apply (f_equal2 (nth _)); [ | reflexivity ].
        step_opt'; [ ].
        step_opt'; [ progress simpl ].
        rewrite nth'_nth.
        apply (f_equal2 (nth _)); [ | reflexivity ].
        reflexivity. } }
    change @nth' with @inner_nth' at 1.
    match goal with
      | [ |- context[@nth'] ] => fail 1
      | _ => change @inner_nth' with @nth'
    end.
    etransitivity_rev _.
    { step_opt'; [ | reflexivity ].
      rewrite nth'_nth at 1.
      rewrite_map_nth_rhs; rewrite !map_map; simpl.
      rewrite <- nth'_nth at 1.
      reflexivity. }

    reflexivity.
  Defined.

  Local Ltac safe_change_opt' :=
    idtac;
    match goal with
    | [ |- context G[minusr (opt.id ?x) (opt.id ?y)] ]
      => let G' := context G[opt.id (opt.minusr x y)] in
         change G'
    | [ |- context G[minusr (opt.id ?x) (opt2.id ?y)] ]
      => let G' := context G[opt2.id (opt2.minusr x y)] in
         change G'
    | [ |- context G[fst (opt.id ?x)] ]
      => let G' := context G[opt.id (opt.fst x)] in
         change G'
    | [ |- context G[snd (opt.id ?x)] ]
      => let G' := context G[opt.id (opt.snd x)] in
         change G'
    | [ |- context G[fst (opt2.id ?x)] ]
      => let G' := context G[opt2.id (opt2.fst x)] in
         change G'
    | [ |- context G[snd (opt2.id ?x)] ]
      => let G' := context G[opt2.id (opt2.snd x)] in
         change G'
    | [ |- context G[nth (opt2.id ?x) ?ls ?d] ]
      => let G' := context G[opt2.id (opt2.nth x ls d)] in
         change G'
    | [ |- context G[StringLike.length (opt.id ?str)] ]
      => let G' := context G[StringLike.length str] in
         change G'
    | [ |- context G[map (opt.id ?f) (opt.id ?x)] ]
      => let G' := context G[opt.id (opt.map f x)] in
         change G'
    | [ |- context G[map fst (opt.id ?x)] ]
      => let G' := context G[opt.id (opt.map opt.fst x)] in
         change G'
    | [ |- context G[map snd (opt.id ?x)] ]
      => let G' := context G[opt.id (opt.map opt.snd x)] in
         change G'
    (*| [ |- context G[snd (of_string (opt.id ?x))] ]
               => let G' := context G[opt.snd (of_string x)] in
                  change G'*)
    | [ |- context G[string_beq (opt.id ?x)] ]
      => let G' := context G[opt.id (opt.string_beq x)] in
         change G'
    | [ |- context G[fun x0 y0 : ?T => string_beq (fst x0) (fst y0)] ]
      => let G' := context G[opt.id (fun x0 y0 : T => opt.string_beq (opt.fst x0) (opt.fst y0))] in
         change G'
    | [ |- context G[uniquize (opt.id ?beq) (opt.id ?ls)] ]
      => let G' := context G[opt.id (opt.uniquize beq ls)] in
         change G'
    | [ |- context G[uniquize string_beq (opt.id ?ls)] ]
      => let G' := context G[opt.id (opt.uniquize opt.string_beq ls)] in
         change G'
    | [ |- context G[List.length (opt.id ?ls)] ]
      => let G' := context G[opt.id (opt.length ls)] in
         change G'
    | [ |- context G[List.length (opt2.id ?ls)] ]
      => let G' := context G[opt2.id (opt2.length ls)] in
         change G'
    | [ |- context G[first_index_default (opt.id ?x) (opt.id ?y) (opt.id ?z)] ]
      => let G' := context G[opt.id (opt.first_index_default x y z)] in
         change G'
    | [ |- context G[up_to (opt.id ?n)] ]
      => let G' := context G[opt.id (opt.up_to n)] in
         change G'
    | [ |- context G[pred (opt.id ?n)] ]
      => let G' := context G[opt.id (opt.pred n)] in
         change G'
    | [ |- context G[rev (opt.id ?ls)] ]
      => let G' := context G[opt.id (opt.rev ls)] in
         change G'
    | [ |- context G[fun x0 : ?T => up_to (Datatypes.length (snd x0))] ]
      => let G' := context G[opt.id (fun x0 : T => opt.up_to (opt.length (opt.snd x0)))] in
         change G'
    | [ |- context G[combine (opt.id ?ls) (opt.id ?ls')] ]
      => let G' := context G[opt.id (opt.combine ls ls')] in
         change G'
    | [ |- context G[List.hd ?d (opt.id ?ls)] ]
      => let G' := context G[opt.id (opt.hd d ls)] in
         change G'
    | [ |- context G[fst (of_string ?str')] ]
      => let G' := context G[opt.id (opt.fst (of_string str'))] in
         change G'
    | [ |- context G[snd (of_string ?str')] ]
      => let G' := context G[opt.id (opt.snd (of_string str'))] in
         change G'
    | [ |- context G[EqNat.beq_nat (opt2.id ?x) 0] ]
      => let G' := context G[opt2.id (opt2.beq_nat x 0)] in
         change G'
    | [ |- context G[(opt2.id ?x, 0)] ]
      => let G' := context G[opt2.id (x, 0)] in
         change G'
    | [ |- context G[(opt2.id ?x, opt2.id ?y)] ]
      => let G' := context G[opt2.id (x, y)] in
         change G'
    | [ |- context G[EqNat.beq_nat (opt.id ?x) 0] ]
      => let G' := context G[opt.id (opt.beq_nat x 0)] in
         change G'
    | [ |- context G[S (opt2.id ?x)] ]
      => let G' := context G[opt2.id (S x)] in
         change G'
    | [ |- context G[S (opt.id ?x)] ]
      => let G' := context G[opt.id (S x)] in
         change G'
    | [ |- context G[Compare_dec.leb (opt2.id ?x) (opt.id ?y)] ]
      => let G' := context G[opt2.id (opt2.leb x y)] in
         change G'
    | [ |- context G[Compare_dec.leb 1 (opt2.id ?x)] ]
      => let G' := context G[opt2.id (opt2.leb 1 x)] in
         change G'
    | [ |- context G[Compare_dec.leb 1 (opt2.length ?x)] ]
      => let G' := context G[opt2.id (opt2.leb 1 (opt2.length x))] in
         change G'
    | [ |- context G[@interp_RCharExpr ?Char ?idata (opt.id ?expr)] ]
      => let G' := context G[opt.id (@opt.interp_RCharExpr Char idata expr)] in
         change G'
    end.

  Local Ltac change_opt_reduce' :=
    idtac;
    match goal with
    | _ => progress safe_change_opt'
    | [ |- ?LHS = _ ]
      => match LHS with
         | context[opt.id] => unfold opt.id at 1
         | context[opt2.id] => unfold opt2.id at 1
         | context[opt3.id] => unfold opt3.id at 1
         end
    | [ |- ?e = opt.id ?x ]
      => progress change (e = x)
    | [ |- ?e = opt2.id ?x ]
      => progress change (e = x)
    | [ |- _ = opt2.map _ _ ]
      => apply ((_ : Proper (pointwise_relation _ _ ==> eq ==> eq) (@List.map _ _))
                : Proper (pointwise_relation _ _ ==> eq ==> eq) (@opt2.map _ _));
        [ let x := fresh in intro x; change x with (opt2.id x)
        | ]
    | [ |- _ = opt.map _ _ ]
      => apply ((_ : Proper (pointwise_relation _ _ ==> eq ==> eq) (@List.map _ _))
                : Proper (pointwise_relation _ _ ==> eq ==> eq) (@opt.map _ _));
        [ let x := fresh in intro x; change x with (opt.id x)
        | ]
    | [ |- _ = @opt.fold_left ?A ?B orb _ false ]
      => refine (_ : opt.fold_left orb _ false = _);
        apply ((_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B))
               : Proper _ (@opt.fold_left A B));
        repeat (let x := fresh in intro x; change x with (opt.id x))
    | [ |- _ = @opt.fold_left ?A ?B orbr _ false ]
      => refine (_ : opt.fold_left orbr _ false = _);
        apply ((_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B))
               : Proper _ (@opt.fold_left A B));
        repeat (let x := fresh in intro x; change x with (opt.id x))
    | [ |- _ = @opt.list_caset ?A (fun _ => ?P) _ _ _ ]
      => refine (_ : @opt.list_caset A (fun _ => P) _ _ _ = _);
        apply ((_ : Proper (_ ==> pointwise_relation _ (pointwise_relation _ _) ==> _ ==> _) (@list_caset A (fun _ => P)))
               : Proper _ (@opt.list_caset A (fun _ => P)));
        repeat (let x := fresh in intro x; change x with (opt.id x))
    | _ => progress cbv beta
    | [ |- _ = opt2.nth _ _ _ ]
      => apply (f_equal2 (opt2.nth _))
    | [ |- _ = opt2.bool_rect ?P _ _ _ ]
      => apply (f_equal3 (opt2.bool_rect P))
    | _ => progress fin_step_opt
    | [ |- _ = orb _ _ ] => apply (f_equal2 orb)
    | [ |- _ = orbr _ _ ] => apply (f_equal2 orbr)
    | [ |- _ = andb _ _ ] => apply (f_equal2 andb)
    | [ |- _ = andbr _ _ ] => apply (f_equal2 andbr)
    | [ |- _ = minusr _ _ ] => apply (f_equal2 minusr)
    | [ |- ?e = List.map ?f (opt2.id ?x) ]
      => progress change (e = opt2.map f x)
    | [ |- context G[List.map ?f (opt.id ?ls)] ]
      => let G' := context G[opt.id (opt.map f ls)] in
         change G'
    | [ |- context G[bool_rect ?x ?y ?z (opt.id ?w)] ]
      => let G' := context G[opt.id (opt.bool_rect x y z w)] in
         change G'
    | [ |- context G[bool_rect ?x ?y ?z (opt2.id ?w)] ]
      => let G' := context G[opt2.id (opt2.bool_rect x y z w)] in
         change G'
    | [ |- context G[list_caset ?x ?y ?z (opt.id ?w)] ]
      => let G' := context G[opt.id (opt.list_caset x y z w)] in
         change G'
    | [ |- context G[item_rect ?x ?y ?z (opt.id ?w)] ]
      => let G' := context G[opt.id (opt.item_rect x y z w)] in
         change G'
    | [ |- context G[ritem_rect ?x ?y ?z (opt.id ?w)] ]
      => let G' := context G[opt.id (opt.ritem_rect x y z w)] in
         change G'
    | [ |- context G[List.fold_left orb (opt.id ?ls) false] ]
      => let G' := context G[opt.id (opt.fold_left orb ls false)] in
         change G'
    | [ |- context G[List.fold_left orbr (opt.id ?ls) false] ]
      => let G' := context G[opt.id (opt.fold_left orbr ls false)] in
         change G'
    | [ |- _ = list_rect ?P ?N ?C (opt.id ?ls) (opt2.id ?idx) ?offset ?len ]
      => t_reduce_list_evar;
        [
               | match goal with
                 | [ |- ?e ?x ?xs ?H ?a ?b ?c = _ ]
                   => is_evar e;
                     change x with (opt.id x);
                     change xs with (opt.id xs);
                     change a with (opt2.id a)
                 end ]
    | [ |- _ = opt.item_rect ?T ?A ?B ?c ] (* evar kludge following *)
      => revert c;
        let RHS := match goal with |- forall c', _ = ?RHS c' => RHS end in
        let f := constr:(fun TC NC =>
                           forall c, opt.item_rect T TC NC c = RHS c) in
        let f := (eval cbv beta in f) in
        let e1 := fresh in
        let e2 := fresh in
        match type of f with
        | ?X -> ?Y -> _
          => evar (e1 : X); evar (e2 : Y)
        end;
          intro c;
          let ty := constr:(opt.item_rect T e1 e2 c = RHS c) in
          etransitivity_rev _; [ refine (_ : ty) | reflexivity ];
          revert c;
          refine (item_rect
                    (fun c => opt.item_rect T e1 e2 c = RHS c)
                    _ _);
          intro c; simpl @opt.item_rect; subst e1 e2;
          change c with (opt.id c)
    | [ |- _ = opt.ritem_rect ?T ?A ?B ?c ] (* evar kludge following *)
      => revert c;
        let RHS := match goal with |- forall c', _ = ?RHS c' => RHS end in
        let f := constr:(fun TC NC =>
                           forall c, opt.ritem_rect T TC NC c = RHS c) in
        let f := (eval cbv beta in f) in
        let e1 := fresh in
        let e2 := fresh in
        match type of f with
        | ?X -> ?Y -> _
          => evar (e1 : X); evar (e2 : Y)
        end;
          intro c;
          let ty := constr:(opt.ritem_rect T e1 e2 c = RHS c) in
          etransitivity_rev _; [ refine (_ : ty) | reflexivity ];
          revert c;
          refine (ritem_rect
                    (fun c => opt.ritem_rect T e1 e2 c = RHS c)
                    _ _);
          intro c; simpl @opt.ritem_rect; subst e1 e2;
          change c with (opt.id c)
    | [ |- _ = opt2.beq_nat _ _ ] => apply (f_equal2 opt2.beq_nat)
    | [ |- _ = opt2.leb _ _ ] => apply (f_equal2 opt2.leb)
    | [ |- _ = opt2.length _ ] => apply f_equal
    | [ |- _ = opt.snd _ ] => apply f_equal
    | [ |- _ = opt2.snd _ ] => apply f_equal
    | [ |- _ = opt.fst _ ] => apply f_equal
    | [ |- _ = opt2.fst _ ] => apply f_equal
    | [ |- _ = opt.interp_RCharExpr _ ] => apply f_equal
    | [ |- _ = opt.uniquize _ _ ] => reflexivity
    | [ |- _ = opt.combine _ _ ] => reflexivity
    | [ |- _ = opt.length ?x ] => is_var x; reflexivity
    | [ |- _ = char_at_matches _ _ _ ] => apply f_equal3
    | [ |- _ = char_at_matches_interp _ _ _ ] => apply f_equal3
    end.

  Local Ltac safe_change_opt := repeat safe_change_opt'.
  Local Ltac change_opt_reduce := repeat change_opt_reduce'.

  Local Ltac do_flip_map ls :=
    idtac;
    progress
      (repeat let A := match goal with |- context[@List.map ?A ?B] => A end in
              let B := match goal with |- context[@List.map A ?B] => B end in
              let flip_map := fresh "flip_map" in
              pose (flip_map ls' f := @List.map A B f ls');
                progress change (@List.map A B) with (fun f ls' => @flip_map ls' f);
                cbv beta;
                try change (@flip_map ls) with (@flip_map (opt.id ls)));
    repeat match goal with
           | [ flip_map := fun ls' f => @List.map _ _ f ls' |- _ ]
             => subst flip_map
           end;
    cbv beta.

  Local Ltac do_flip_combine ls :=
    idtac;
    progress
      (repeat let A := match goal with |- context[@List.combine ?A ?B] => A end in
              let B := match goal with |- context[@List.combine A ?B] => B end in
              let flip_combine := fresh "flip_combine" in
              pose (flip_combine ls' f := @List.combine A B f ls');
                progress change (@List.combine A B) with (fun f ls' => @flip_combine ls' f);
                cbv beta;
                try change (@flip_combine ls) with (@flip_combine (opt.id ls)));
    repeat match goal with
           | [ flip_combine := fun ls' f => @List.combine _ _ f ls' |- _ ]
             => subst flip_combine
           end;
    cbv beta.

  Definition parse_nonterminal_opt'3
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'2 str nt) in
    let h := head c in
    let p := (eval cbv beta iota zeta delta [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].
    evar (b' : bool).
    sigL_transitivity b'; subst b'.
    Focus 2.
    { progress unfold rdp_list_of_nonterminal, default_of_nonterminal; simpl.
      unfold pregrammar_nonterminals; simpl.
      match goal with
        | [ |- _ = ?f ?x ]
          => set (F := f)
      end.
      rewrite map_length.
      subst F.
      (** TODO: Come up with a robust (possibly reflective) version of
      this, based or wheich things are recursively accessible *)
      change @nth' with @opt3.nth' at 1.
      change @List.map with @opt2.map at 1.
      change (pregrammar_productions G) with (opt.id (pregrammar_productions G)).
      change nt with (opt.id nt).
      change str with (opt.id str).
      safe_change_opt.
      change (opt.id (pregrammar_productions G)) with (pregrammar_productions G).
      change (opt.id nt) with nt.
      change (opt.id str) with str.
      reflexivity. }
    Unfocus.
    refine_Fix2_5_Proper_eq.
    etransitivity_rev _.
    { fix2_trans;
      [
      | solve [ change @opt3.nth' with @nth';
                change @opt2.map with @List.map;
                t_reduce_fix;
                t_postreduce_list;
                unfold ritem_rect;
                t_reduce_fix ] ].

      do_flip_map (pregrammar_rproductions G).
      do_flip_combine (pregrammar_rproductions G).
      change (List.length (pregrammar_rproductions G)) with (opt.id (opt.length (pregrammar_rproductions G))).

      step_opt'; [ | reflexivity ].
      apply (f_equal2 (opt3.nth' _)); [ | reflexivity ].
      change_opt_reduce.
      step_opt';
        change_opt_reduce; [ | | | ].
      { match goal with
        | [ |- _ = ?f (opt2.id ?x) ?y ?z ]
          => refine (f_equal (fun x' => f x' y z) _)
        end.
        change_opt_reduce; [].
        match goal with
        | [ |- _ = if opt2.id _ then opt2.id _ else opt2.id _ ]
          => unfold opt2.id; reflexivity
        end. }
      { match goal with
        | [ |- _ = ?f _ _ (opt.id (opt.first_index_default _ _ _)) ]
          => unfold opt.id
        end.
        reflexivity. }
      { match goal with
        | [ |- _ = ?f (opt2.id ?x) ?y ?z ]
          => refine (f_equal (fun x' => f x' y z) _)
        end.
        change_opt_reduce; [].
        match goal with
        | [ |- _ = if opt2.id _ then opt2.id _ else opt2.id _ ]
          => unfold opt2.id; reflexivity
        end. }
      { change @List.map with @opt2.map at 1. (** FIXME: is this right? *)
        change_opt_reduce; [ | | progress unfold opt2.id; reflexivity ].
        { match goal with
          | [ |- _ = ?f _ _ (opt.id (opt.first_index_default _ _ _)) ]
            => unfold opt.id
          end.
          reflexivity. }
        { match goal with
          | [ |- _ = ?f (opt2.id ?x) ?y ?z ]
            => refine (f_equal (fun x' => f x' y z) _)
          end.
          change_opt_reduce; [].
          match goal with
          | [ |- _ = if opt2.id _ then opt2.id _ else opt2.id _ ]
            => unfold opt2.id; reflexivity
          end. } } }
    change @fold_left with @opt3.fold_left at 1.
    change @list_rect with @opt.list_rect at 1.
    reflexivity.
  Defined.

  Definition parse_nonterminal_preopt
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'2 str nt) in
    let h := head c in
    let impl := (eval cbv beta iota zeta delta [h proj1_sig] in (proj1_sig c)) in
    (exists impl);
      abstract (exact (proj2_sig c)).
  Defined.

  Lemma parse_nonterminal_preopt_eq
        {HSLP : StringLikeProperties Char}
        {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}
        (str : String)
        (nt : String.string)
    : proj1_sig (parse_nonterminal_preopt str nt) = parse_nonterminal (data := data) str nt.
  Proof.
    rewrite <- parse_nonterminal_optdata_eq.
    apply proj2_sig.
  Qed.

  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'3 str nt) in
    let h := head c in
    let impl := (eval cbv beta iota zeta delta [h proj1_sig item_rect ritem_rect list_caset] in (proj1_sig c)) in
    (exists impl);
      abstract (exact (proj2_sig c)).
  Defined.

  Lemma parse_nonterminal_opt_eq
        {HSLP : StringLikeProperties Char}
        {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}
        (str : String)
        (nt : String.string)
    : proj1_sig (parse_nonterminal_opt str nt) = parse_nonterminal (data := data) str nt.
  Proof.
    rewrite <- parse_nonterminal_optdata_eq.
    apply proj2_sig.
  Qed.
End recursive_descent_parser.
