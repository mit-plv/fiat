
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerOptimized.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.Semantics Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.SemanticsOptimized Fiat.Parsers.Reflective.ParserSemanticsOptimized.
Require Import Fiat.Parsers.Reflective.Morphisms.
Require Import Fiat.Parsers.Reflective.ParserReify.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.

Section recursive_descent_parser.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii}
          {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Ascii.ascii _ _}.

  Definition parse_nonterminal_prereified0 (str : String) (nt : String.string) : polyhas_parse_term cbool.
  Proof.
    let p := constr:(parse_nonterminal_preopt Hvalid str nt) in
    let h := head p in
    let p := (eval cbv [proj1_sig h] in (proj1_sig p)) in
    do_reify_has_parse p ltac:(fun r => exact r).
  Defined.
End recursive_descent_parser.

Definition parse_nonterminal_reified (G : pregrammar Ascii.ascii) (nt : String.string) : polyhas_parse_term cbool.
Proof.
  let p := constr:(fun HSLM => @parse_nonterminal_prereified0 HSLM G) in
  let p := (eval cbv [parse_nonterminal_prereified0] in p) in
  let p := match p with fun A B C => ?f => f end in
  let p := (eval cbv [rdp_list_of_nonterminal grammar_of_pregrammar pregrammar'_of_pregrammar pregrammar_nonterminals pregrammar_productions] in (p nt)) in
  exact p.
Defined.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}
          {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Ascii.ascii _ _}.

  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.

  Context {splitdata_correct : @CorrectnessBaseTypes.boolean_parser_completeness_dataT' _ _ _ G data}.

  Context (str : String) (nt : String.string).

  Definition rinterp_parse pnt
    := (opt.interp_has_parse_term
          (T := cbool)
          (@is_valid_nonterminal _ _)
          (length str)
          (fun n => @Reflective.char_at_matches_interp _ _ (pregrammar_idata G) n str)
          (fun n => split_string_for_production n str)
          pnt).

  Local Ltac step_interp_Term_fold :=
    unfold interp_Term, interp_Term_gen; fold @interp_Term_gen;
    unfold interp_Term_gen_step;
    change (@interp_Term_gen (@interp_RLiteralTerm)) with (@interp_Term);
    fold @interp_TypeCode.

  Local Ltac fin_proper' :=
    idtac;
    instantiate;
    match goal with
    | [ |- ?x = ?x ] => reflexivity
    | _ => progress cbv beta iota
    | [ |- Proper_relation_for _ _ _ ] => unfold Proper_relation_for at 1
    | _ => intro
    | _ => progress subst
    | _ => progress unfold Proper in *
    | [ H : ?R ?f ?g |- ?f ?x = ?g ?x ]
      => apply H
    | _ => progress unfold map_args_for
    | _ => progress unfold args_for_related
    | [ |- ?LHS = ahd ?e ]
      => is_evar e; refine (_ : LHS = ahd (an_arg _ _)); fin_proper'
    | [ |- ?LHS = atl ?e ]
      => is_evar e; refine (_ : LHS = atl (an_arg _ _)); fin_proper'
    | [ |- ?LHS = ?f (atl ?e) ]
      => is_evar e; refine (_ : LHS = f (atl (an_arg _ _))); fin_proper'
    | [ |- ?LHS = ?a (?b (atl ?e)) ]
      => is_evar e; refine (_ : LHS = a (b (atl (an_arg _ _)))); fin_proper'
    | [ |- ?LHS = ?a (?b (?c (atl ?e))) ]
      => is_evar e; refine (_ : LHS = a (b (c (atl (an_arg _ _))))); fin_proper'
    | [ |- ?LHS = ?a (?b (?c (?d (atl ?e)))) ]
      => is_evar e; refine (_ : LHS = a (b (c (d (atl (an_arg _ _)))))); fin_proper'
    | [ |- noargs = _ ] => reflexivity
    | [ |- appcontext G[ahd (an_arg ?x ?y)] ]
      => let G' := context G[x] in
         change G'
    | [ |- appcontext G[atl (an_arg ?x ?y)] ]
      => let G' := context G[y] in
         change G'
    | [ |- _ /\ _ ] => split
    end.
  Local Ltac fin_proper := repeat fin_proper'.

  Local Ltac head_app x :=
    match x with
    | RApp ?x' _ => head_app x'
    | _ => x
    end.
  Local Ltac handle_var :=
    repeat lazymatch goal with
           | [ |- ?LHS = _ ]
             => lazymatch LHS with
                | appcontext[interp_Term ?x]
                  => match head_app x with
                     | RVar _ => step_interp_Term_fold
                     end
                end
           end;
    lazymatch goal with
    | [ |- ?LHS = ?RHS ]
      => let x := head LHS in
         let y := head RHS in
         match goal with
         | [ H : ?R x y |- _ ]
           => first [ apply H
                    | etransitivity; [ apply H | instantiate; f_equal ] ]
         end
    end.

  Local Ltac reified_eq' :=
    idtac;
    match goal with
    | _ => reflexivity
    | [ |- appcontext G[@list_rect ?A (fun _ => ?T)] ]
      => let G' := context G[@Operations.List.list_rect_nodep A T] in change G'
    | [ |- appcontext G[@Operations.List.list_caset ?A (fun _ => ?T)] ]
      => let G' := context G[@Operations.List.list_caset_nodep A T] in change G'
    | [ |- context G[if ?b then ?t else ?f] ]
      => let G' := context G[@bool_rect_nodep _ t f b] in change G'
    | [ |- interp_Term (RLambda _) _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ _ _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ _ _ _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ _ _ _ _ _ = _ ] => step_interp_Term_fold
    | [ |- interp_Term (RLambda _) _ _ _ _ _ _ _ _ _ = _ ] => step_interp_Term_fold
    | [ |- ?LHS = _ ]
      => let test := head LHS in
         constr_eq test (@interp_Term);
         lazymatch LHS with
         | appcontext[interp_Term ?x]
           => match head_app x with
              | RVar _ => idtac
              end
         end;
         handle_var; fin_proper
    | [ |- @apply_args_for ?T (interp_RLiteralTerm ?f) ?args = _ ]
      => etransitivity;
         [ apply (@apply_args_for_Proper T);
           [ first [ reflexivity
                   | lazymatch goal with
                     | [ |- appcontext[interp_RLiteralTerm ?f] ]
                       => apply (@RLiteralTerm_Proper _ f)
                     end ]
           | fin_proper.. ]
         | instantiate; simpl @apply_args_for; reflexivity ]
    | [ |- interp_Term (RLiteralApp ?f ?args) = _ ]
      => step_interp_Term_fold
    | [ |- context[Syntactify.syntactify_rproductions _ _] ]
      => rewrite <- interp_Term_syntactify_rproductions
    | _ => instantiate; progress fin_proper
    end.

  Local Ltac reified_eq := reified_eq'; try reified_eq.

  Lemma parse_nonterminal_reified_opt_interp_precorrect
    : rinterp_parse (parse_nonterminal_reified G nt _)
      = proj1_sig (parse_nonterminal_preopt Hvalid str nt).
  Proof.
    clear splitdata_correct HSLP.
    cbv [rinterp_parse parse_nonterminal_reified].
    change @opt.interp_has_parse_term with @interp_has_parse_term.
    cbv [interp_has_parse_term].
    cbv [proj1_sig parse_nonterminal_preopt].
    match goal with
    | [ |- ?f ?x = ?g ?y ]
      => replace x with y
    end.
    Focus 2.
    { unfold rdp_list_of_nonterminal.
      cbv [pregrammar_productions pregrammar'_of_pregrammar].
      rewrite !List.map_length, !List.map_map; simpl.
      reflexivity. }
    Unfocus.
    refine (Wf2.Fix2_5_Proper_eq _ _ _ _ _ _ _ _ _ _).
    repeat intro.
    unfold step_option_rec.
    lazymatch goal with
    | [ |- option_rect (fun _ : option (interp_TypeCode ?T) => _) _ _ ?x = option_rect _ _ _ ?y ]
        => idtac;
             let x0 := fresh "x" in
           let y0 := fresh "y" in
           destruct x as [x0|] eqn:?, y as [y0|] eqn:?;
             [ let p := fresh "P" in
               cut ((Proper_relation_for T)%signature x0 y0); [ intro p | ]
             | exfalso
             | exfalso
             | reflexivity ]
    end;
      [
      |
      | edestruct Compare_dec.lt_dec;
        simpl @is_valid_nonterminal in *; unfold rdp_list_is_valid_nonterminal in *;
        [ | edestruct dec ];
        simpl in *;
        congruence.. ].
    { unfold option_rect.
      reified_eq. }
    { unfold forall_relation, pointwise_relation in *.
      edestruct Compare_dec.lt_dec;
      simpl @is_valid_nonterminal in *; unfold rdp_list_is_valid_nonterminal in *;
      [ | edestruct dec ];
      simpl in *; try congruence;
      repeat match goal with
             | _ => progress subst
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
             end.
      { repeat intro; subst; eauto with nocore. }
      { repeat intro; subst; eauto with nocore. } }
  Qed.

  Lemma parse_nonterminal_reified_opt_interp_correct
    : rinterp_parse (parse_nonterminal_reified G nt _)
      = BooleanRecognizer.parse_nonterminal (data := data) str nt.
  Proof.
    rewrite parse_nonterminal_reified_opt_interp_precorrect.
    apply parse_nonterminal_preopt_eq; assumption.
  Qed.
End correctness.
