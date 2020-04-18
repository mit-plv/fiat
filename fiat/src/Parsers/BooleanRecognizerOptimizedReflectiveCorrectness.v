
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerOptimizedReflective.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.
Require Import Fiat.Parsers.Reflective.ParserSoundnessOptimized.
Require Import Fiat.Parsers.Reflective.ParserPartialUnfold.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.StringLike.Core.

Lemma Term_equiv_syntactify_list {var1 var2 G} {T : SimpleTypeCode} (ls1 : list (Term var1 T)) (ls2 : list (Term var2 T))
      (Hlen : List.length ls1 = List.length ls2)
      (H : forall x y, List.In (x, y) (List.combine ls1 ls2) -> Term_equiv G x y)
: Term_equiv G (Syntactify.syntactify_list ls1) (Syntactify.syntactify_list ls2).
Proof.
  revert dependent ls2; induction ls1 as [|x xs IHxs]; simpl;
    (destruct ls2; simpl; try congruence; []);
    intros Hlen H;
    match goal with
    | [ |- Term_equiv ?G (RLiteralApp ?f ?v1) (RLiteralApp ?f ?v2) ]
      => apply (@EqLiteralApp _ _ G _ f v1 v2)
    end;
    repeat constructor;
    eauto.
Qed.

Lemma Term_equiv_syntactify_list_map {var1 var2 G A}
      {T : SimpleTypeCode}
      (f : A -> Term var1 T) (g : A -> Term var2 T)
      (ls : list A)
      (H : forall x, List.In x ls -> Term_equiv G (f x) (g x))
: Term_equiv
    G
    (Syntactify.syntactify_list (List.map f ls))
    (Syntactify.syntactify_list (List.map g ls)).
Proof.
  apply Term_equiv_syntactify_list.
  { rewrite !List.map_length; reflexivity. }
  { rewrite ListFacts.combine_map_l, ListFacts.combine_map_r, List.map_map; simpl.
    intros ?? H'.
    apply List.in_map_iff in H'.
    pose proof (@ListFacts.map_combine_id A _ (fun x => x) ls) as H''.
    rewrite List.map_id in H''.
    rewrite H'' in H'; clear H''.
    destruct H' as [[? ?] [H'0 H'1]].
    apply List.in_map_iff in H'1.
    destruct H'1 as [? [H'1 H'2]].
    inversion H'1; clear H'1; subst; simpl in *.
    inversion H'0; clear H'0; subst; simpl in *.
    eauto. }
Qed.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}
          {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Ascii.ascii _ _}.

  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.

  Let optdata : boolean_parser_dataT :=
    {| split_data := RecognizerPreOptimized.optsplitdata |}.

  Context {splitdata_correct : @CorrectnessBaseTypes.boolean_parser_completeness_dataT' _ _ _ G data}.

  Context (str : String) (nt : String.string).

  Local Ltac build_term_equiv_step :=
    idtac;
    match goal with
    | _ => progress intros
    | [ |- Term_equiv _ _ _ ]
      => econstructor
    | [ |- args_for_related_ind _ _ _ ]
      => econstructor
    | [ |- Term_equiv ?G (RLiteralApp ?f ?v1) (RLiteralApp ?f ?v2) ]
      => apply (@EqLiteralApp _ _ G _ f v1 v2)
    | [ |- List.In ?v (?v :: _) ]
      => left; reflexivity
    | [ |- List.In ?v (?x :: ?xs) ]
      => match xs with
         | context[v]
           => right
         end
    | [ |- Term_equiv
             _
             (Syntactify.syntactify_list (List.map ?f ?ls))
             (Syntactify.syntactify_list (List.map ?g ?ls)) ]
      => apply Term_equiv_syntactify_list_map; simpl @fst; simpl @snd
    end.

  Lemma parse_nonterminal_reified_unfold_extensional
    : ParserSyntaxEquivalence.has_parse_term_equiv
        nil
        (parse_nonterminal_reified G nt Semantics.interp_TypeCode)
        (parse_nonterminal_reified G nt
                                   (PartialUnfold.normalized_of Semantics.interp_TypeCode)).
  Proof.
    unfold parse_nonterminal_reified, Syntactify.syntactify_rproductions,
    Syntactify.syntactify_prod, Syntactify.syntactify_string, Syntactify.syntactify_ritem_ascii;
      constructor.
    (*Start Profiling.*)
    repeat build_term_equiv_step.
    (*Show Profile.*)
    (* total time:     25.328s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─econstructor --------------------------  60.4%  60.4%    1224    0.260s
─apply (EqLiteralApp (G:=G) f (v1:=v1) (  27.4%  27.4%     297    0.312s
─right ---------------------------------   8.3%   8.3%     438    0.020s
─left ----------------------------------   2.0%   2.0%     117    0.012s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─econstructor --------------------------  60.4%  60.4%    1224    0.260s
─apply (EqLiteralApp (G:=G) f (v1:=v1) (  27.4%  27.4%     297    0.312s
─right ---------------------------------   8.3%   8.3%     438    0.020s
─left ----------------------------------   2.0%   2.0%     117    0.012s
 *)
    repeat build_term_equiv_step.
  Qed.

  Lemma parse_nonterminal_reified_opt_interp_polynormalize_precorrect
    : rinterp_parse str (polypnormalize (parse_nonterminal_reified G nt) _)
      = BooleanRecognizer.parse_nonterminal (data := optdata) str nt.
  Proof.
    cbv [rinterp_parse].
    rewrite <- opt.polypnormalize_correct by apply parse_nonterminal_reified_unfold_extensional.
    etransitivity;
      [ etransitivity; [ | apply parse_nonterminal_reified_opt_interp_precorrect ]
      | let p := match goal with |- context[proj1_sig ?p] => p end in
        apply (proj2_sig p) ].
    cbv [rinterp_parse].
    reflexivity.
    Grab Existential Variables.
    assumption.
  Qed.
End correctness.
