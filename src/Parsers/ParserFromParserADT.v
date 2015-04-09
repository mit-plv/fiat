(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import ADTSynthesis.Parsers.SplitterFromParserADT.
Require Import ADTSynthesis.Parsers.ParserImplementation.
Require Import ADTSynthesis.ADT.ComputationalADT.
Require Import ADTSynthesis.ADTRefinement.GeneralRefinements.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarTransfer.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTSynthesis.ADTRefinement.Core.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section parser.
  Context (G : grammar Ascii.ascii).
  Context (splitter_impl : FullySharpened (string_spec G)).

  Definition base_parser : Parser G (adt_based_splitter splitter_impl)
    := parser (adt_based_splitter splitter_impl).

  Definition new_string_of_base_string (str : String.string)
    := (cConstructors (projT1 splitter_impl) {| StringBound.bindex := "new" |} (str : String.string)).

  Lemma new_string_of_base_string_R {str}
  : AbsR (projT2 splitter_impl) str (new_string_of_base_string str).
  Proof.
    unfold new_string_of_base_string.
    pose proof (ADTRefinementPreservesConstructors (projT2 splitter_impl) {| StringBound.bindex := "new" |} str (cConstructors (projT1 splitter_impl) {| StringBound.bindex := "new" |} str) (ReturnComputes _)) as H'';
      computes_to_inv;
      simpl in H'';
      computes_to_inv; subst; assumption.
  Qed.

  Definition new_string_of_string str : @String Ascii.ascii (adt_based_splitter splitter_impl)
    := (exist
          _
          (new_string_of_base_string str)
          (ex_intro
             _
             str
             new_string_of_base_string_R)).

  Definition soundness_type := forall str : @String _ string_stringlike,
                                 has_parse base_parser (new_string_of_string str) = true ->
                                 parse_of_item G str (NonTerminal G).

  Lemma string_parser_sound
  : soundness_type.
  Proof.
    Set Printing All.
    Timeout 2 abstract (exfalso; admit).
    admit.


  Definition string_parser : Parser G string_stringlike.
  Proof.
    refine {| has_parse str
              := has_parse
                   base_parser
                   (exist
                      _  (new_string_of_base_string str)
                      (ex_intro _ str new_string_of_base_string_R));
              has_parse_sound := _;
              has_parse_complete := _ |}.
    { refine (fun str Hparse
              => @transfer_parse_of_item
                   Ascii.ascii (adt_based_StringLike splitter_impl) string_stringlike G
                   (fun x y => AbsR (projT2 splitter_impl) y (` x))
                   _ _ _ _ _ _ _ _ (has_parse_sound base_parser _ Hparse)).
      admit.
      { intros ????.
        simpl.
        erewrite mis_char_eq; intros; eassumption. }
      { intros ???.
        admit; erewrite mlength_eq; intros; eassumption. }
    { intros; apply mtake_R; assumption. }
    { intros; refine (mdrop_R _ _); assumption. }
    { apply new_string_of_base_string_R. }
  Qed.
  Next Obligation.
    refine (@transfer_parse_of_item Ascii.ascii (adt_based_StringLike splitter_impl) string_stringlike G
                                    ((fun x y => AbsR (projT2 splitter_impl) y (` x)) : _ -> String.string -> Prop)
                                    _ _ _ _ _ _ _ _ (has_parse_sound base_parser _ Hparse));
    simpl.
    { intros ????.
      erewrite mis_char_eq; intros; eassumption. }
    { intros ???.
      erewrite mlength_eq; intros; eassumption. }
    { intros; apply mtake_R; assumption. }
    { intros; refine (mdrop_R _ _); assumption. }
    { apply new_string_of_base_string_R. }
  Qed.


              (fun x (y : String.string) => AbsR (projT2 splitter_impl) x y)).
    Focus 5.
    pose .


    dependent destruction p.
    pose proof (@parse_nonterminal_complete Char splitter _ G _ _ rdp_list_rdata' str (Start_symbol G) p) as H'.
    apply H'.
    rewrite <- (parse_of_item_respectful_refl (pf := reflexivity _)).
    rewrite <- (parse_of_item_respectful_refl (pf := reflexivity _)) in Hp.
    eapply expand_forall_parse_of_item; [ | reflexivity.. | eassumption ].
    simpl.
    unfold rdp_list_is_valid_nonterminal; simpl.
    intros ? ? ? ? ? H0.
    edestruct List.in_dec as [ | nH ]; trivial; [].
    destruct (nH H0).
  Qed.





End parser.
