(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ExpressionParen.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Common.
Require Import Fiat.Common.Wf.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Refinement.FixedLengthLemmas.

Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec paren_expr_grammar).
  Proof.
    lazymatch goal with
     | [ |- FullySharpened _ ]
       => (eapply FullySharpened_Start)
    end.
    eapply SharpenStep;
  [ solve [ apply FirstStep ] | ].
    Timeout 5 unfold rindexed_spec, rindexed_spec'.
    unfold forall_reachable_productions.
    Timeout 5 simpl expanded_fallback_list'.
    unfold expanded_fallback_list_rules'.
    Timeout 5 simpl map.
    Timeout 5 unfold fold_right at 1.
    Timeout 5 simpl map.
    Timeout 5 unfold Operations.enumerate.
    Timeout 5 unfold all_disjoint.
    Timeout 5 simpl map.
    Timeout 5 unfold Operations.disjoint.
    Timeout 5 simpl map.
    Timeout 5 unfold fold_right at 1.
    Timeout 5 unfold fold_right at 1.
    Timeout 5 unfold fold_right at 1.
    Timeout 5 unfold fold_right at 1.
    Timeout 5 simpl andb.
    Timeout 5 simpl @snd.
    Timeout 5 unfold If_Then_Else at 4.
    Timeout 5 simpl @fst.
    Timeout 5 change (@If_Then_Else ?A false) with (fun (x y : A) => y).
    Timeout 5 change (@If_Then_Else ?A true) with (fun (x y : A) => x).
    Timeout 5 cbv beta.
    Timeout 5 unfold fold_right at 1.
    Timeout 5 simpl @fst.
    Timeout 5 simpl @snd.
    About Equality.list_bin.
    Timeout 5 change (@Equality.list_bin) with (fun A f a ls => let lb := fun a' => @Equality.list_bin A f a' ls in lb a).
    Timeout 5 cbv beta.
    Timeout 5 repeat match goal with
      | [ |- appcontext[fun a' => @Equality.list_bin ?A ?f a' [?ls]] ]
        => let c := constr:(fun a' => @Equality.list_bin A f a' [ls]) in
           let c' := (eval simpl in c) in
           change c with c'
    end.
    Opaque ParserInterface.rules_list_is_complete.
    Timeout 5 match goal with
                | [ |- context[(fun dummy => If @?x dummy Then @?y dummy Else _)] ]
                  => let c := constr:(fun dummy => If_Then_Else (x dummy) (y dummy)) in
                     let c' := (eval simpl in c) in
                     idtac
              end.
    Timeout 20 simpl.

    Timeout 5 simpl (Equality.list_bin Equality.ascii_beq).
    Timeout 5 simpl.
    Timeout 5 unfold If_Then_Else at 11.
    Timeout 5 simpl (If true Then _ Else _).

    Timeout 5 simpl.



     | _ => start_honing
      end

    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      finish honing parser method.
    }

    hone method "rules".
    {
      simplify parser splitter.
      finish honing parser method.
    }

    FullySharpenEachMethodWithoutDelegation.
    extract delegate-free implementation.
    simpl; higher_order_reflexivityT.
  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec paren_expr_grammar).
  Proof.
    let impl := (eval simpl in (projT1 ComputationalSplitter')) in
    refine (existT _ impl _).
    abstract (exact (projT2 ComputationalSplitter')).
  Defined.

End IndexedImpl.

Global Arguments ComputationalSplitter / .

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Time Definition paren_expr_parser (str : String.string) : bool
  := Eval simpl in has_parse (parser ComputationalSplitter) str.

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
