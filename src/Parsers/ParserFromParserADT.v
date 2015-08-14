(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import Fiat.Parsers.SplitterFromParserADT.
Require Import Fiat.Parsers.ContextFreeGrammarNotations.
Require Export Fiat.Parsers.ParserImplementationOptimized.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.ContextFreeGrammarTransfer.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.BooleanRecognizerEquality.
Require Import Fiat.ADTRefinement.Core.
Require Import Fiat.Common.BoundedLookup.
Require Import Fiat.ADTNotation.BuildADTSig.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section parser.
  Context {ls : list (String.string * productions Ascii.ascii)}.
  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).
  Context (splitter_impl : FullySharpened (string_spec G)).

  Definition newS := ibound (indexb (@Build_BoundedIndex _ _ (ConstructorNames (string_rep Ascii.ascii)) "new" _ )).

  Definition new_string_of_base_string (str : String.string)
    := (cConstructors (projT1 splitter_impl) newS (str : String.string)).

  Lemma new_string_of_base_string_R {str}
  : AbsR (projT2 splitter_impl) str (new_string_of_base_string str).
  Proof.
    unfold new_string_of_base_string.
    pose proof (ADTRefinementPreservesConstructors (projT2 splitter_impl) newS str (cConstructors (projT1 splitter_impl) newS str) (ReturnComputes _)) as H'';
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

  Local Instance adtProj
  : @StringLikeProj
      _
      (adt_based_splitter splitter_impl)
      (adt_based_StringLike_lite splitter_impl)
      (ParserImplementation.parser_data (adt_based_splitter splitter_impl))
      (fun it its str => msplits splitter_impl (it, its) str)
    := { proj := @proj1_sig _ _ }.
  Proof.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
  Defined.

  Context {constT varT}
          {strC : @BooleanRecognizerOptimized.str_carrier
                    Ascii.ascii
                    (adt_based_StringLike_lite splitter_impl)
                    constT varT}.

  Definition parser : Parser G string_stringlike.
  Proof.
    refine (@parser ls (adt_based_splitter splitter_impl)
                    (adt_based_StringLike_lite splitter_impl)
                    _
                    adtProj new_string_of_string
                    (fun rep str => AbsR (projT2 splitter_impl) str (` rep))
                    (@new_string_of_base_string_R) _ _
                    _ _ strC);
    abstract (
        split;
        first [ (intros ????);
                simpl;
                erewrite mis_char_eq; intros; eassumption
              | (intros ???);
                simpl;
                erewrite mlength_eq; intros; eassumption
              | intros; apply mtake_R; assumption
              | intros; refine (mdrop_R _ _); assumption ]
      ).
  Defined.
End parser.

Global Arguments parser {ls} splitter_impl {constT varT strC}.
